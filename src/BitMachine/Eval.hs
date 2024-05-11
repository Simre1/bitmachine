{-# LANGUAGE RecursiveDo #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module BitMachine.Eval where

import BitMachine.BitCircuit
import BitMachine.Bits (BitRep (..))
import BitMachine.Circuit (Circuit (..))
import Control.Monad (forM)
import Data.Bits
import Data.Coerce (coerce)
import Data.Foldable
import Data.Functor ((<&>))
import Data.Maybe (fromMaybe)
import Data.Sequence qualified as S
import Debug.Trace
import GHC.Stack (HasCallStack)
import GHC.TypeNats
import Reactimate

eval ::
  forall a b f.
  (BitRep a, BitRep b) =>
  (forall i o. f i o -> [SimBool] -> IO [SimBool]) ->
  [(Int -> Bool)] ->
  Circuit f a b ->
  IO [[Bool]]
eval runEffect initializers (Circuit bc) = do
  let inputSize = fromIntegral $ fromSNat (natSing @(Size a))
  outputs <- sample ((snd $ go bc inputSize)) inputs
  forM outputs $ \output ->
    maybe (fail "Does not converge") pure $ traverse fromSimBool output
  where
    inputs :: [[SimBool]]
    inputs = initializers <&> \makeInitial -> toSimBool . makeInitial <$> [0 .. (fromIntegral $ natVal $ natSing @(Size a)) - 1]

    go :: BitCircuit f n1 n2 -> Int -> (Int, Signal ([SimBool]) ([SimBool]))
    go BCAnd 2 = (1, arr $ \([b1, b2]) -> [b1 `andSimBool` b2])
    go BCOr 2 = (1, arr $ \([b1, b2]) -> [b1 `orSimBool` b2])
    go BCNot 1 = (1, arr $ \([b]) -> [notSimBool b])
    go (BCSequence c1 c2) a =
      let (b, signal1) = go c1 a
          (c, signal2) = go c2 b
       in (c, signal1 >>> signal2)
    go (BCPar c1 c2) a =
      let (b, signal1) = go c1 a
          (c, signal2) = go c2 a
       in (b + c, (<>) <$> signal1 <*> signal2)
    go BCHigh 0 = (1, pure [SBTrue])
    go BCId i = (i, arr id)
    go (BCDrop split) w =
      let x = (fromIntegral $ fromSNat split)
       in (w - x, arr $ \bs -> drop x bs)
    go (BCTake split) _ =
      let x = (fromIntegral $ fromSNat split)
       in (x, arr $ \bs -> take x bs)
    go (BCAt index) _ = (1, arr $ \bs -> [bs !! (fromIntegral $ fromSNat index)])
    go (BCFeedback _ bc') a =
      let (b, signal) = go bc' (a)
       in (b, feedbackSignal b signal)
    -- -- bs' <- go bc' (bs <> bs')
    -- pure bs'
    go (BCEff outputSize f) _ = (fromIntegral $ fromSNat outputSize, arrIO $ runEffect f)
    -- go (BCComponent _ bc') bs = go bc' bs
    go _ _ = error "Invalid bit circuit"

feedbackSignal :: Int -> Signal [SimBool] [SimBool] -> Signal [SimBool] [SimBool]
feedbackSignal outputSize signal =
  feedback (const SBUnknown <$> [1 .. outputSize]) $
    arrIO $ \(input, initialOutput) -> do
      let loop unstableOutput = do
            [output] <- sample (signal) [input ++ unstableOutput]
            if output == unstableOutput
              then pure output
              else loop output

      loop initialOutput

data Number (n :: Nat) = Number Integer Integer

-- data Number = Number Int Integer

eval2 ::
  forall a b .
  (BitRep a, BitRep b) =>
  (forall i o. NoEffect i o -> Number i -> IO (Number o)) ->
  [Number (Size a)] ->
  Circuit NoEffect a b ->
  IO [Number (Size b)]
eval2 runEffect inputs (Circuit bc) = do
  let inputSize = fromIntegral $ fromSNat (natSing @(Size a))
      outputSize = fromIntegral $ fromSNat (natSing @(Size b))
  outputs <- sample ((snd $ go bc inputSize)) inputs
  pure outputs
  where
    go :: BitCircuit NoEffect n1 n2 -> Int -> (Int, Signal (Number n1) (Number n2))
    go BCAnd 2 = (1, arr $ \(Number v u) -> Number (v .&. shiftR v 1) (u .|. shiftR u 1))
    go BCOr 2 = (1, arr $ \(Number v u) -> Number ((v .|. shiftR v 1) .&. 1) ((u .|. shiftR u 1) .&. 1))
    go BCNot 1 = (1, arr $ \(Number v u) -> Number (if testBit v 0 then 0 else 1) u)
    go (BCSequence c1 c2) a =
      let (b, signal1) = go c1 a
          (c, signal2) = go c2 b
       in (c, signal1 >>> signal2)
    go (BCPar c1 c2) a =
      let (b, signal1) = go c1 a
          (c, signal2) = go c2 a
       in (b + c, (\(Number v1 u1) (Number v2 u2) -> Number (shiftL v1 c .|. v2) (shiftL u1 c .|. u2)) <$> signal1 <*> signal2)
    go BCHigh 0 = (1, pure $ Number 1 0)
    go BCId i = (i, arr id)
    go (BCDrop d) w =
      let x = w - (fromIntegral $ fromSNat d)
       in (x, arr $ \(Number v1 u1) -> Number (v1 .&. setBits x) (u1 .&. setBits x))
    go (BCTake t) w =
      let x = (fromIntegral $ fromSNat t)
       in (x, arr $ \(Number v u) -> Number (shiftR v (w-x)) (shiftR u (w-x)))
    go (BCAt index) w =
      let x = w - (fromIntegral $ fromSNat index) - 1
       in (1, arr $ \(Number v u) -> Number (shiftR v x .&. 1) (shiftR u x .&. 1))
    -- go (BCFeedback outputSize bc') a =
    --   let (b, signal) = go bc' (a + x)
    --       x = fromIntegral $ fromSNat outputSize
    --    in (b, feedbackSignal2 b signal)
    -- bs' <- go bc' (bs <> bs')
    -- pure bs'
    -- go (BCEff outputSize f) _ = (fromIntegral $ fromSNat outputSize, arrIO $ runEffect f)
    -- go (BCComponent _ bc') bs = go bc' bs
    go bc x = error $ "Invalid bit circuit: " ++ show (bc, x)

setBits :: Int -> Integer
setBits 0 = 0
setBits n = setBit (setBits (n - 1)) (n-1)

feedbackSignal2 :: forall a b. Int -> Signal (Number (a + b)) (Number b) -> Signal (Number a) (Number b)
feedbackSignal2 outputSize signal =
  feedback (Number 0 $ foldl' setBit 0 [0 .. outputSize - 1]) $
    arrIO $ \(Number v1 u1, initialOutput) -> do
      let loop (Number v2 u2) = do
            [Number v3 u3] <- sample signal [Number (shiftL v1 outputSize .|. v2) (shiftL u1 outputSize .|. u2)]
            -- print (Number v1 u1, Number v2 u2, Number v3 u3)
            if u2 == u3
              then pure (Number v3 u3)
              else loop (Number v3 u3)
      x <- loop initialOutput
      pure x

evalNoEffect :: NoEffect a b -> x -> m y
evalNoEffect _ _ = error "No Effect"

data SimBool = SBTrue | SBFalse | SBUnknown deriving (Eq, Show)

toNumber :: forall n. (KnownNat n) => Integer -> Number n
toNumber i = Number (i .&. setBits (fromIntegral $ fromSNat $ natSing @n)) 0

instance (KnownNat n) => Show (Number n) where
  show (Number v u) = toChar <$> [size - 1, size - 2..0]
    where
      toChar p
        | testBit u p = 'U'
        | testBit v p = '1'
        | otherwise = '0'
      size = fromIntegral $ natVal (natSing @n)

fromSimBool :: SimBool -> Maybe Bool
fromSimBool SBTrue = Just True
fromSimBool SBFalse = Just False
fromSimBool SBUnknown = Nothing

toSimBool :: Bool -> SimBool
toSimBool True = SBTrue
toSimBool False = SBFalse

andSimBool :: SimBool -> SimBool -> SimBool
andSimBool SBTrue SBTrue = SBTrue
andSimBool SBFalse _ = SBFalse
andSimBool _ SBFalse = SBFalse
andSimBool _ _ = SBUnknown

orSimBool :: SimBool -> SimBool -> SimBool
orSimBool SBTrue _ = SBTrue
orSimBool _ SBTrue = SBTrue
orSimBool SBFalse SBFalse = SBFalse
orSimBool _ _ = SBUnknown

notSimBool :: SimBool -> SimBool
notSimBool SBTrue = SBFalse
notSimBool SBFalse = SBTrue
notSimBool SBUnknown = SBUnknown
