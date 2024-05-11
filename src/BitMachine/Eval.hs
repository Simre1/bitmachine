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

data Number (n :: Nat) = Number Integer Integer deriving (Eq, Ord)


eval ::
  forall a b .
  (BitRep a, BitRep b) =>
  (forall i o. NoEffect i o -> Number i -> IO (Number o)) ->
  [Number (Size a)] ->
  Circuit NoEffect a b ->
  IO [Number (Size b)]
eval runEffect inputs (Circuit bc) = do
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
