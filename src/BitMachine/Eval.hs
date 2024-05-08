module BitMachine.Eval where

import BitMachine.BitCircuit
import BitMachine.Bits
import BitMachine.Circuit
import Data.Sequence qualified as S
import GHC.TypeNats

eval ::
  forall a b f m.
  (BitRep a, BitRep b, Monad m) =>
  (forall i o. f i o -> S.Seq Bool -> m (S.Seq Bool)) ->
  (Int -> Bool) ->
  Circuit f a b ->
  m [Bool]
eval runEffect makeInitial (Circuit bc) =
  foldr (:) [] <$> go bc initial
  where
    initial :: (S.Seq Bool)
    initial = S.fromFunction (fromIntegral $ natVal $ natSing @(Size a)) (makeInitial)

    go :: BitCircuit f n1 n2 -> S.Seq Bool -> m (S.Seq Bool)
    go BCAnd (b1 S.:<| b2 S.:<| S.Empty) = pure $ S.singleton (b1 && b2)
    go BCOr (b1 S.:<| b2 S.:<| S.Empty) = pure $ S.singleton (b1 || b2)
    go BCNot (b1 S.:<| S.Empty) = pure $ S.singleton (not b1)
    go (BCSequence c1 c2) bs = go c1 bs >>= go c2
    go (BCPar c1 c2) bs = (<>) <$> go c1 bs <*> go c2 bs
    go BCHigh _ = pure $ S.singleton True
    go BCId bs = pure bs
    go (BCDrop split) bs = pure $ S.drop (fromIntegral $ fromSNat split) bs
    go (BCTake split) bs = pure $ S.take (fromIntegral $ fromSNat split) bs
    go (BCAt index) bs = pure $ S.singleton (bs `S.index` (fromIntegral $ fromSNat index))
    go (BCEff f) bs = runEffect f bs
    go (BCComponent _ bc') bs = go bc' bs
    go _ _ = error "Invalid bit circuit"

evalNoEffect :: NoEffect a b -> S.Seq Bool -> m (S.Seq Bool)
evalNoEffect _ _ = error "No Effect"
