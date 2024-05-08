module Eval where

import BitCircuit
import Bits
import Circuit
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
    go CAnd (b1 S.:<| b2 S.:<| S.Empty) = pure $ S.singleton (b1 && b2)
    go COr (b1 S.:<| b2 S.:<| S.Empty) = pure $ S.singleton (b1 || b2)
    go CNot (b1 S.:<| S.Empty) = pure $ S.singleton (not b1)
    go (CSequence c1 c2) bs = go c1 bs >>= go c2
    go (CPar c1 c2) bs = (<>) <$> go c1 bs <*> go c2 bs
    go CHigh _ = pure $ S.singleton True
    go CId bs = pure bs
    go (CDrop split) bs = pure $ S.drop (fromIntegral $ fromSNat split) bs
    go (CTake split) bs = pure $ S.take (fromIntegral $ fromSNat split) bs
    go (CAt index) bs = pure $ S.singleton (bs `S.index` (fromIntegral $ fromSNat index))
    go (CEff f) bs = runEffect f bs
    go _ _ = error "Invalid bit circuit"

evalNoEffect :: NoEffect a b -> S.Seq Bool -> m (S.Seq Bool)
evalNoEffect _ _ = error "No Effect"
