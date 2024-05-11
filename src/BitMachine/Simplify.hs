{-# LANGUAGE LambdaCase #-}

module BitMachine.Simplify where

import BitMachine.BitCircuit
import Data.Type.Equality
import GHC.TypeNats

singleSimplify :: BitCircuit f a b -> BitCircuit f a b
singleSimplify = \case
  BCSequence BCId bc -> bc
  BCSequence bc BCId -> bc
  BCPar (BCTake n@SNat) bc -> case sameNat n (natSing @0) of
    Just Refl -> bc
    Nothing -> BCPar (BCTake n) bc
  BCPar bc (BCTake n@SNat) -> case sameNat n (natSing @0) of
    Just Refl -> bc
    Nothing -> BCPar (BCTake n) (bc)
  BCSequence (BCDrop n@SNat) bc -> case sameNat n (natSing @0) of
    Just Refl -> bc
    Nothing -> BCSequence (BCDrop n) (bc)
  BCSequence bc (BCDrop n@SNat) -> case sameNat n (natSing @0) of
    Just Refl -> bc
    Nothing -> BCSequence (bc) (BCDrop n)
  BCSequence bc (BCTake n@SNat) -> case sameNat n (natSing @0) of
    Just Refl -> BCTake n
    Nothing -> BCSequence bc (BCTake n)
  x -> x

simplify :: BitCircuit f a b -> BitCircuit f a b
simplify = \case
  BCSequence bc1 bc2 -> singleSimplify $ BCSequence (simplify bc1) (simplify bc2)
  BCPar bc1 bc2 -> singleSimplify $ BCPar (simplify bc1) (simplify bc2)
  x -> singleSimplify x
