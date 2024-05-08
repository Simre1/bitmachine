module Data.List.Sized where

import BitMachine.Proofs
import Data.Type.Ord
import GHC.TypeNats

data SList (n :: Nat) a where
  SLCons :: a -> SList n a -> SList (n + 1) a
  SLEmpty :: SList 0 a

instance Functor (SList n) where
  fmap _ SLEmpty = SLEmpty
  fmap f (SLCons a as) = SLCons (f a) (f <$> as)

takeSList :: forall a b x. (KnownNat a) => SList (a + b) x -> SList a x
takeSList list = case cmpNat (natSing @a) (natSing @0) of
  LTI -> error "takeSList: impossible pattern match"
  EQI -> SLEmpty
  GTI -> case list of
    (SLCons a (as :: SList (a + b - 1) x)) ->
      withProof (ordToGreater @0 @a) $
        withProof (greaterToGreaterEqual @0 @a) $
          SLCons a (takeSList @(a - 1) @b as)
    SLEmpty -> error "takeSList: impossible pattern match"

dropSList :: forall a b x. (KnownNat a) => SList (a + b) x -> SList b x
dropSList list = case cmpNat (natSing @a) (natSing @0) of
  LTI -> error "takeSList: impossible pattern match"
  EQI -> list
  GTI -> case list of
    (SLCons a (as :: SList (a + b - 1) x)) ->
      withProof (ordToGreater @0 @a) $
        withProof (greaterToGreaterEqual @0 @a) $
          (dropSList @(a - 1) @b as)
    SLEmpty -> error "takeSList: impossible pattern match"
