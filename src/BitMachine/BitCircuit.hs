{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}

module BitMachine.BitCircuit where

import Data.Kind
import Data.Text (Text)
import Data.Type.Ord
import GHC.TypeLits
import Type.Reflection
import Unsafe.Coerce (unsafeCoerce)

data BitCircuit (f :: Nat -> Nat -> Type) (a :: Nat) (b :: Nat) where
  BCAnd :: BitCircuit f 2 1
  BCOr :: BitCircuit f 2 1
  BCNot :: BitCircuit f 1 1
  BCSequence :: BitCircuit f a b -> BitCircuit f b c -> BitCircuit f a c
  BCPar :: BitCircuit f a b -> BitCircuit f a c -> BitCircuit f a (b + c)
  BCHigh :: BitCircuit f 0 1
  BCId :: BitCircuit f a a
  BCDrop :: SNat a -> BitCircuit f (a + b) b
  BCTake :: SNat a -> BitCircuit f (a + b) a
  BCAt :: (i < n) => SNat i -> BitCircuit f n 1
  BCFeedback :: SNat b -> BitCircuit f (a + b) b -> BitCircuit f a b
  BCEff :: SNat b -> f a b -> BitCircuit f a b
  BCComponent :: ComponentDescription -> BitCircuit f a b -> BitCircuit f a b

data ComponentDescription = ComponentDescription
  { behavior :: ComponentType,
    name :: Text,
    description :: Text
  }
  deriving (Show, Eq, Ord)

newtype ComponentType = ComponentType SomeTypeRep deriving (Show, Eq, Ord)

deriving instance (forall x y. Show (f x y)) => Show (BitCircuit f a b)

data NoEffect a b deriving (Show)

hoistF :: forall a b f. BitCircuit NoEffect a b -> BitCircuit f a b
hoistF = unsafeCoerce

bcAnd :: BitCircuit f 2 1
bcAnd = BCAnd

bcOr :: BitCircuit f 2 1
bcOr = BCOr

bcNot :: BitCircuit f 1 1
bcNot = BCNot

bcSequence :: forall a b c f. BitCircuit f a b -> BitCircuit f b c -> BitCircuit f a c
bcSequence = BCSequence

(#>>) :: forall a b c f. BitCircuit f a b -> BitCircuit f b c -> BitCircuit f a c
(#>>) = bcSequence

(<<#) :: forall a b c f. BitCircuit f b c -> BitCircuit f a b -> BitCircuit f a c
(<<#) = flip bcSequence

bcPar :: forall a b c f. BitCircuit f a b -> BitCircuit f a c -> BitCircuit f a (b + c)
bcPar = BCPar

(&#&) :: forall a b c f. BitCircuit f a b -> BitCircuit f a c -> BitCircuit f a (b + c)
(&#&) = BCPar

(*#*) :: forall a b c d f. (KnownNat a) => BitCircuit f a b -> BitCircuit f c d -> BitCircuit f (a + c) (b + d)
(*#*) = bcTogether

bcTogether :: forall a b c d f. (KnownNat a) => BitCircuit f a b -> BitCircuit f c d -> BitCircuit f (a + c) (b + d)
bcTogether bc1 bc2 =
  bcPar
    (bcTake @a #>> bc1)
    (bcDrop @a #>> bc2)

bcHigh :: BitCircuit f 0 1
bcHigh = BCHigh

bcId :: BitCircuit f a a
bcId = BCId

bcDrop :: forall a b f. (KnownNat a) => BitCircuit f (a + b) b
bcDrop = BCDrop natSing

bcTake :: forall a b f. (KnownNat a) => BitCircuit f (a + b) a
bcTake = BCTake natSing

bcAt :: forall x n f. (x < n, KnownNat x) => BitCircuit f n 1
bcAt = BCAt (natSing @x)

bcFeedback :: KnownNat b => BitCircuit f (a + b) b -> BitCircuit f a b
bcFeedback = BCFeedback natSing

bcEff :: KnownNat b => f a b -> BitCircuit f a b
bcEff = BCEff natSing

bcComponent :: ComponentDescription -> BitCircuit f a b -> BitCircuit f a b
bcComponent = BCComponent

bcNor :: BitCircuit f 2 1
bcNor = bcOr #>> bcNot

bcNand :: BitCircuit f 2 1
bcNand = bcOr #>> bcNot

