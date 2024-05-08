{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Bits where

import BitCircuit
import GHC.TypeLits
import Type.Reflection

data Bits (n :: Nat) where
  FromInput :: SNat i -> BitCircuit NoEffect i n -> Bits n
  FromZero :: BitCircuit NoEffect 0 n -> Bits n

data BitsInput i where
  FullInput :: SNat i -> BitsInput i
  NoInput :: BitsInput 0

class (KnownNat (Size a)) => BitRep a where
  type Size a :: Nat
  toBits :: a -> Bits (Size a)
  fromBits :: Bits (Size a) -> a

instance BitRep () where
  type Size () = 0
  toBits _ = FromZero CId
  fromBits _ = ()

instance (KnownNat n) => BitRep (Bits n) where
  type Size (Bits n) = n
  toBits x = x
  fromBits x = x

instance (BitRep a, BitRep b) => BitRep (a, b) where
  type Size (a, b) = Size a + Size b
  toBits (a, b) = mergeBits (toBits a) (toBits b)
  fromBits bits =
    ( fromBits $ mapBits (CTake (natSing @(Size a))) bits,
      fromBits $ mapBits (CDrop (natSing @(Size a))) bits
    )

instance (BitRep a, BitRep b, BitRep c) => BitRep (a, b, c) where
  type Size (a, b, c) = Size a + Size b + Size c
  toBits (a, b, c) = mergeBits (mergeBits (toBits a) (toBits b)) (toBits c)
  fromBits bits =
    ( fromBits $ mapBits (CTake (natSing @(Size a))) bits,
      fromBits $ mapBits (CSequence (CDrop (natSing @(Size a))) (CTake (natSing @(Size b)))) bits,
      fromBits $ mapBits (CDrop (natSing @(Size a + Size b))) bits
    )

bitFunction :: forall f a b. (BitRep a, BitRep b) => (a -> b) -> BitCircuit f (Size a) (Size b)
bitFunction f =
  let a = fromBits (FromInput aNat CId)
      b = f a
   in case toBits b of
        FromInput bNat outputBits -> case assertEqual aNat bNat of
          Refl -> hoistF outputBits
        FromZero outputBits -> CSequence (CDrop (natSing @(Size a))) (hoistF outputBits)
  where
    aNat = natSing

coerceBits :: forall a b. ((Size a) ~ (Size b), BitRep a, BitRep b) => a -> b
coerceBits = fromBits . toBits

splitBits :: (KnownNat a, KnownNat b) => Bits (a + b) -> (Bits a, Bits b)
splitBits = coerceBits

mergeBits :: Bits a -> Bits b -> Bits (a + b)
mergeBits (FromInput iA bcA) (FromInput iB bcB) =
  case assertEqual iA iB of
    Refl -> FromInput iA (CPar bcA bcB)
mergeBits (FromZero bcA) (FromInput @i iB@SNat bcB) =
  FromInput iB (CPar (CSequence (CDrop (natSing @i)) bcA) bcB)
mergeBits (FromInput @i iA@SNat bcA) (FromZero bcB) =
  FromInput iA (CPar bcA (CSequence (CDrop (natSing @i)) bcB))
mergeBits (FromZero bcA) (FromZero bcB) =
  FromZero $ CPar bcA bcB

bAnd :: Bits 2 -> Bits 1
bAnd = mapBits CAnd

bOr :: Bits 2 -> Bits 1
bOr = mapBits COr

bNot :: Bits 1 -> Bits 1
bNot = mapBits CNot

bHigh :: Bits 1
bHigh = FromZero CHigh

bLow :: Bits 1
bLow = FromZero (CSequence CHigh CNot)

(.&.) :: (KnownNat x) => Bits x -> Bits x -> Bits x
bits1 .&. bits2 = mapBits (bcZip CAnd) (mergeBits bits1 bits2)

(.|.) :: (KnownNat x) => Bits x -> Bits x -> Bits x
bits1 .|. bits2 = mapBits (bcZip COr) (mergeBits bits1 bits2)

bsNot :: (KnownNat x) => Bits x -> Bits x
bsNot = mapBits notCircuit

mapBits :: BitCircuit NoEffect a b -> Bits a -> Bits b
mapBits bc2 (FromInput i bc1) = FromInput i (CSequence bc1 bc2)
mapBits bc2 (FromZero bc1) = FromZero (CSequence bc1 bc2)
