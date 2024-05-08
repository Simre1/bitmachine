{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module BitMachine.Bits where

import BitMachine.BitCircuit
import BitMachine.BitCircuit.Combinators
import BitMachine.Proofs
import Data.List.Sized
import Data.Maybe (fromMaybe)
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
  toBits _ = FromZero bcId
  fromBits _ = ()

instance (KnownNat n) => BitRep (Bits n) where
  type Size (Bits n) = n
  toBits x = x
  fromBits bits = bits

instance (BitRep a, BitRep b) => BitRep (a, b) where
  type Size (a, b) = Size a + Size b
  toBits (a, b) = mergeBits (toBits a) (toBits b)
  fromBits bits =
    ( fromBits $ mapBits (bcTake @(Size a)) bits,
      fromBits $ mapBits (bcDrop @(Size a)) bits
    )

instance (BitRep a, BitRep b, BitRep c) => BitRep (a, b, c) where
  type Size (a, b, c) = Size a + Size b + Size c
  toBits (a, b, c) = mergeBits (mergeBits (toBits a) (toBits b)) (toBits c)
  fromBits bits =
    ( fromBits $ mapBits (bcTake @(Size a)) bits,
      fromBits $ mapBits ((bcDrop @(Size a)) #>> (bcTake @(Size b))) bits,
      fromBits $ mapBits (bcDrop @(Size a + Size b)) bits
    )

instance (BitRep a, KnownNat n) => BitRep (SList n a) where
  type Size (SList n a) = n * Size a
  toBits (SLCons a as) = mergeBits (toBits a) (toBits as)
  toBits SLEmpty = emptyBits
  fromBits bits = case cmpNat (natSing @n) (natSing @0) of
    LTI -> error "fromBits: impossible pattern match"
    EQI -> SLEmpty
    GTI ->
      withProof (ordToGreater @0 @n) $
        withProof (greaterToGreaterEqual @0 @n) $
          SLCons
            (fromBits $ bTake @(Size a) bits)
            (fromBits @(SList (n - 1) a) $ bDrop @(Size a) bits)

bitFunction :: forall f a b. (BitRep a, BitRep b) => (a -> b) -> BitCircuit f (Size a) (Size b)
bitFunction f =
  let a = fromBits (FromInput aNat bcId)

      b = f a
   in case toBits b of
        FromInput bNat outputBits -> case assertEqual aNat bNat of
          Refl -> hoistF outputBits
        FromZero outputBits -> (bcDrop @(Size a)) #>> (hoistF outputBits)
  where
    aNat = natSing

coerceBits :: forall a b. ((Size a) ~ (Size b), BitRep a, BitRep b) => a -> b
coerceBits = fromBits . toBits

splitBits :: (KnownNat a, KnownNat b) => Bits (a + b) -> (Bits a, Bits b)
splitBits = coerceBits

mergeBits :: Bits a -> Bits b -> Bits (a + b)
mergeBits (FromInput iA bcA) (FromInput iB bcB) =
  case assertEqual iA iB of
    Refl -> FromInput iA (bcPar bcA bcB)
mergeBits (FromZero bcA) (FromInput @i iB@SNat bcB) =
  FromInput iB (bcPar (bcDrop @i #>> bcA) bcB)
mergeBits (FromInput @i iA@SNat bcA) (FromZero bcB) =
  FromInput iA (bcPar bcA ((bcDrop @i) #>> bcB))
mergeBits (FromZero bcA) (FromZero bcB) =
  FromZero $ bcPar bcA bcB

emptyBits :: Bits 0
emptyBits = FromZero bcId

zeroBits :: Bits 0
zeroBits = FromZero bcId

bAnd :: Bits 2 -> Bits 1
bAnd = mapBits bcAnd

bOr :: Bits 2 -> Bits 1
bOr = mapBits bcOr

bNot :: Bits 1 -> Bits 1
bNot = mapBits bcNot

bHigh :: Bits 1
bHigh = FromZero bcHigh

bLow :: Bits 1
bLow = FromZero (bcHigh #>> bcNot)

bTake :: forall a b. (KnownNat a) => Bits (a + b) -> Bits a
bTake = mapBits $ bcTake @a

bDrop :: forall a b. (KnownNat a) => Bits (a + b) -> Bits b
bDrop = mapBits $ bcDrop @a

(.&.) :: (KnownNat x) => Bits x -> Bits x -> Bits x
bits1 .&. bits2 = mapBits (bcZip bcAnd) (mergeBits bits1 bits2)

(.|.) :: (KnownNat x) => Bits x -> Bits x -> Bits x
bits1 .|. bits2 = mapBits (bcZip bcOr) (mergeBits bits1 bits2)

bsNot :: (KnownNat n) => Bits n -> Bits n
bsNot = mapBits $ bcMap bcNot

mapBits :: BitCircuit NoEffect a b -> Bits a -> Bits b
mapBits bc2 (FromInput i bc1) = FromInput i (bc1 #>> bc2)
mapBits bc2 (FromZero bc1) = FromZero (bc1 #>> bc2)

assertEqual :: SNat a -> SNat b -> a :~: b
assertEqual t1@SNat t2@SNat =
  fromMaybe (error "Not equal type reps") $ sameNat t1 t2

pattern (:#) :: (KnownNat n, 1 <= n) => Bits 1 -> Bits n -> Bits (n + 1)
pattern a :# as <- (coerceBits -> (a, as))
  where
    a :# as = mergeBits a as

{-# COMPLETE (:#) #-}

infixr 5 :#
