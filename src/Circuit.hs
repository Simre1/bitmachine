{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Circuit where

import BitCircuit
import Bits
import Control.Category
import Data.Type.Ord
import Effects
import GHC.TypeLits
import Prelude hiding (id, (.))

data Circuit f a b where
  Circuit :: BitCircuit f (Size a) (Size b) -> Circuit f a b

getBitCircuit :: Circuit f a b -> BitCircuit f (Size a) (Size b)
getBitCircuit (Circuit bc) = bc

cMap :: (BitRep a, BitRep b) => Circuit NoEffect a b -> a -> b
cMap (Circuit bc) a =
  let bitsA = toBits a
      bitsB = mapBits bc bitsA
   in fromBits bitsB

instance Category (Circuit f) where
  id = Circuit CId
  (Circuit f) . (Circuit g) = Circuit $ CSequence g f

arr :: (BitRep a, BitRep b) => (a -> b) -> Circuit f a b
arr f = Circuit (bitFunction f)

(***) :: forall f a b c d. (KnownNat (Size a)) => Circuit f a b -> Circuit f c d -> Circuit f (a, c) (b, d)
(Circuit bc1) *** (Circuit bc2) =
  Circuit $
    CPar
      ( CSequence
          (CTake (natSing @(Size a)))
          bc1
      )
      (CSequence (CDrop (natSing @(Size a))) bc2)

(&&&) :: forall f a b c. (KnownNat (Size a)) => Circuit f a b -> Circuit f a c -> Circuit f a (b, c)
(Circuit bc1) &&& (Circuit bc2) = Circuit $ CPar bc1 bc2

first :: (KnownNat (Size a)) => Circuit f a b -> Circuit f (a, c) (b, c)
first circuit = circuit *** id

second :: (KnownNat (Size c)) => Circuit f a b -> Circuit f (c, a) (c, b)
second circuit = id *** circuit

cId :: Circuit f a a
cId = Circuit CId

cEqual :: Circuit f (Bits 2) (Bits 1)
cEqual = Circuit $ CSequence (CPar CAnd (CSequence (bcTogether CNot CNot) CAnd)) COr

cXor :: Circuit f (Bits 2) (Bits 1)
cXor = Circuit $ CSequence (CPar COr (CSequence CAnd CNot)) CAnd

cAnd :: Circuit f (Bits 2) (Bits 1)
cAnd = Circuit CAnd

cOr :: Circuit f (Bits 2) (Bits 1)
cOr = Circuit COr

cNot :: Circuit f (Bits 1) (Bits 1)
cNot = Circuit CNot

cPar :: Circuit f a b -> Circuit f a c -> Circuit f a (b, c)
cPar (Circuit bc1) (Circuit bc2) = Circuit (CPar bc1 bc2)

cTogether :: (KnownNat (Size a)) => Circuit f a b -> Circuit f c d -> Circuit f (a, c) (b, d)
cTogether (Circuit bc1) (Circuit bc2) = Circuit $ bcTogether bc1 bc2

cHigh :: Circuit f () (Bits 1)
cHigh = Circuit CHigh

cLow :: Circuit f () (Bits 1)
cLow = Circuit (CSequence CHigh CNot)

cDrop :: (KnownNat a) => Circuit f (Bits (a + b)) (Bits b)
cDrop = Circuit (CDrop natSing)

cTake :: (KnownNat a) => Circuit f (Bits (a + b)) (Bits a)
cTake = Circuit (CTake natSing)

cAt :: forall i f n. ((i < n), KnownNat i) => Circuit f (Bits n) (Bits 1)
cAt = Circuit (CAt (natSing @i))

cEff :: f (Size a) (Size b) -> Circuit f a b
cEff = Circuit . CEff

cCoerce :: (BitRep a, BitRep b, Size a ~ Size b) => Circuit f a b
cCoerce = Circuit CId

cHalfAdder :: Circuit f (Bits 2) (Bits 2)
cHalfAdder = cPar cAnd cXor >>> cCoerce

cFullAdder :: Circuit f (Bits 3) (Bits 2)
cFullAdder =
  arr coerceBits
    >>> arr
      ( \(a :: Bits 1, b :: Bits 1, cin :: Bits 1) ->
          let (c :: Bits 1, s :: Bits 1) = coerceBits $ cMap cHalfAdder (mergeBits a b)
              (c' :: Bits 1, s' :: Bits 1) = coerceBits $ cMap cHalfAdder (mergeBits s cin)
           in coerceBits $ (c' .|. c, s')
      )

cFullAdder2 :: Circuit f (Bits 3) (Bits 2)
cFullAdder2 =
  cPar
    (cTake @2 >>> cHalfAdder)
    (cDrop @2 >>> cId)
    >>> cCoerce
    >>> cPar
      (cTake @1 >>> cId)
      (cDrop @1 >>> cHalfAdder)
    >>> cCoerce
    >>> cPar
      (cTake @2 >>> cOr)
      (cDrop @2 >>> cId)
    >>> cCoerce

cZipFold :: (KnownNat x, KnownNat n) => Circuit f (Bits (x + 2)) (Bits (x + 1)) -> Circuit f (Bits (x + n + n)) (Bits n)
cZipFold (Circuit bc) = Circuit $ bcZipFold bc

rippleAdder :: forall f n. (KnownNat n) => Circuit f (Bits (n + n)) (Bits n)
rippleAdder = cPar (arr (const ()) >>> cLow) cId >>> cCoerce >>> cZipFold cFullAdder
