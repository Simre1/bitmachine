module BitMachine.Circuit.Components where

import BitMachine.Bits
import BitMachine.Circuit
import BitMachine.Circuit.Combinators
import Control.Category
import Data.List.Sized
import GHC.TypeLits
import BitMachine.BitCircuit

cHalfAdder :: Circuit f (Bits 2) (Bits 2)
cHalfAdder = cPar cAnd cXor >>> cCoerce

cFullAdder :: Circuit f (Bits 3) (Bits 2)
cFullAdder =
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

cRippleAdder :: forall n f. (KnownNat n) => Circuit f (Bits (n + n)) (Bits n)
cRippleAdder = arr ((),) >>> cTogether cLow cId >>> cCoerce >>> cZipFold cFullAdder

-- cMultiplex :: forall n a b f. (KnownNat n) => SList (2 ^ n) (Circuit f a b) -> Circuit f (Bits n, a) b
-- cMultiplex options = case cmpNat (natSing @n) (natSing @1) of
--   EQI -> case options of
--     (SLCons option1 (SLCons option2 SLEmpty)) ->
--       second (cPar option1 option2)
--         >>> fromBitCircuit
--           ( bcPar @(n + Size a)
--               undefined
--               undefined
--           )
