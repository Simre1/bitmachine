module BitMachine.Circuit.Combinators where

import BitMachine.BitCircuit.Combinators
import BitMachine.Bits
import BitMachine.Circuit
import Data.List.Sized
import GHC.TypeNats

cZipFoldRight :: (KnownNat x, KnownNat n) => Circuit f (Bits (x + 2)) (Bits (x + 1)) -> Circuit f (Bits (x + n + n)) (Bits n)
cZipFoldRight (Circuit bc) = Circuit $ bcZipFoldRight bc

cZipFoldLeft :: (KnownNat x, KnownNat n) => Circuit f (Bits (x + 2)) (Bits (x + 1)) -> Circuit f (Bits (x + n + n)) (Bits n)
cZipFoldLeft (Circuit bc) = Circuit $ bcZipFoldLeft bc

cMultiplex :: (KnownNat n, KnownNat (Size b)) => SList (2 ^ n) (Circuit f a b) -> Circuit f (Bits n, a) b
cMultiplex options = fromBitCircuit $ bcMultiplex (toBitCircuit <$> options)
