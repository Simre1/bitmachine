{-# LANGUAGE TypeAbstractions #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Effects where

import BitCircuit
import Data.Constraint (withDict)
import GHC.TypeNats
import Proofs (lesserWithConstant)

data ReaderF (n :: Nat) (a :: Nat) (b :: Nat) where
  ReaderF :: ReaderF n 0 n

runReaderFBit :: forall n a b. (KnownNat n) => BitCircuit (ReaderF n) a b -> BitCircuit NoEffect (n + a) b
runReaderFBit (CEff ReaderF) = CId
runReaderFBit CNot = CSequence (CDrop (natSing @n)) CNot
runReaderFBit CAnd = CSequence (CDrop (natSing @n)) CAnd
runReaderFBit COr = CSequence (CDrop (natSing @n)) COr
runReaderFBit CHigh = CSequence (CDrop (natSing @n)) CHigh
runReaderFBit CId = CSequence (CDrop (natSing @n)) CId
runReaderFBit (CSequence bc1 bc2) =
  CSequence
    ( CPar
        (CTake (natSing @n))
        (runReaderFBit bc1)
    )
    (runReaderFBit bc2)
runReaderFBit (CPar bc1 bc2) = CPar (runReaderFBit bc1) (runReaderFBit bc2)
runReaderFBit (CDrop @i SNat) = CDrop @(n + i) @_ @b (natSing @(n + i))
runReaderFBit (CTake i) = CSequence (CDrop (natSing @n)) (CTake i)
runReaderFBit (CAt @i SNat) = withDict (lesserWithConstant @n @i @a) $ CAt (natSing @(n + i))

