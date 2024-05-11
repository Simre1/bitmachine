module BitMachine.Effects where

import BitMachine.BitCircuit
import BitMachine.Proofs (lesserWithConstant)
import Data.Constraint (withDict)
import GHC.TypeNats

data ReaderF (n :: Nat) (a :: Nat) (b :: Nat) where
  ReaderF :: ReaderF n 0 n

runReaderFBit :: forall n a b. (KnownNat n) => BitCircuit (ReaderF n) a b -> BitCircuit NoEffect (n + a) b
runReaderFBit (BCEff _ ReaderF) = bcId
runReaderFBit BCNot = (bcDrop @n) #>> bcNot
runReaderFBit BCAnd = bcDrop @n #>> bcAnd
runReaderFBit BCOr = bcDrop @n #>> bcOr
runReaderFBit BCHigh = bcDrop @n #>> bcHigh
runReaderFBit BCId = bcDrop @n #>> bcId
runReaderFBit (BCSequence bc1 bc2) =
  bcPar
    (bcTake @n)
    (runReaderFBit bc1)
    #>> runReaderFBit bc2
runReaderFBit (BCPar bc1 bc2) = bcPar (runReaderFBit bc1) (runReaderFBit bc2)
runReaderFBit (BCDrop @i SNat) = bcDrop @(n + i)
runReaderFBit (BCTake @i SNat) = bcDrop @n #>> (bcTake @i)
runReaderFBit (BCAt @i SNat) = withDict (lesserWithConstant @n @i @a) $ BCAt (natSing @(n + i))
runReaderFBit (BCComponent cd bc) = bcComponent cd $ runReaderFBit bc 
