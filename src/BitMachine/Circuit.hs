{-# LANGUAGE AllowAmbiguousTypes #-}

module BitMachine.Circuit where

import BitMachine.BitCircuit
import BitMachine.BitCircuit.Combinators
import BitMachine.Bits
import BitMachine.Effects
import Control.Category
import Data.Type.Ord
import GHC.TypeLits
import Prelude hiding (id, (.))

data Circuit f a b where
  Circuit :: BitCircuit f (Size a) (Size b) -> Circuit f a b

toBitCircuit :: Circuit f a b -> BitCircuit f (Size a) (Size b)
toBitCircuit (Circuit bc) = bc

fromBitCircuit :: forall a b f. BitCircuit f (Size a) (Size b) -> Circuit f a b
fromBitCircuit bc = Circuit bc

cMap :: (BitRep a, BitRep b) => Circuit NoEffect a b -> a -> b
cMap (Circuit bc) a =
  let bitsA = toBits a
      bitsB = mapBits bc bitsA
   in fromBits bitsB

instance Category (Circuit f) where
  id = Circuit bcId
  (Circuit f) . (Circuit g) = Circuit $ g #>> f

arr :: (BitRep a, BitRep b) => (a -> b) -> Circuit f a b
arr f = Circuit (bitFunction f)

(***) :: forall f a b c d. (KnownNat (Size a)) => Circuit f a b -> Circuit f c d -> Circuit f (a, c) (b, d)
(Circuit bc1) *** (Circuit bc2) =
  Circuit $
    bcPar
      ( (bcTake @(Size a))
          #>> bc1
      )
      (bcDrop @(Size a) #>> bc2)

(&&&) :: forall f a b c. (KnownNat (Size a)) => Circuit f a b -> Circuit f a c -> Circuit f a (b, c)
(Circuit bc1) &&& (Circuit bc2) = Circuit $ bcPar bc1 bc2

first :: forall a b c f. (KnownNat (Size a)) => Circuit f a b -> Circuit f (a, c) (b, c)
first circuit = circuit *** id

second :: forall a b c f. (KnownNat (Size c)) => Circuit f a b -> Circuit f (c, a) (c, b)
second circuit = id *** circuit

cId :: forall a f. Circuit f a a
cId = Circuit bcId

cEqual :: Circuit f (Bits 2) (Bits 1)
cEqual = Circuit $ (bcPar bcAnd (bcTogether bcNot bcNot #>> bcAnd)) #>> bcOr

cXor :: Circuit f (Bits 2) (Bits 1)
cXor = Circuit $ bcPar bcOr (bcAnd #>> bcNot) #>> bcAnd

cAnd :: Circuit f (Bits 2) (Bits 1)
cAnd = Circuit bcAnd

cOr :: Circuit f (Bits 2) (Bits 1)
cOr = Circuit bcOr

cNot :: Circuit f (Bits 1) (Bits 1)
cNot = Circuit bcNot

cPar :: forall a b c f. Circuit f a b -> Circuit f a c -> Circuit f a (b, c)
cPar (Circuit bc1) (Circuit bc2) = Circuit (bcPar bc1 bc2)

cTogether :: forall a b c d f. (KnownNat (Size a)) => Circuit f a b -> Circuit f c d -> Circuit f (a, c) (b, d)
cTogether (Circuit bc1) (Circuit bc2) = Circuit $ bcTogether bc1 bc2

cHigh :: Circuit f () (Bits 1)
cHigh = Circuit bcHigh

cLow :: Circuit f () (Bits 1)
cLow = Circuit (bcHigh #>> bcNot)

cDrop :: forall a b f. (KnownNat a) => Circuit f (Bits (a + b)) (Bits b)
cDrop = Circuit bcDrop

cTake :: forall a b f. (KnownNat a) => Circuit f (Bits (a + b)) (Bits a)
cTake = Circuit bcTake

cAt :: forall i f n. ((i < n), KnownNat i) => Circuit f (Bits n) (Bits 1)
cAt = Circuit $ bcAt @i

cFeedback :: KnownNat (Size b) => Circuit f (a, b) b -> Circuit f a b
cFeedback (Circuit bc) = Circuit $ bcFeedback bc

cEff :: forall a b f. KnownNat (Size b) => f (Size a) (Size b) -> Circuit f a b
cEff = Circuit . bcEff

cCoerce :: forall a b f. (BitRep a, BitRep b, Size a ~ Size b) => Circuit f a b
cCoerce = Circuit bcId

cNor :: Circuit f (Bits 2) (Bits 1)
cNor = Circuit bcNor

cNand :: Circuit f (Bits 2) (Bits 1)
cNand = Circuit bcNand
