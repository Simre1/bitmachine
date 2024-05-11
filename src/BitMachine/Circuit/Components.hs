module BitMachine.Circuit.Components where

import BitMachine.BitCircuit
import BitMachine.Bits
import BitMachine.Circuit
import BitMachine.Circuit.Combinators
import Control.Category
import Data.List.Sized
import GHC.TypeLits

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
cRippleAdder = arr (,()) >>> cTogether cId cLow >>> cCoerce >>> cZipFoldLeft (cFullAdder >>> cPar (cDrop @1) (cTake @1) >>> cCoerce)

newtype Clock = Clock (Bits 1)

latch :: Circuit f (Bits 2) (Bits 2)
latch =
  fromBitCircuit $
    bcFeedback $
      bcPar
        ( bcPar
            (bcAt @0)
            (bcAt @3)
            #>> bcNor
        )
        ( bcPar
            (bcAt @1)
            (bcAt @2)
            #>> bcNor
        )

-- bcFullAdder :: BitCircuit f 3 2
-- bcFullAdder = toBitCircuit $ cFullAdder >>> cPar (cDrop @1) (cTake @1)

-- rippleAdder2 :: BitCircuit f 5 2
-- rippleAdder2 = -- 10010
--   ( bcPar @5 @2 @2 
--       ( bcPar
--           (bcPar (bcAt @1) (bcAt @(3))) -- 01
--           (bcDrop @(4)) -- 0
--           #>> bcFullAdder -- 10
--           #>> bcPar -- 01
--             (bcDrop @1)
--             (bcTake @1)
--       ) -- 01
--       ( bcPar @_ @(1) @(1)
--           (bcTake @(1) @(4)) -- 1
--           (bcDrop @2 @(3) #>> bcTake @(1) @(2)) -- 0
--       ) -- 10
--   ) -- 01 10
--     #>> bcPar @((2 - 1) + (2 - 1) + 1 + 1) @(2 - 1) @1
--       ( bcTake @((2 - 1) + (2 - 1) + 1)
--           #>> ( ( bcPar @(1 + 1 + 1) @(1 + 1) @((1 - 1) + (1 - 1))
--                     ( bcPar
--                         (bcPar (bcAt @(1 - 1)) (bcAt @(1 - 1 + 1)))
--                         (bcDrop @(1 + 1))
--                         #>> bcFullAdder
--                         #>> bcPar
--                           (bcDrop @1)
--                           (bcTake @1)
--                     )
--                     ( bcPar @_ @(1 - 1) @(1 - 1)
--                         (bcTake @(1 - 1) @(1 + 1 + 1))
--                         (bcDrop @1 @(1 + 1) #>> bcTake @(1 - 1) @(1 + 1))
--                     )
--                 )
--                   #>> bcPar @((1 - 1) + (1 - 1) + 1 + 1) @(1 - 1) @1
--                     (bcTake @((1 - 1) + (1 - 1) + 1) #>> bcTake @0)
--                     (bcDrop @((1 - 1) + (1 - 1) + 1))
--               )
--       )
--       (bcDrop @((2 - 1) + (2 - 1) + 1))
