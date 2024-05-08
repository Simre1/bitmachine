module Main where

import BitMachine
import BitMachine.Circuit.Combinators
import BitMachine.Circuit.Components (cRippleAdder)
import Data.Functor.Identity
import Data.List.Sized
import Data.Sequence qualified as S
import Test.Hspec

main :: IO ()
main = hspec $ do
  describe "Circuit eval tests" $ do
    circuitTests

circuitTests :: SpecWith ()
circuitTests = do
  it "ripple adder 1" $
    ( runIdentity $
        eval
          evalNoEffect
          ([False, True, False, False, False, False, True, False] !!)
          (cRippleAdder @4)
    )
      == [False, True, True, False]

  it "ripple adder 2" $
    ( runIdentity $
        eval
          evalNoEffect
          ([True, True, False, False, False, False, False, True] !!)
          (cRippleAdder @4)
    )
      == [True, True, False, True]

  it "multiplexer 1" $
    ( runIdentity $
        eval
          evalNoEffect
          ([False] !!)
          (cMultiplex (SLCons cLow (SLCons cHigh SLEmpty)))
    )
      == [False]

  it "multiplexer 2" $
    ( runIdentity $
        eval
          evalNoEffect
          ([True, False] !!)
          ( cMultiplex
              ( SLCons
                  cLow
                  ( SLCons
                      cLow
                      ( SLCons
                          cHigh
                          (SLCons cLow SLEmpty)
                      )
                  )
              )
          )
    )
      == [True]
