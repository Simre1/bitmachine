module Main where

import BitMachine
import BitMachine.Circuit.Combinators
import BitMachine.Circuit.Components (cRippleAdder)
import Data.Functor ((<&>))
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
    eval
      evalNoEffect
      [toNumber $ 0b01000010]
      (cRippleAdder @4)
      `shouldReturn` [toNumber 0b0110]

  it "ripple adder 2" $
    eval
      evalNoEffect
      [toNumber $ 0b11000001]
      (cRippleAdder @4)
      `shouldReturn` [toNumber 0b1101]

  it "multiplexer 1" $
    eval
      evalNoEffect
      [toNumber $ 0b0]
      (cMultiplex (SLCons cLow (SLCons cHigh SLEmpty)))
      `shouldReturn` [toNumber 0b0]

  it "multiplexer 2" $
    eval
      evalNoEffect
      [toNumber 0b10]
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
      `shouldReturn` [toNumber 0b1]
