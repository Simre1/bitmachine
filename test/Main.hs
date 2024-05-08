module Main where

import BitBlast
import Test.Hspec

main :: IO ()
main = hspec $ do
  describe "Circuit eval tests" $ do
    circuitTests
    

circuitTests :: SpecWith ()
circuitTests = do
  it "add" False

