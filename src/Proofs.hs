{-# LANGUAGE AllowAmbiguousTypes #-}

module Proofs where

import Data.Constraint
import Data.Type.Ord
import GHC.TypeNats
import Unsafe.Coerce

ordToGreater :: forall a b. (Compare b a ~ 'GT) :- (a < b)
ordToGreater = fakeProof

ordToLesser :: forall a b. (Compare a b ~ 'LT) :- (a < b)
ordToLesser = fakeProof

ordToEq :: forall a b. (Compare a b ~ 'EQ) :- (a ~ b)
ordToEq = fakeProof

transitiveLesser :: forall a x b. ((a + x) < b) :- (a < b)
transitiveLesser = fakeProof

greaterToGreaterEqual :: forall n. (1 < n) :- (1 <= n)
greaterToGreaterEqual = fakeProof

lesserToZero :: (n < 1) :- (n ~ 0)
lesserToZero = fakeProof

greaterStaysGreater :: forall k n x. (k < n) :- (k < (n + x))
greaterStaysGreater = fakeProof

plusMakesGreater :: forall n x. (0 < x) :- (n < n + x)
plusMakesGreater = fakeProof

lesserWithConstant :: forall n a b. (a < b) :- ((n + a) < (n + b))
lesserWithConstant = fakeProof

addInvertsMinus :: forall n x. (x <= n) :- (n ~ (n - x) + x)
addInvertsMinus = fakeProof

symmetricAdd :: forall a b. () :- (a + b ~ b + a)
symmetricAdd = fakeProof

associativeAdd :: forall a b c. () :- ((a + b) + c ~ a + (b + c))
associativeAdd = fakeProof

fakeProof :: a :- b
fakeProof = unsafeCoerce (Sub $ unsafeCoerce $ Dict @())
