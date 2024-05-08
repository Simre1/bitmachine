{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeAbstractions #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module BitCircuit where

import Data.Constraint
import Data.Kind
import Data.Maybe (fromMaybe)
import Data.Type.Ord
import GHC.TypeLits
import Proofs
import Type.Reflection
import Unsafe.Coerce (unsafeCoerce)

data BitCircuit (f :: Nat -> Nat -> Type) (a :: Nat) (b :: Nat) where
  CAnd :: BitCircuit f 2 1
  COr :: BitCircuit f 2 1
  CNot :: BitCircuit f 1 1
  CSequence :: BitCircuit f a b -> BitCircuit f b c -> BitCircuit f a c
  CPar :: BitCircuit f a b -> BitCircuit f a c -> BitCircuit f a (b + c)
  CHigh :: BitCircuit f 0 1
  CId :: BitCircuit f a a
  CDrop :: SNat a -> BitCircuit f (a + b) b
  CTake :: SNat a -> BitCircuit f (a + b) a
  CAt :: (i < n) => SNat i -> BitCircuit f n 1
  CEff :: f a b -> BitCircuit f a b

deriving instance Show (BitCircuit NoEffect a b)

data NoEffect a b deriving (Show)

assertEqual :: SNat a -> SNat b -> a :~: b
assertEqual t1@SNat t2@SNat =
  fromMaybe (error "Not equal type reps") $ sameNat t1 t2

hoistF :: BitCircuit NoEffect a b -> BitCircuit f a b
hoistF = unsafeCoerce

bcZip :: forall f n. (KnownNat n) => BitCircuit f 2 1 -> BitCircuit f (n + n) n
bcZip bc = case cmpNat (natSing @n) (natSing @1) of
  EQI -> bc
  GTI ->
    withDict (ordToGreater @1 @n) $
      withDict (transitiveLesser @0 @1 @n) $
        withDict (greaterStaysGreater @0 @n @n) $
          withDict (plusMakesGreater @n @n) $
            withDict (greaterToGreaterEqual @n) $
              CPar @_ @(n + n) @1 @(n - 1)
                ( CSequence
                    (CPar (CAt (natSing @0)) (CAt (natSing @(n))))
                    bc
                )
                ( CSequence
                    ( CSequence
                        (CDrop (natSing @1))
                        ( CPar
                            (CTake (natSing @(n - 1)))
                            (CDrop (natSing @n))
                        )
                    )
                    (bcZip bc)
                )
  LTI -> withDict (lesserToZero @n *** ordToLesser @n @1) CId

notCircuit :: forall f n. (KnownNat n) => BitCircuit f n n
notCircuit = case cmpNat (natSing @n) (natSing @1) of
  GTI ->
    withDict (ordToGreater @1 @n) $
      withDict (greaterToGreaterEqual @n) $
        CPar @_ @n @1 @(n - 1)
          (CSequence (CTake (natSing @1)) CNot)
          (CSequence (CDrop (natSing @1)) notCircuit)
  EQI -> CNot
  LTI -> CId

bcTogether :: forall f a b c d. (KnownNat a) => BitCircuit f a b -> BitCircuit f c d -> BitCircuit f (a + c) (b + d)
bcTogether bc1 bc2 =
  CPar
    (CSequence (CTake (natSing @a)) bc1)
    (CSequence (CDrop (natSing @a)) bc2)

bcZipFold :: forall f n x. (KnownNat x, KnownNat n) => BitCircuit f (x + 2) (x + 1) -> BitCircuit f (x + n + n) n
bcZipFold bc = case cmpNat (natSing @n) (natSing @1) of
  EQI -> CSequence bc (CTake (natSing @1))
  GTI ->
    withDict (ordToGreater @1 @n) $
      withDict (transitiveLesser @0 @1 @n) $
        withDict (greaterStaysGreater @0 @n @n) $
          withDict (greaterStaysGreater @0 @n @(x + n)) $
            withDict (plusMakesGreater @n @n) $
              withDict (plusMakesGreater @(x + n) @n) $
                withDict (plusMakesGreater @(x) @n) $
                  withDict (greaterStaysGreater @n @(n + n) @x) $
                    withDict (greaterStaysGreater @x @(x + n) @n) $
                      withDict (greaterToGreaterEqual @n) $
                        CSequence
                          ( CPar @_ @(x + n + n) @(1 + x) @((n - 1) + (n - 1))
                              ( CSequence
                                  ( CSequence
                                      ( CPar
                                          (CTake (natSing @x))
                                          (CPar (CAt (natSing @x)) (CAt (natSing @(x + n))))
                                      )
                                      bc
                                  )
                                  ( CPar
                                      (CDrop (natSing @x))
                                      (CTake (natSing @x))
                                  )
                              )
                              ( CSequence
                                  (CDrop (natSing @(x + 1)))
                                  ( CPar
                                      (CTake (natSing @(n - 1)))
                                      (CDrop (natSing @n))
                                  )
                              )
                          )
                          ( CPar @_ @(1 + x + (n - 1) + (n - 1)) @1 @(n - 1)
                              (CTake (natSing @1))
                              (CSequence (CDrop (natSing @1)) (bcZipFold bc))
                          )
  LTI -> withDict (lesserToZero @n *** ordToLesser @n @1) (CTake (natSing @0))
