module BitMachine.BitCircuit.Combinators where

import BitMachine.BitCircuit
import BitMachine.Proofs
import Data.List.Sized
import Data.Type.Ord
import GHC.TypeNats

bcZip :: forall f n. (KnownNat n) => BitCircuit f 2 1 -> BitCircuit f (n + n) n
bcZip bc = case cmpNat (natSing @n) (natSing @0) of
  EQI -> bcId
  GTI ->
    withProof (ordToGreater @0 @n) $
      withProof (greaterToGreaterEqual @0 @n) $
        withProof (greaterStaysGreater @0 @n @n) $
          withProof (plusMakesGreater @n @n) $
            bcPar @(n + n) @1 @(n - 1)
              ( bcPar (bcAt @0) (bcAt @(n))
                  #>> bc
              )
              ( bcDrop @1
                  #>> bcPar
                    (bcTake @(n - 1))
                    (bcDrop @n)
                  #>> bcZip bc
              )
  LTI -> error "bcZip: impossible pattern match"

bcMap :: forall a b n f. (KnownNat n, KnownNat a) => BitCircuit f a b -> BitCircuit f (n * a) (n * b)
bcMap bc = case cmpNat (natSing @n) (natSing @0) of
  EQI -> bcId
  LTI -> error "bcMap: impossible pattern match"
  GTI ->
    withProof (ordToGreater @0 @n) $
      withProof (greaterToGreaterEqual @0 @n) $
        bcTogether @a @b @((n - 1) * a) @((n - 1) * b)
          bc
          (bcMap @a @b @(n - 1) bc)

bcZipFoldRight :: forall f n x. (KnownNat x, KnownNat n) => BitCircuit f (x + 2) (x + 1) -> BitCircuit f (x + n + n) n
bcZipFoldRight bc = case cmpNat (natSing @n) (natSing @0) of
  EQI -> (bcTake @0)
  LTI -> error "bcZipFold: impossible pattern match"
  GTI ->
    withProof (ordToGreater @0 @n) $
      withProof (greaterToGreaterEqual @0 @n) $
        withProof (plusMakesGreater @(x + n) @n) $
          withProof (plusMakesGreater @(x) @n) $
            withProof (greaterStaysGreater @x @(x + n) @n) $
              ( bcPar @(x + n + n) @(1 + x) @((n - 1) + (n - 1))
                  ( bcPar
                      (bcTake @x)
                      (bcPar (bcAt @x) (bcAt @(x + n)))
                      #>> bc
                      #>> bcPar
                        (bcDrop @x)
                        (bcTake @x)
                  )
                  ( bcDrop @(x + 1)
                      #>> bcPar
                        (bcTake @(n - 1))
                        (bcDrop @n)
                  )
              )
                #>> bcPar @(1 + x + (n - 1) + (n - 1)) @1 @(n - 1)
                  (bcTake @1)
                  (bcDrop @1 #>> bcZipFoldRight bc)

bcZipFoldLeft :: forall f n x. (KnownNat x, KnownNat n) => BitCircuit f (2 + x) (1 + x) -> BitCircuit f (n + n + x) n
bcZipFoldLeft bc = case cmpNat (natSing @n) (natSing @0) of
  EQI -> (bcTake @0)
  LTI -> error "bcZipFold: impossible pattern match"
  GTI ->
    withProof (ordToGreater @0 @n) $
      withProof (greaterToGreaterEqual @0 @n) $
        withProof (plusMakesGreater @(n + x) @n) $
          withProof (plusMakesGreater @(x) @n) $
            withProof (plusMakesGreater @(n) @n) $
              withProof (minusMakesSmaller @1 @n) $
                withProof (greaterStaysGreater @x @(n + x) @n) $
                  withProof (plusSameStaysGreater @(n - 1) @(n) @n) $
                    withProof (greaterStaysGreater @((n - 1) + n) @(n + n) @x) $
                      withProof (greaterStaysGreater @n @(n + n) @x) $
                        withProof (greaterStaysGreater @(n - 1) @(n) @n) $
                          withProof (greaterStaysGreater @(n - 1) @(n + n) @x) $
                            ( bcPar @(x + n + n) @((n - 1) + (n - 1)) @(x + 1) 
                                ( bcPar @_ @(n - 1) @(n - 1)
                                    (bcTake @(n - 1) @(n + 1 + x))
                                    (bcDrop @n @(n + x) #>> bcTake @(n - 1) @(x + 1))
                                )
                                ( bcPar
                                    (bcPar (bcAt @(n - 1)) (bcAt @(n - 1 + n)))
                                    (bcDrop @(n + n))
                                    #>> bc
                                    #>> bcPar
                                      (bcDrop @1)
                                      (bcTake @1)
                                )
                            )
                              #>> bcPar @((n - 1) + (n - 1) + x + 1) @(n - 1) @1
                                (bcTake @((n - 1) + (n - 1) + x) #>> bcZipFoldLeft bc)
                                (bcDrop @((n - 1) + (n - 1) + x))

bcExpand :: forall a n f. (KnownNat n, KnownNat a) => BitCircuit f a (n * a)
bcExpand = case cmpNat (natSing @n) (natSing @0) of
  EQI -> bcDrop @a
  LTI -> error "bcExpand: impossible pattern match"
  GTI ->
    withProof (ordToGreater @0 @n) $
      withProof (greaterToGreaterEqual @0 @n) $
        bcPar bcId (bcExpand @_ @(n - 1))

-- | Select bits are the index for the SList
bcMultiplex :: forall n a b f. (KnownNat n, KnownNat b) => SList (2 ^ n) (BitCircuit f a b) -> BitCircuit f (n + a) b
bcMultiplex options = case cmpNat (natSing @n) (natSing @0) of
  LTI -> error "bcMultiplex: impossible pattern match"
  EQI -> case options of
    (SLCons option SLEmpty) -> option
    _ -> error "bcMultiplex: impossible pattern match"
  GTI ->
    withProof (ordToGreater @0 @n) $
      withProof (greaterToGreaterEqual @0 @n) $
        let (left, right) = (takeSList @(2 ^ (n - 1)) @(2 ^ (n - 1)) options, dropSList @(2 ^ (n - 1)) @(2 ^ (n - 1)) options)
         in bcTogether bcId (bcPar (bcMultiplex left) (bcMultiplex right))
              #>> bcPar
                (bcTake @(1 + b) #>> bcTogether (bcNot #>> bcExpand @1 @b) bcId #>> bcZip bcAnd)
                ( bcPar
                    (bcTake @1)
                    (bcDrop @(1 + b))
                    #>> bcTogether (bcExpand @1 @b) bcId
                    #>> bcZip bcAnd
                )
              #>> bcZip bcOr
