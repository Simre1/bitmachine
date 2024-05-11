{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module BitMachine.BitCircuit.Pretty where

import BitMachine.BitCircuit
import Data.Data (Typeable)
import Data.Text (Text)
import GHC.TypeNats
import Prettyprinter
import Type.Reflection
import Prettyprinter.Render.Terminal (putDoc)

prettyPrintBitCircuit :: forall x a b f. (Show x, Typeable f) => ([x] -> BitCircuit f a b -> x) -> BitCircuit f a b -> IO ()
prettyPrintBitCircuit extraShow bitCircuit = putDoc $ go bitCircuit <> line
  where
    go :: forall a b ann. BitCircuit f a b -> Doc ann
    go = \case
      BCAnd -> "and"
      BCOr -> "or"
      BCNot -> "not"
      BCSequence a b -> align (go a) <+> "->" <+> align (go b)
      BCPar a b -> vsep [nest 2 ("> " <> go a), nest 2 ("> " <> go b)] <> line
      BCHigh -> "1"
      BCId -> "id"
      BCDrop s -> "drop" <+> pretty (show $ fromIntegral @_ @Int $ fromSNat s)
      BCTake s -> "take" <+> pretty (show $ fromIntegral @_ @Int $ fromSNat s)
      BCAt s -> "at" <+> pretty (show $ fromIntegral @_ @Int $ fromSNat s)
      BCFeedback _ bc -> vsep ["feedback", hang 1 $ go bc]
      BCEff _ _ -> pretty $ show (typeRep @f)
      BCComponent _ bc -> go bc
