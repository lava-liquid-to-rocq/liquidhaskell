{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wall #-}

module Language.Haskell.Liquid.RefCore.Simplify
  ( prepareBind, typeAppMarker
  ) where

import Control.Monad.State.Strict
import Data.List (find, isPrefixOf, nub, stripPrefix)
import qualified Data.HashSet as Set
import Text.Read (readMaybe)
import qualified Data.Map.Strict as M

import GHC.Builtin.Types (falseDataCon, intDataCon, trueDataCon)
import GHC.Core
import GHC.Core.DataCon (dataConName, dataConWorkId)
import GHC.Data.FastString (LexicalFastString (..), fsLit, unpackFS)
import GHC.Types.Id (isDataConId_maybe)
import GHC.Types.Literal (Literal (LitNumber))
import GHC.Types.SrcLoc (mkRealSrcLoc, mkRealSrcSpan)
import GHC.Types.Tickish (GenTickish (SourceNote))
import qualified Language.Fixpoint.Types as F
import qualified Language.Fixpoint.Types.Visitor as FV
import Language.Haskell.Liquid.Types.RType (SpecType)
import Language.Haskell.Liquid.Types.RTypeOp (mapExprReft)
import GHC.Types.Var
-- needed for Show Var instance
import Language.Haskell.Liquid.GHC.Misc ()

import Language.Haskell.Liquid.RefCore.Misc (TypeApplications, showStripped, typeAppSite)

-- The markers are put on the extractor's private Core copy, never on the
-- program sent to LiquidHaskell. They keep the occurrence attached to its
-- argument through ANF substitution.
typeAppMarker :: GenTickish pass -> Maybe Int
typeAppMarker (SourceNote _ name) = stripPrefix "RefCore type argument " (unpackFS (getLexicalFastString name)) >>= readMaybe
typeAppMarker _ = Nothing

-- | Prepare an ANF binding for extraction. Match each application against
-- the checked Core before substituting its terms. Use the same lexical scope
-- to substitute the values referred to by its solved type arguments.
prepareBind
  :: [F.DataDecl]
  -> TypeApplications
  -> CoreBind
  -> (CoreBind, M.Map Int (Either String [SpecType]))
prepareBind dataDecls solved bind =
    (prepared, M.map resolve sites)
  where
    (prepared, (_, sites)) = runState (prepare (Scope M.empty M.empty) bind) (0 :: Int, M.empty)
    counts = M.fromListWith (+) [(site, 1 :: Int) | (site, _) <- M.elems sites]
    resolve (site, scope)
      | M.lookup site counts /= Just 1 = Left ("ambiguous Core type application " ++ show site)
      | Just templates <- M.lookup site solved =
          Right (map (normalizeType dataDecls scope) templates)
      | otherwise = Left ("missing solved type for Core type application " ++ show site)

    prepare scope (NonRec binder rhs) = NonRec binder <$> rewrite scope binder rhs
    prepare scope (Rec bindings) =
      let innerScope = withoutBindings scope (map fst bindings)
       in Rec <$> traverse (\(binder, rhs) -> (,) binder <$> rewrite innerScope binder rhs) bindings

    rewrite scope binder app@(App fun arg@(Type _)) = do
      fun' <- rewrite scope binder fun
      (index, current) <- get
      put (index + 1, M.insert index (typeAppSite binder app, predicateValues scope) current)
      let position = mkRealSrcLoc (fsLit "<RefCore>") 1 1
          marker = SourceNote (mkRealSrcSpan position position) (LexicalFastString (fsLit ("RefCore type argument " ++ show index)))
      pure (App fun' (Tick marker arg))
    rewrite scope binder (App fun arg) = App <$> rewrite scope binder fun <*> rewrite scope binder arg
    rewrite scope binder (Let (NonRec var rhs) body) = do
      rhs' <- rewrite scope var rhs
      let inline = isANFVar var
          symbol = F.symbol var
          terms = if inline then M.insert var rhs' (inlinedTerms scope) else M.delete var (inlinedTerms scope)
          values = case knownValue scope rhs of
            Just value -> M.insert symbol value (predicateValues scope)
            Nothing -> M.delete symbol (predicateValues scope)
      body' <- rewrite (Scope terms values) binder body
      pure $ if inline then body' else Let (NonRec var rhs') body'
    rewrite scope binder (Let binding@(Rec bindings) body) =
      Let <$> prepare scope binding <*> rewrite (withoutBindings scope (map fst bindings)) binder body
    rewrite scope binder (Lam argument body) =
      Lam argument <$> rewrite (withoutBinding argument scope) binder body
    rewrite scope binder (Case scrutinee scrutineeBinder result alternatives) =
      Case <$> rewrite scope scrutineeBinder scrutinee <*> pure scrutineeBinder <*> pure result
           <*> traverse (rewriteAlt (withoutBinding scrutineeBinder scope) binder) alternatives
    rewrite scope binder (Cast expr co) = flip Cast co <$> rewrite scope binder expr
    rewrite scope binder (Tick tick expr) = Tick tick <$> rewrite scope binder expr
    rewrite scope _ expr@(Var var) =
      pure (M.findWithDefault expr var (inlinedTerms scope))
    rewrite _ _ expr = pure expr

    rewriteAlt scope binder (Alt con binders body) =
      Alt con binders <$> rewrite (withoutBindings scope binders) binder body

    withoutBindings = foldr withoutBinding
    withoutBinding var scope =
      Scope (M.delete var (inlinedTerms scope)) (M.delete (F.symbol var) (predicateValues scope))

isANFVar :: Var -> Bool
isANFVar = isPrefixOf "lq_anf" . showStripped

data Scope = Scope
  { inlinedTerms :: M.Map Var CoreExpr
  , predicateValues :: ValueScope
  }

type ValueScope = M.Map F.Symbol F.Expr

-- | Interpret only literal bindings and constructor applications. In
-- particular, the exporter does not evaluate arbitrary Haskell functions.
knownValue :: Scope -> CoreExpr -> Maybe F.Expr
knownValue scope (Tick _ expr) = knownValue scope expr
knownValue _ (Lit (LitNumber _ n)) = Just (F.ECon (F.I n))
knownValue scope expr
  | (Var var, args, _) <- collectArgsTicks (const True) expr
  , Just dc <- isDataConId_maybe var
  , Just values <- traverse (knownValue scope) [arg | arg <- args, not (isTypeArg arg)] =
      Just (constructorValue (F.symbol (dataConName dc)) values)
  | (Var var, [], _) <- collectArgsTicks (const True) expr =
      let symbol = F.symbol var
       in Just (M.findWithDefault (F.EVar symbol) symbol (predicateValues scope))
knownValue _ _ = Nothing

constructorValue :: F.Symbol -> [F.Expr] -> F.Expr
constructorValue con [num@(F.ECon (F.I _))]
  | con == F.symbol (dataConName intDataCon) || con == F.symbol (dataConWorkId intDataCon) = num
constructorValue con args = foldl F.EApp (F.EVar con) args

normalizeType :: [F.DataDecl] -> ValueScope -> SpecType -> SpecType
normalizeType dataDecls scope = mapExprReft normalize
  where
    normalize binder expr =
      let substitutions = F.mkSubst (M.toList (M.delete binder scope))
          rewritten = F.rapierSubstExpr (F.substSymbolsSet substitutions `Set.union` F.syms expr) substitutions expr
          next = FV.trans reduce
          fixedPoint e = let e' = next e in if e' == e then e else fixedPoint e'
       in fixedPoint rewritten

    constructorFamilies = map F.ddCtors dataDecls
    constructors = concat constructorFamilies
    testerFamilies =
      [(F.testSymbol (F.symbol con), (F.symbol con, map F.symbol family))
      | family <- constructorFamilies, con <- family]
    reduce (F.EVar sym)
      | sym == F.symbol (dataConName trueDataCon) = F.PTrue
      | sym == F.symbol (dataConName falseDataCon) = F.PFalse
    reduce (F.EApp (F.EVar fun) arg)
      | (F.EVar con, args) <- flattenLogicApp arg
      , Just ctor <- find ((== con) . F.symbol) constructors
      , let fields = F.dcFields ctor
      , length args == length fields =
          case lookup fun testerFamilies of
            Just (expected, family) | con `elem` family -> boolean (con == expected)
            _ -> maybe (F.EApp (F.EVar fun) arg) id $ lookup fun (zip (map F.symbol fields) args)
      | otherwise = constructorValue fun [arg]
    reduce (F.ECst e@(F.ECon (F.I _)) F.FInt) = e
    reduce (F.PAtom F.Eq lhs rhs) | lhs == rhs = F.PTrue
    reduce (F.PAtom F.Ne lhs rhs) | lhs == rhs = F.PFalse
    reduce (F.PAtom F.Eq (F.ECon (F.I lhs)) (F.ECon (F.I rhs))) = boolean (lhs == rhs)
    reduce (F.PNot F.PFalse) = F.PTrue
    reduce (F.PNot F.PTrue) = F.PFalse
    reduce (F.PAnd es)
      | F.PFalse `elem` es = F.PFalse
      | otherwise = F.pAnd (nub (filter (/= F.PTrue) es))
    reduce (F.POr es)
      | F.PTrue `elem` es = F.PTrue
      | otherwise = F.pOr (nub (filter (/= F.PFalse) es))
    reduce expr = expr

    boolean True = F.PTrue
    boolean False = F.PFalse

flattenLogicApp :: F.Expr -> (F.Expr, [F.Expr])
flattenLogicApp = go []
  where
    go args (F.EApp f arg) = go (arg : args) f
    go args f = (f, args)
