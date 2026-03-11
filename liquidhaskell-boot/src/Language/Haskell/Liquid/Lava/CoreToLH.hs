{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TupleSections #-}

-- |
-- - Main module for the translation between GHC Core Haskell and Internal Liquid Haskell
module Language.Haskell.Liquid.Lava.CoreToLH (transBind) where

import           Control.Exception (assert)
import           Data.Bifunctor (first, second)
import           Data.Data (Data)
import qualified Data.HashMap.Strict as HM
import qualified Data.Map.Strict as M
import qualified Data.Text as Text

-- import GHC.Parser.Annotation
-- import GHC.Types.Var hiding (Id)
-- import GHC.Types.SrcLoc
import           GHC.Core
import           GHC.Core.TyCo.Rep
import           GHC.Types.Literal
import           GHC.Types.Name
import           GHC.Utils.Outputable (ppr, showSDocUnsafe)
import qualified Language.Haskell.Liquid.GHC.Misc ()
import           Language.Haskell.Liquid.Types.RType (SpecType)
import           Language.Haskell.Liquid.Types.Types (AnnInfo (..))
import qualified Language.Haskell.Liquid.Types.Types ()

import           Lava.InternalLH (CaseBranch (..), LHSimpleTerm, LHTerm, ffTm, modifyBrBody, ttTm, unitTm)
import qualified Lava.InternalLH as ILH
import qualified Lava.LH as LH
import           Lava.Misc
import           Lava.Util

import qualified Language.Haskell.Liquid.Lava.SpecToLH as SLH

-- | Constraint synonym for GHC Core binder variables
type CoreBinder b = (Data b, Show b, NamedThing b)

-- | Translate Haskell binders, with mutually recursive binders unsupported for now.
-- Entry point for the translations in this module
--
-- > transBind(NonRec f = e) = trans(f,e)
-- > transBind(Rec [f_1 = e_1, …, f_n = e_n]) = trans(f_1,e_1)
transBind :: CoreBinder b => String -> AnnInfo SpecType -> Bind b -> LH.Def
transBind modId infTypes binds = case binds of
  NonRec b e -> let (args, body) = flattenFun modId infTypes (f b) e in
                LH.Def (f b) args body False
  Rec [(b, e)] -> let (args, body) = flattenFun modId infTypes (f b) e in
                  LH.Def (f b) args body True
  Rec defs -> error $ "Mutually recursive definitions " ++ show (map fst defs) ++ " not yet supported."
  where
    f b = stripLegalName modId $ show b

data ParsedEqn
  = Basic ILH.LHSimpleTerm
  | Eqn ParsedEqn ILH.LHSimpleTerm
  | Qmark ILH.LHTerm ParsedEqn
  deriving (Eq, Show)

-- | Classification of application head symbols.
data HeadSymbol
  = HNot | HLambda | HEqChain | HCast | HQmark | HPatError
  | HConst LHSimpleTerm | HUnbox | HBinOp ILH.Bop | HGeneric Id

-- | Classify an application head name into a 'HeadSymbol'.
classifyHead :: Id -> HeadSymbol
classifyHead "not"      = HNot
classifyHead "lambda"   = HLambda
classifyHead "==="      = HEqChain
classifyHead "***"      = HCast
classifyHead "?"        = HQmark
classifyHead "patError" = HPatError
classifyHead n
  | n `elem` ["()", "trivial", "True", "False"] = HConst (transName n)
  | n `elem` ["I#", "I"]                        = HUnbox
  | Just op <- M.lookup n SLH.bops              = HBinOp op
  | otherwise                                   = HGeneric n

-- | Does the term contain equational reasoning combinators?
hasEqn :: LHTerm -> Bool
hasEqn ILH.SEqn {}     = True
hasEqn (ILH.QMark s t) = hasEqn s || hasEqn t
hasEqn _               = False

unBasic :: LHTerm -> Maybe LHSimpleTerm
unBasic (ILH.BasicTerm tm) = Just tm
unBasic _                  = Nothing

-- | The head of a flattened Core application.
data AppHead
  = VarHead HeadSymbol  -- ^ head is a classified variable
  | ExprHead LHTerm     -- ^ head is a non-variable expression (already translated)

-- | Flatten and translate an application, returning a structured head.
--
-- > flattenCoreApp((x e_1) … e_n) = (NamedHead x, [trans(e_1), …, trans(e_n)])
-- > flattenCoreApp((e e_1) … e_n) = (ExprHead (trans e), [trans(e_1), …, trans(e_n)])
flattenCoreApp :: CoreBinder b => Id -> AnnInfo SpecType -> Id -> Expr b -> (AppHead, [LHTerm])
flattenCoreApp modId infTypes f (App g x) =
  second (++ [trans modId infTypes f x]) $ flattenCoreApp modId infTypes f g
flattenCoreApp modId _        _ (Var name) = (VarHead (classifyHead (stripLegalName modId $ show name)), [])
flattenCoreApp modId infTypes f t          = (ExprHead (trans modId infTypes f t), [])

-- | Translate a flattened application to ILH.
transFlattenedApp :: AppHead -> [LHTerm] -> LHTerm
transFlattenedApp (ExprHead g) args = case traverse unBasic (g : args) of
  Just (h : hargs) -> ILH.BasicTerm $ ILH.App h hargs
  _                -> unexpected "expression head" (g : args)
transFlattenedApp (VarHead HNot)          [ILH.BasicTerm tm]                  = ILH.BasicTerm $ ILH.Neg tm
transFlattenedApp (VarHead HLambda)       [ILH.BasicTerm (ILH.Var x), e]      = ILH.Lambda x e
transFlattenedApp (VarHead HEqChain)      [_, fstTerm, ILH.BasicTerm lstTerm] = transEqns (parseLHTerm fstTerm) lstTerm
transFlattenedApp (VarHead HCast) [_, eqChain, qed]
  | qed == ILH.BasicTerm (ILH.Var "QED") = case parseLHTerm eqChain of
      Eqn firstTerm lastTerm -> transEqns firstTerm lastTerm
      _                      -> eqChain
transFlattenedApp (VarHead HQmark)        (_ : _ : firstArg : secondArg : _)
  | hasEqn firstArg || hasEqn secondArg =
      mkQmark (prevEqns firstArg ++ [ILH.QMark secondArg (collectTm firstArg)])
  | otherwise =
      mkQmark (prevEqns firstArg ++ [ILH.QMark firstArg (collectTm secondArg)])
transFlattenedApp (VarHead HPatError)     _                                    = ILH.Undefined
transFlattenedApp (VarHead (HConst tm))   _                                    = ILH.BasicTerm tm
transFlattenedApp (VarHead HUnbox)        [singleArg]                          = singleArg
transFlattenedApp (VarHead (HBinOp op))   (_ : _ : a : b : _)                  =
  let (fstBnd, fstArg) = evaluate a
      (sndBnd, sndArg) = evaluate b
      binders = foldr (.) id (fstBnd ++ sndBnd)
  in  binders . ILH.BasicTerm $ ILH.Bop op fstArg sndArg
transFlattenedApp (VarHead (HGeneric n))  args                                 =
  let (letBinders, sArgs) = first (foldr (.) id . concat) . unzip $ map evaluate args
  in  letBinders . ILH.BasicTerm $ ILH.App (ILH.Var n) sArgs
transFlattenedApp (VarHead HNot)          args                                 = unexpected "not" args
transFlattenedApp (VarHead HLambda)       args                                 = unexpected "lambda" args
transFlattenedApp (VarHead HEqChain)      args                                 = unexpected "===" args
transFlattenedApp (VarHead HCast)         args                                 = unexpected "***" args
transFlattenedApp (VarHead HQmark)        args                                 = unexpected "?" args
transFlattenedApp (VarHead HUnbox)        args                                 = unexpected "unbox" args
transFlattenedApp (VarHead (HBinOp _))    args                                 = unexpected "binop" args

unexpected :: Id -> [LHTerm] -> a
unexpected n as = error $ "transFlattenedApp: unexpected args for " ++ show n ++ ": " ++ show as

transName :: Id -> LHSimpleTerm
transName "()"      = unitTm
transName "trivial" = unitTm
transName "True"    = ttTm
transName "False"   = ffTm
transName "?"       = error "Impossible: '?'"
transName n         = ILH.Var n

-- | Translate Haskell expressions.
-- The first argument is the name of the top-level binder we are translating.
-- Unsupported: casts, coercions, mutually recursive lets
-- Ignored: ticks
--
-- > trans(() e1 … en) = trans(trivial e1 … en) = trivial
-- > trans(True e1 … en) = True
-- > trans(False e1 … en) = False
-- > trans(literal) = literal
-- > trans(x e1 … en) = x [trans(e1), …, trans(en)]        -- if is a x variable
-- > trans(*** e1 (=== e2 e3 e4) QED) = transEqns(e3,e4) -- if trans(e1) = trans(e2)
-- > trans(? _ _ e1 e2 e3 … en) = ? ((hint) trans(e1)) trans(e2)
-- > trans(I# e) = trans(I e) = trans(e)
-- > trans(bop e1 e2) = bop trans(e1) trans(e2)
-- > trans(tick e) = trans(e)
-- > trans(type t) = TODO
-- > trans(case e _ _ of []) = trans(e)
-- > trans(case e _ _ of alts) = let y = trans(e) in trans(case y _ _ alts)  -- if trans(e) is a simple term and not a variable
-- > trans(case x _ _ of [ci xi* |-> ei]_i) = mkCase(x,[ci xi* |-> trans(ei)]_i)
-- > trans(let x = lit in e) = trans(e)   -- lit is ignored
-- > trans(let x = e' in e) = let x = trans(e') in trans(e)
-- > trans(let [x1 = e1, ..., xn=en] in e) = let x1 = trans(e1) in trans(e) -- the other binders are ignored
-- > trans(λx.e | cast | coercion) = unsupported
trans :: CoreBinder b => Id -> AnnInfo SpecType -> Id -> Expr b -> LHTerm
trans modId _        _ (Var n)           = ILH.BasicTerm $ transName (stripLegalName modId $ show n)
trans modId infTypes f app@App {}        = transApp modId infTypes f app
trans modId infTypes f (Lam x e)         = ILH.Lambda (stripLegalName modId $ show x) $ trans modId infTypes f e
trans modId infTypes f (Case e _ _ alts) = transCase modId infTypes f e alts
trans _     _        _ c@Cast {}         = error $ "cast expression not supported: " ++ toStr c
trans modId infTypes f (Tick _ e)        = trans modId infTypes f e
trans _     _        _ (Type t)          = transType t
trans _     _        _ c@Coercion {}     = error $ "coercion expression not supported: " ++ toStr c
trans modId infTypes f (Let bind e)      = transLet modId infTypes f bind e
trans _     _        _ (Lit lit)         = ILH.BasicTerm $ transLit lit

-- | Translate type arguments.
transType :: Type -> LHTerm
transType (GHC.Core.TyCo.Rep.TyConApp tyCon []) = ILH.BasicTerm (ILH.Var $ show tyCon)
transType t = error $ "Polymorphism not supported: " ++ toStr t

-- | Translate applications by flattening them and translating the parsed application.
transApp :: CoreBinder b => Id -> AnnInfo SpecType -> Id -> Expr b -> LHTerm
transApp modId infTypes f app = transFlattenedApp appHead args
  where
    (appHead, args) = flattenCoreApp modId infTypes f app

collectTm :: LHTerm -> LHTerm
collectTm (ILH.SEqn _ lstTm _) = ILH.BasicTerm lstTm
collectTm (ILH.QMark t _)      = collectTm t
collectTm tm                   = tm

prevEqns :: LHTerm -> [LHTerm]
prevEqns eq@ILH.SEqn {}  = [eq]
prevEqns (ILH.QMark t _) = prevEqns t
prevEqns _               = []

evaluate :: LHTerm -> ([LHTerm -> LHTerm], LHSimpleTerm)
evaluate (ILH.BasicTerm t) = ([], t)
evaluate tm                = ([ILH.Let x Nothing tm], ILH.Var x)
  where
    x = "x_" ++ hashName tm

-- | Translate case expressions.
transCase :: CoreBinder b => Id -> AnnInfo SpecType -> Id -> Expr b -> [Alt b] -> LHTerm
transCase modId infTypes f e []   = trans modId infTypes f e
-- NOTE: we could support match on simple terms
transCase modId infTypes f e alts = case eT of
    ILH.BasicTerm (ILH.Var x') -> mkCase f x' branches
    ILH.BasicTerm {} -> ILH.Let y Nothing eT (mkCase f y branches)
    _ -> error $ "unexpected case: case " ++ show eT ++ " of \n" ++ intercalate "\n" (map show branches)
  where
    eT = trans modId infTypes f e
    y = "x_" ++ hashName eT
    branches = map (altToClause modId infTypes f) alts

-- | Translate let bindings.
transLet :: CoreBinder b => Id -> AnnInfo SpecType -> Id -> Bind b -> Expr b -> LHTerm
transLet modId infTypes f bind e =
    let (x, e') = deconstructBind bind in
    case e' of
      Lit {} -> trans modId infTypes f e -- ignore let lit (part of patError)
      _ ->
        ILH.Let
          (stripLegalName modId $ show x)
          (Just $ SLH.transType "" (SLH.ConstrArgsCtx Nothing []) $ binderType infTypes x)
          (trans modId infTypes f e')
          (trans modId infTypes f e)

-- | Trivial translation of literals
transLit :: Literal -> LHSimpleTerm
transLit (LitNumber _ n) = ILH.IntLit n
transLit (LitString s)   = ILH.StringLit $ show s
transLit (LitFloat x)    = ILH.FloatLit $ fromRational x
transLit (LitDouble x)   = ILH.FloatLit $ fromRational x
transLit other           = error $ "Unsupported literal " ++ toStr other

-- | Fall back to non-mutually recursive binds.
-- NB: silently ignores mutually recursive groups.
deconstructBind :: (NamedThing b) => Bind b -> (b, Expr b)
deconstructBind (NonRec b e)       = (b, e)
deconstructBind (Rec ((b, e) : _)) = (b, e)
deconstructBind (Rec [])           = error "Found empty list of mutually recursive binders while translating."

-- | Retrieves the type inferred by Liquid Haskell for a variable
binderType :: (Show b, NamedThing b) => AnnInfo SpecType -> b -> SpecType
binderType (AI infTypes) x =
  case HM.lookup (getSrcSpan x) infTypes of
    Just [(Just qualifName, tp)] ->
      assert (Text.unpack (snd $ Text.breakOnEnd (Text.singleton '.') qualifName) == show x) tp
    _ -> error $ "Type annotation for " ++ show x ++ " not found."

-- | Straightforward translation of Haskell cases
altToClause :: CoreBinder b => Id -> AnnInfo SpecType -> Id -> Alt b -> CaseBranch
altToClause modId infTypes f (Alt con bs e) =
  CaseBranch (go con)
             (map (stripLegalName modId . show) bs)
             (trans modId infTypes f e)
  where
    go :: AltCon -> String
    -- NOTE: was `show dc`, but no show instance for DataCon
    go (DataAlt dc) = stripLegalName modId $ showSDocUnsafe (ppr dc)
    go (LitAlt lit) = show (transLit lit)
    go DEFAULT = "_"

-- | Flattens and translate abstractions
--
-- > flattenFun(λx1. λx2.…λxn.e) = λx1…xn.trans(e)
flattenFun :: CoreBinder b => Id -> AnnInfo SpecType -> Id -> Expr b -> ([Id], LHTerm)
flattenFun modId infTypes f (Lam b e) = first ((stripLegalName modId . show) b :) $ flattenFun modId infTypes f e
flattenFun modId infTypes f e         = ([], trans modId infTypes f e)

-- | combine lists of 'LHSimpleTerm's into a single 'LHTerm' using 'QMark', observe that 'mkQmark . map Hint' is a right-inverse of 'flattenQmarks'
mkQmark :: [LHTerm] -> LHTerm
mkQmark []     = ILH.BasicTerm unitTm
mkQmark (z:zs) = foldl ILH.QMark z zs

-- TODO: does this also work for (nested) === operators with hints (using the ? combinator)?

parseLHTerm :: LHTerm -> ParsedEqn
parseLHTerm (ILH.BasicTerm t)                          = Basic t
parseLHTerm (ILH.QMark eq@ILH.SEqn {} (ILH.QMark h t)) = Qmark eq (Qmark h (parseLHTerm t))
parseLHTerm (ILH.QMark t h)                            = Qmark h (parseLHTerm t)
parseLHTerm (ILH.SEqn s t h)                           = Eqn (Qmark h (Basic s)) t
parseLHTerm other                                      = error $ "Expected simple term or proof combinator but found " ++ show other

-- | translate an 'LHTerm' representation of a (nested) === combinator to the corresponding ILH data structure
transEqns :: ParsedEqn -> LHSimpleTerm -> LHTerm
transEqns s' =
  {- traceFuncRet ["transEqns", show s', show t'] $ -}
  mkQmark . recurse s'
  where
    recurse :: ParsedEqn -> LHSimpleTerm -> [LHTerm]
    recurse (Basic s)                                    v = [ILH.SEqn s v (mkQmark [])]
    recurse (Qmark eq@ILH.SEqn {} s)                     v = eq : recurse s v
    recurse (Qmark nextHint (Qmark nextHint' s))         v = recurse (Qmark (ILH.QMark nextHint nextHint') s) v
    recurse (Qmark nextHint (Basic nextTerm))            v = [ILH.SEqn nextTerm v (mkQmark [nextHint])]
    recurse (Qmark h s@Eqn {})                           v = h : recurse s v
    recurse (Eqn (Basic s) t)                            v = [ILH.SEqn s t (mkQmark []), ILH.SEqn t v (mkQmark [])]
    recurse (Eqn (Qmark nextHint (Qmark nextHint' s)) t) v = recurse (Eqn (Qmark (ILH.QMark nextHint nextHint') s) t) v
    recurse (Eqn (Qmark nextHint s) t)                   v = recurse s t ++ [ILH.SEqn t v (mkQmark [nextHint])]
    recurse (Eqn (Eqn s t) u)                            v = recurse s t ++ [ILH.SEqn t u (mkQmark []), ILH.SEqn u v (mkQmark [])]

{- The following is based on code liquidhaskell-boot Transforms/CoreToLogic -}

-- | Cut redundant branches and matches and construct the given match
mkCase :: Id -> Id -> [CaseBranch] -> ILH.LHTerm
mkCase f x = transCaseExpr (Just f) x False

collapseUnproductiveMatches :: CaseBranch -> CaseBranch
collapseUnproductiveMatches = modifyBrBody go
  where
    go e = case e of
      -- ILH.Case x [CaseBranch "False" [] elseE, CaseBranch "True" [] thenE] _ -> ILH.Ite (ILH.Var x) thenE elseE
      ILH.Case x branches b -> ILH.Case x (map collapseUnproductiveMatches branches) b
      _ -> e

-- | remove redundant branches/matches from an ILH pattern match
transCaseExpr :: Maybe Id -> Id -> Bool -> [ILH.CaseBranch] -> ILH.LHTerm
transCaseExpr = recurse []
  where
    recurse :: [(Id, (Id, [Id]))] -> Maybe Id -> Id -> Bool -> [ILH.CaseBranch] -> ILH.LHTerm
    recurse prevPats fO indVar isRec cases' =
      {- traceFuncRet ["recurse", show prevPats, show fO, indVar, show isRec, show cases] $ -}
      subst substs res
      where
        cases = map (\br -> modifyBrBody
                              (replaceSubterm (TermPat (ILH.Var indVar), True)
                                              (ILH.App (ILH.Var (brCon br)) (map ILH.Var (brVars br))))
                              br) cases'
        res = caseOrInduct indVar branches
        {- res = case branches of
          -- [CaseBranch "False" [] elseE, CaseBranch "True" [] thenE] -> ILH.Ite (ILH.Var indVar) thenE elseE
          _ -> caseOrInduct indVar branches -}
        (cutCases, substs) = cutRedundantBranches indVar prevPats cases
        cleanedCases = map collapseUnproductiveMatches cutCases
        isRecursive :: ILH.LHTerm -> Bool
        isRecursive e =
          maybe False
            (\f -> hasMatch (TermPat (ILH.Var f), True) e) fO
        branches = map (modifyBrBody transBranchE) cleanedCases
        transBranchE :: ILH.LHTerm -> ILH.LHTerm
        transBranchE e = case e of
          ILH.Case (ILH.Var x) css _ -> recurse prevPats fO x (isRecursive e) css
          ILH.Let x tpx def tm       -> ILH.Let x tpx (transBranchE def) (transBranchE tm)
          _ -> e
        {- Case (Let x def _) _ css -> LHTerm $ Let x (transBranchE def) (LHTerm $ recurse prevPats fO x (isRecursive e) css)
        _ -> transAExpr fO e (isRecursive e) -}
        caseOrInduct :: Id -> [ILH.CaseBranch] -> ILH.LHTerm
        caseOrInduct x brs = ILH.Case (ILH.Var x) brs anyIsRec
        anyIsRec = isRec || any (isRecursive . brBody) branches

    -- \| Remove cases from nested matches whose patterns contradict the current branch's pattern in an ambient match
    cutRedundantBranches :: Id -> [(Id, (Id, [Id]))] -> [ILH.CaseBranch] -> ([ILH.CaseBranch], [(Id, ILH.LHSimpleTerm)])
    cutRedundantBranches n prevPats = second concat . unzip . cutBranches . filterBranches
      where
        filterBr (CaseBranch c cargs tm) =
          ((n, (c, cargs)) `notElem` prevPats)
            || trace
              ( unwords
                  [ "cutting case: "
                  , show (c, cargs)
                  , show tm
                  , "from match on"
                  , show n
                  , "due to redundancy with previous match patterns"
                  , show prevPats
                  ]
              )
              False
        filterBranches = filter filterBr
        cutBranches :: [ILH.CaseBranch] -> [(ILH.CaseBranch, [(Id, ILH.LHSimpleTerm)])]
        cutBranches = mapMaybe (\(CaseBranch c cargs e) ->
                                    first (CaseBranch c cargs) <$> cutRedundantMatches (prevPats ++ [(n, (c, cargs))]) e)

    -- \| Translate nested matches, replacing redundant matches with the translation of the only matching branch
    cutRedundantMatches :: [(Id, (Id, [Id]))] -> ILH.LHTerm -> Maybe (ILH.LHTerm, [(Id, ILH.LHSimpleTerm)])
    cutRedundantMatches prevPats (ILH.Case (ILH.Var m) branches _) | m `elem` map fst prevPats = res
      where
        -- \| The previous pattern in which we already matched on the same variable as we do now, if any
        prevPat = find ((== m) . fst) prevPats
        -- \| Pattern and expression in the branch, in which the pattern matches the previous pattern, if any
        caseExpr = find ((== (fst . snd <$> prevPat)) . Just . brCon) branches
        caseVarSub = case (snd . snd <$> prevPat, brVars <$> caseExpr) of
          (Just args, Just args') -> newSubst
            where
              newSubst = mapMaybe mkSubstO (zip args args')
              mkSubstO (x, y) = case (unspecName x, unspecName y) of
                (True, False) -> Just (x, ILH.Var y) -- if variable is specified now, but not earlier use current name throughout
                (False, True) -> Just (y, ILH.Var x) -- if variable was specified before, but not now use previous name here as well
                (_, _) -> Nothing
          _ -> []
        -- \| The translation of the only branch in which the pattern is consistent with the previously matched pattern matched against the same expression
        recO = maybe ((,[]) . brBody <$> caseExpr) (cutRedundantMatches prevPats . brBody) caseExpr
        res = second (++ caseVarSub) <$> recO
    cutRedundantMatches prevPats (ILH.Case (ILH.Var m) branches b) = Just (ILH.Case (ILH.Var m) branches' b, subs)
      where
        (branches', subs) = cutRedundantBranches m prevPats branches
    cutRedundantMatches _        tm                                = Just (tm, [])
