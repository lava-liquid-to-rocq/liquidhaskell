{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Lava.Util
  ( module Data.Maybe,
    module Lava.Util,
    module Control.Applicative,
    module Data.List,
    module Data.Functor,
    module Data.Tuple.Extra,
    module Debug.Trace,
  )
where

import Control.Applicative ((<|>))
import qualified Data.Bifunctor as B
import Data.Char (isDigit)
import Data.Data
import Data.Functor ((<&>))
import Data.Hashable (hash)
import Data.List (find, intercalate, isInfixOf, isPrefixOf, isSuffixOf, partition, singleton, stripPrefix)
import Data.Maybe (catMaybes, fromJust, fromMaybe, isJust, isNothing, mapMaybe, maybe, maybeToList)
import Data.Tuple.Extra (fst3, snd3, thd3)
import Debug.Trace
import Prelude

type Id = String

finalDelim = ". "

intermediateDelim = ". "

addParens :: String -> String
-- addParens s@(c:cs) | c == '(' && last s == ')' = s
addParens s
  | bracketed && correctlyBracketed 0 sStripped = s
  | otherwise = if ' ' `elem` s || ':' `elem` s then "(" ++ s ++ ")" else s
  where
    bracketed = safeHead s == Just '(' && last s == ')' || safeHead s == Just '{' && last s == '}'
    sStripped = if bracketed then (init . tail) s else s
    correctlyBracketed :: Int -> String -> Bool
    correctlyBracketed n (brO : tl) | brO `elem` "({[" = correctlyBracketed (n + 1) tl
    correctlyBracketed n (brC : _) | brC `elem` ")}]" && n <= 0 = False
    correctlyBracketed n (brC : tl) | brC `elem` ")}]" = correctlyBracketed (n - 1) tl
    correctlyBracketed n (_ : tl) = correctlyBracketed n tl
    correctlyBracketed n [] = n == 0

showForall :: (Show a) => (Show b) => [(Id, a)] -> b -> String
showForall [] ret = show ret
showForall (("_", t) : tl) ret = show t ++ "->" ++ showForall tl ret
showForall args ret = addParens $ argsS ++ show ret
  where
    argsS = if null args then "" else "forall " ++ concatMap (\(x, t) -> addParens (showArg x t) ++ " ") args ++ ", "
    showArg x tp = addParens (x ++ (if show tp == "_" then "" else (": " ++ show tp)))

showP :: (Show a) => a -> String
showP = addParens . show

mkDistinct :: [(Id, a)] -> [(Id, a)]
mkDistinct [] = []
mkDistinct ((x, xData) : tl) = (x, xData) : (mkDistinct (mapFst (\y -> if y == x then y ++ "_" else y) tl))

removeSuffix :: (Eq a) => [a] -> [a] -> [a]
removeSuffix suffix orig = reverse $ removePrefix (reverse suffix) (reverse orig)

unspecName x = ("lq_anf" `isPrefixOf` x && all isDigit (removePrefix "lq_anf" x)) || "ds_d" `isPrefixOf` x

removePrefix prefix orig = fromMaybe orig $ stripPrefix prefix orig

stripSuffixO suf s = reverse <$> stripPrefix (reverse suf) (reverse s)

showNewline :: Int -> String
showNewline indent = "\n" ++ concat (replicate indent "\t")

-- | pretty print indented code elements, separated by given delimiter
showIndent :: (PrettyPrintable a) => String -> Bool -> Int -> [a] -> String
showIndent delim delimitLast indent codeElems = case codeElems of
  [] -> ""
  code : moreCode -> codeS ++ (if delimitLast || not (null moreCode) then sep else "") ++ showIndent delim delimitLast indent moreCode
    where
      codeS = prettyPrint indent code
      done = null moreCode
      codeDelim
        | includesBranches code = ""
        | done = finalDelim
        | otherwise = delim
      sep = codeDelim ++ if done then "" else showNewline indent

-- pretty print tactic concatenation
showTacs :: (PrettyPrintable a) => Int -> [a] -> String
showTacs = showIndent intermediateDelim True

-- | pretty prints several tactics (separated by the separator), while newlining and indenting branches of tactics
showTacBranch :: (PrettyPrintable a) => Int -> Bool -> [a] -> String
showTacBranch indent bracket prf
  | null prf = ""
  | indent > 0 = init (showNewline indent) ++ tacsS
  | otherwise = tacsS
  where
    tacsS = "  " ++ showSubprf indent (showTacs indent prf)
    showSubprf n s =
      if bracket
        then "{ " ++ s ++ " }"
        else case n of
          -- reserved for asserts
          0 -> "{ " ++ s ++ " } "
          _ -> replicate (n - 1) '-' ++ " " ++ s ++ " "

showTacBranches :: (PrettyPrintable a) => Int -> [(b, [a])] -> String
showTacBranches indent = concatMap (showTacBranch indent False . snd)

class (Show a) => PrettyPrintable a where
  -- | print the code element at given indentation level
  prettyPrint :: Int -> a -> String

  -- | whether the printed tactic included its own branches (if any) and those terminate the proof
  includesBranches :: a -> Bool
  includesBranches = const False

-- Get rid of module names.
showStripped :: (Show a) => a -> String
showStripped = strip . show

toStr :: (Data a) => a -> String
toStr = showConstr . Data.Data.toConstr

-- | produce an (almost certainly) unique number string for the given printable object
hashName :: (Show a) => a -> Id
hashName e = take 8 $ show (abs . hash $ show e)

conjPreds :: (a -> Bool) -> (a -> Bool) -> (a -> Bool)
conjPreds p q e = p e && q e

freshVar :: [Id] -> Id
freshVar = mkFresh "x"

-- TODO: decide if we want to rename inductive variables in some uniform way, to make them better distinguishable in the output
indPatVarName x = x -- ++ "'"

mkFresh :: Id -> [Id] -> Id
mkFresh x vars =
  let start :: Integer
      start = 1
      names = x : [x ++ "_" ++ show i | i <- [start .. 99999]]
      Just name = find ((`notElem` vars) `conjPreds` ((`notElem` vars) . indPatVarName)) names -- (\x -> x `notElem` vars && indPatVarName x `notElem` vars)
   in name

{-@ strip :: s:String -> String @-}
strip :: String -> String
strip s = case split '.' s of
  [] -> ""
  parts -> last parts

split :: Char -> String -> [String]
split c s = case rest of
  [] -> [chunk]
  _ : tl -> chunk : split c tl
  where
    (chunk, rest) = break (== c) s

safeHead :: [a] -> Maybe a
safeHead [] = Nothing
safeHead (x : _) = Just x

setAt :: [a] -> Int -> a -> [a]
setAt xs i x = take i xs ++ [x] ++ drop (i + 1) xs

{-@ modifyAt :: forall a. l: [a] -> {i: Int | i >= 0 && i < len l} -> f: (a -> a) -> [a] @-}
modifyAt :: [a] -> Int -> (a -> a) -> [a]
modifyAt xs i f = take i xs ++ [f $ xs !! i] ++ drop (i + 1) xs

deleteAt :: [a] -> Int -> [a]
deleteAt xs n = take n xs ++ drop (n + 1) xs

unzipMaybe :: Maybe (a, b) -> (Maybe a, Maybe b)
unzipMaybe = maybe (Nothing, Nothing) (B.bimap Just Just)

mcons :: Maybe a -> [a] -> [a]
mcons mx xs = maybe xs (: xs) mx

(?:) = mcons

infixr 5 ?:

toMaybe :: Bool -> a -> Maybe a
toMaybe b = if b then Just else const Nothing

notNull :: [a] -> Bool
notNull = not . null

mapSnd :: (a -> b) -> [(c, a)] -> [(c, b)]
mapSnd f = map $ B.second f

mapFst :: (c -> b) -> [(c, a)] -> [(b, a)]
mapFst f = map $ B.first f

mapThd :: (c -> d) -> [(a, b, c)] -> [(a, b, d)]
mapThd f = map (\(x, y, z) -> (x, y, f z))

mapFrth :: (d -> e) -> [(a, b, c, d)] -> [(a, b, c, e)]
mapFrth f = map (\(w, x, y, z) -> (w, x, y, f z))

fourth5 :: (a, b, c, d, e) -> d
fourth5 (_, _, _, x, _) = x

mapMSnd :: (Monad m) => (a -> m b) -> [(c, a)] -> m [(c, b)]
mapMSnd _ [] = return []
mapMSnd f ((x, y) : xys) = do
  y' <- f y
  xys' <- mapMSnd f xys
  return ((x, y') : xys')

dependentMap :: [a] -> ([a] -> a -> b) -> [b]
dependentMap [] _ = []
dependentMap (x : xs) f = f [] x : dependentMap xs (\tl y -> f (x : tl) y)

dependentTrans :: ([b] -> a -> b) -> [a] -> [b]
dependentTrans f = reverse . foldl (\ys x -> f ys x : ys) []

-- | @dependentFlatTr deps f [x_1,...,x_n] = ++_{1 ≤ i ≤ n} f deps_i x_i@
-- where @deps_0 := deps@ and @deps_i := deps_{i-1} ++ f deps_{i-1} x_{i-1}@
dependentFlatTr :: [b] -> ([b] -> a -> [b]) -> [a] -> [b]
dependentFlatTr _ _ [] = []
dependentFlatTr deps f (x : xs) = xT ++ dependentFlatTr (deps ++ xT) f xs
  where
    xT = f deps x

dependentFlatTr2 :: ([b], [c]) -> (([b], [c]) -> a -> ([b], [c])) -> [a] -> ([b], [c])
dependentFlatTr2 (_, cs) _ [] = ([], cs)
dependentFlatTr2 (deps, cs) f (x : xs) = (xT ++ xsT, cs'')
  where
    (xT, cs') = f (deps, cs) x
    (xsT, cs'') = dependentFlatTr2 (deps ++ xT, cs ++ cs') f xs

-- | Same as 'dependentFlatTr' with @deps_0 := []@
dependentFlatTrans :: ([b] -> a -> [b]) -> [a] -> [b]
dependentFlatTrans = dependentFlatTr []

dependentFlatM :: [a] -> [a] -> ([a] -> a -> [b]) -> [b]
dependentFlatM _ [] _ = []
dependentFlatM deps (x : xs) f = f deps x ++ dependentFlatM (deps ++ [x]) xs f

dependentFlatMap :: [a] -> ([a] -> a -> [b]) -> [b]
dependentFlatMap = dependentFlatM []

dependentMapCtx :: c -> (c -> [b] -> c) -> [a] -> (c -> a -> b) -> [b]
dependentMapCtx ctx appCtx xs trans = dependentTrans (trans . appCtx ctx) xs

dependentTransArgs :: c -> (c -> [(Id, a)] -> c) -> [(Id, a)] -> (c -> a -> b) -> [(Id, b)]
dependentTransArgs ctx appCtx xs trans = dependentMap xs (trans' . appCtx ctx)
  where
    trans' ctx' (x, tp) = (x, trans ctx' tp)

dependentMapArgs :: c -> (c -> [(Id, b)] -> c) -> [(Id, a)] -> (c -> a -> b) -> [(Id, b)]
dependentMapArgs ctx appCtx xs trans = dependentMapCtx ctx appCtx xs trans'
  where
    trans' ctx' (x, tp) = (x, trans ctx' tp)

class (Show a, Show b, Eq b) => Suable a b where
  -- | Substitutes the first argument for the second in the third
  sub :: Id -> b -> a -> a

  showSub :: a -> Id -> b -> String
  showSub t x tm = show t ++ "[" ++ show tm ++ "/" ++ x ++ "]"
  subst :: [(Id, b)] -> a -> a
  subst [] e = e
  subst ((x, tm) : subs) e = subst subs $ sub x tm e

data TermPattern a where
  IdPat :: Id -> TermPattern a
  TermPat :: a -> TermPattern a
  AppPat :: TermPattern a -> [TermPattern a] -> TermPattern a
  AnyPat :: TermPattern a

type SubtermPattern a = (TermPattern a, Bool)

instance (Show a) => Show (TermPattern a) where
  show (IdPat x) = x
  show (TermPat tm) = show tm
  show (AppPat f ts) = unwords $ map show (f : ts)
  show AnyPat = "*"

transTPat :: (a -> b) -> TermPattern a -> TermPattern b
transTPat f p = case p of
  IdPat x -> IdPat x
  AnyPat -> AnyPat
  TermPat tm -> TermPat $ f tm
  AppPat g ts -> AppPat (transTPat f g) $ map (transTPat f) ts

transPat :: (a -> b) -> SubtermPattern a -> SubtermPattern b
transPat f = B.first (transTPat f)

-- ToDo: Think about whether we can implement this in terms of Data's gfold

-- | used to find and replace recursive calls into induction hypotheses
class (Suable a b) => AppSuable a b where
  {-@ findAndReplace pat:SubtermPattern b -> expr:a -> {v:([b], Maybe (b -> a)) | null (fst v) <-> snd v == Nothing} @-}
  findAndReplace :: SubtermPattern b -> a -> ([b], Maybe (b -> a))
  findSubterm :: SubtermPattern b -> a -> [b]
  findSubterm pat expr = fst $ findAndReplace pat expr
  hasMatch :: SubtermPattern b -> a -> Bool
  hasMatch pat expr = not . null $ findSubterm pat expr
  matchesAny :: a -> [SubtermPattern b] -> Bool
  matchesAny expr = any (`hasMatch` expr)
  replaceSubterm :: SubtermPattern b -> b -> a -> a
  replaceSubterm pat repl expr = {-(\res -> trace (unwords ["replaceSubterm", show pat, show repl, show expr, "yielding", show res]) res) $ -} case findAndReplace pat expr of
    ([], _) -> expr
    (_, Just replExpr) -> replExpr repl
    (_, Nothing) -> error "IMPOSSIBLE"
  replaceSubterms :: [(SubtermPattern b, b)] -> a -> a
  replaceSubterms ((pat, repl) : repls) = replaceSubterms repls . replaceSubterm pat repl
  replaceSubterms [] = id
  replaceApp :: Id -> [b] -> b -> a -> a
  replaceApp x bs = replaceSubterm (AppPat (IdPat x) $ map TermPat bs, True)

  recurseFindAndRepl :: (AppSuable c b) => SubtermPattern b -> (c -> a) -> c -> ([b], Maybe (b -> a))
  recurseFindAndRepl pat constr arg = resRec matches func
    where
      matches = findSubterm pat arg
      func r = constr (replaceSubterm pat r arg)
  unchanged :: ([b], Maybe (b -> a))
  unchanged = ([], Nothing)

  recurseFindAndRepls :: (AppSuable c b) => SubtermPattern b -> ([c] -> a) -> [c] -> ([b], Maybe (b -> a))
  recurseFindAndRepls pat expr [] = findAndReplace pat (expr [])
  recurseFindAndRepls pat constr args = resRec matches func
    where
      matches = concatMap (findSubterm pat) args
      func r = constr $ map (replaceSubterm pat r) args

  recurseFindAndRepls2 :: (AppSuable c b, AppSuable d b) => SubtermPattern b -> ([c] -> [d] -> a) -> [c] -> [d] -> ([b], Maybe (b -> a))
  recurseFindAndRepls2 pat expr [] [] = findAndReplace pat (expr [] [])
  recurseFindAndRepls2 pat constr args args' = resRec matches func
    where
      matches = concatMap (findSubterm pat) args ++ concatMap (findSubterm pat) args'
      func r = constr (map (replaceSubterm pat r) args) (map (replaceSubterm pat r) args')

  recurseFindAndReplFuncBind :: (AppSuable b b, AppSuable c b, AppSuable t b) => SubtermPattern b -> ([t] -> c -> a) -> [t] -> c -> ([b], Maybe (b -> a))
  recurseFindAndReplFuncBind pat constr args ret = resRec (argsMatches ++ retMatches) func
    where
      argsMatches = concatMap (findSubterm pat) args
      retMatches = findSubterm pat ret
      func r = constr (map (replaceSubterm pat r) args) (replaceSubterm pat r ret)

  recurseFindAndRepl2 :: (AppSuable c b, AppSuable d b) => SubtermPattern b -> (c -> d -> a) -> c -> d -> ([b], Maybe (b -> a))
  recurseFindAndRepl2 pat constr x y = {-trace (unwords ["recurseFindAndRepl2", show pat, "...", show x, show y]) $-} resRec matches func
    where
      matches = findSubterm pat x ++ findSubterm pat y
      func r = constr (replaceSubterm pat r x) (replaceSubterm pat r y)

  recurseFindAndRepl3 :: (AppSuable c b, AppSuable d b, AppSuable e b) => SubtermPattern b -> (c -> d -> e -> a) -> c -> d -> e -> ([b], Maybe (b -> a))
  recurseFindAndRepl3 pat constr x y z = resRec matches func
    where
      matches = findSubterm pat x ++ findSubterm pat y ++ findSubterm pat z
      func r = constr (replaceSubterm pat r x) (replaceSubterm pat r y) (replaceSubterm pat r z)

  recurseFindAndRepl4 :: (AppSuable c b, AppSuable d b, AppSuable e b, AppSuable f b) => SubtermPattern b -> (c -> d -> e -> f -> a) -> c -> d -> e -> f -> ([b], Maybe (b -> a))
  recurseFindAndRepl4 pat constr w x y z = resRec matches func
    where
      matches = findSubterm pat w ++ findSubterm pat x ++ findSubterm pat y ++ findSubterm pat z
      func r = constr (replaceSubterm pat r w) (replaceSubterm pat r x) (replaceSubterm pat r y) (replaceSubterm pat r z)

  recurseFindAndReplApp' :: (AppSuable b b) => SubtermPattern b -> (b -> [b] -> a) -> b -> [b] -> (b -> [b] -> b) -> ([b], Maybe (b -> a))
  recurseFindAndReplApp' pat ap f ts app =
    if not (isApplOf pat f)
      then resRec matches func
      else case pat of
        (AppPat _ tPs, ca) -> if length ts >= length tPs && and (zipWith (\p t -> hasMatch (p, ca) t) tPs initialTs) then (initMatch : otherMatches, Just replTm) else ([], Nothing)
          where
            initMatch = app f initialTs
            otherMatches = concatMap (findSubterm pat) remainingTs
            (initialTs, remainingTs) = splitAt (length tPs) ts
            replTm t = replaceSubterm pat t (ap t remainingTs)
        _ -> recurseFindAndReplFuncBind pat (flip ap) ts f
    where
      matches = findSubterm pat f ++ concatMap (findSubterm pat) ts
      func r = ap (replaceSubterm pat r f) (map (replaceSubterm pat r) ts)

transFindAndRepl :: (AppSuable a c) => SubtermPattern b -> a -> (b -> c) -> ([c], Maybe (c -> a))
transFindAndRepl p t f = resRec ms (fromJust funcO)
  where
    p' = transPat f p
    (ms, funcO) = findAndReplace p' t

recurseFindAndReplApp :: (AppSuable b b) => SubtermPattern b -> (b -> [b] -> b) -> b -> [b] -> ([b], Maybe (b -> b))
recurseFindAndReplApp pat ap f ts = case fst pat of
  AnyPat -> ([ap f ts], Just id)
  _ -> recurseFindAndReplApp' pat ap f ts ap

isApplOf :: (AppSuable b b) => SubtermPattern b -> b -> Bool
isApplOf pat x = case fst pat of
  TermPat y -> x == y
  IdPat y -> show x == y
  AppPat y _ -> isApplOf (y, snd pat) x
  AnyPat -> False

isSubstOf pat x = case fst pat of
  IdPat y -> x == y
  _ -> False

resRec :: [b] -> (b -> a) -> ([b], Maybe (b -> a))
resRec matches func = (matches, if null matches then Nothing else Just func)

ifNotFullMatch :: (AppSuable a a, Eq a) => SubtermPattern a -> a -> ([a], Maybe (a -> a)) -> ([a], Maybe (a -> a))
ifNotFullMatch p tm def = {- (if length (show tm) > 20 && length (show p) > 20 then trace (unwords ["ifNotFullMatch", show p, show tm]) else id) $ -} case fst p of
  IdPat f | show tm == f -> resRec [tm] id
  AnyPat -> resRec [tm] id
  TermPat tm' | tm == tm' -> resRec [tm] id
  _ -> def

class Binder a where
  bindName :: a -> Id

-- | traces a function call with arguments and result for debugging purpuses
traceFuncRet :: (Show a) => [String] -> a -> a
traceFuncRet fargs res = trace (unwords (fargs ++ ["\nyields", show res, "\n"])) res
