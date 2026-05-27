-- TODO: rename the module

-- | Functions used in the translation from Core and Spec
module Language.Haskell.Liquid.Lava.Misc where

import Data.List (intercalate, stripPrefix, uncons)
import Data.Maybe (fromMaybe)
import GHC.Core
import Lava.Names (rocqReservedNames)

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

-- Get rid of module names.
showStripped :: (Show a) => a -> String
showStripped = strip . show

-- | tests whether an GHC bind starts with '$' or '?' and should thus not be translated
isIgnoredBind :: (Show b) => Bind b -> Bool
isIgnoredBind bind = name `startsWith` '$' || name == "?"
  where
    name = case bind of
      NonRec b _ -> showStripped b
      Rec ((b, _) : _) -> showStripped b
      Rec [] -> "?"
    startsWith xs c = case uncons xs of Just (c', _) -> c' == c; Nothing -> False

-- | Remove character from LH names that are illegal in names for the translation
removeIllegalCharacters :: String -> String
removeIllegalCharacters = filter (not . (`elem` illegalChars))

illegalChars :: [Char]
illegalChars = ['$', '#']

-- | Remove illegal characters from LH names and strip their qualifications, unless this produces a built-in name
stripLegalName :: String -> String -> String
stripLegalName moduleId s = removeIllegalCharacters $ if strip s `elem` rocqReservedNames then prefixedS else strip s
  where
    prefS = split '.' s
    -- \| Unfortunately Coq doesn't let us use "." prefixes in names, so we use "__" instead
    prefixedS = if length prefS > 1 then intercalate "__" . drop (length prefS - 2) $ prefS else stripLegalName "" (moduleId ++ "." ++ s) -- error $ "clashing:" ++ s

-- | Whether a String is a built-in datatype
isBuiltinDatatype :: String -> Bool
isBuiltinDatatype tc = tc == "[]" || tc == "Maybe" || isTuple tc
  where
    isTuple ('(' : ',' : s) = isTuple' s
    isTuple _ = False
    isTuple' (',' : s) = isTuple' s
    isTuple' [')'] = True
    isTuple' _ = False

removeSuffix :: (Eq a) => [a] -> [a] -> [a]
removeSuffix suffix orig = reverse $ removePrefix (reverse suffix) (reverse orig)

removePrefix :: (Eq a) => [a] -> [a] -> [a]
removePrefix prefix orig = fromMaybe orig $ stripPrefix prefix orig
