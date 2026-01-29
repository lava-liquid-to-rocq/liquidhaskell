-- | Miscellaneous LH-related functions
module Lava.Misc
  ( isIgnoredBind,
    stripLegalName,
    isBuiltinDatatype,
  )
where

import Data.List (intercalate)
import GHC.Core
import Lava.Util (showStripped, split, strip)

-- | tests whether an GHC bind starts with '$' or '?' and should thus not be translated
isIgnoredBind :: (Show b) => Bind b -> Bool
isIgnoredBind bind = name `startsWith` '$' || name == "?"
  where
    name = case bind of
      NonRec b _ -> showStripped b
      Rec ((b, _) : _) -> showStripped b
      Rec [] -> "?"
    startsWith xs c = c == head xs

-- | Remove character from LH names that are illegal in names for the translation
removeIllegalCharacters :: String -> String
removeIllegalCharacters = filter (not . (`elem` illegalChars))

illegalChars :: [Char]
illegalChars = ['$', '#']

-- | Remove illegal characters from LH names and strip their qualifications, unless this produces a built-in name
stripLegalName :: String -> String -> String
stripLegalName moduleId s = removeIllegalCharacters $ if strip s `elem` illegalNames then prefixedS else strip s
  where
    prefS = split '.' s
    -- \| Unfortunately Coq doesn't let us use "." prefixes in names, so we use "__" instead
    prefixedS = if length prefS > 1 then intercalate "__" . drop (length prefS - 2) $ prefS else stripLegalName "" (moduleId ++ "." ++ s) -- error $ "clashing:" ++ s

illegalNames = ["Z", "N", "sub"]

-- | Whether a String is a built-in datatype
isBuiltinDatatype :: String -> Bool
isBuiltinDatatype tc = tc == "[]" || isTuple tc
  where
    isTuple ('(' : ',' : s) = isTuple' s
    isTuple _ = False
    isTuple' (',' : s) = isTuple' s
    isTuple' [')'] = True
    isTuple' _ = False
