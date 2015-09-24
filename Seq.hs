{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Seq
    ( pattern (:<)
    , pattern (:>)
    , pattern Empty
    , module Data.Sequence
    ) where

import Data.Sequence hiding ((:<), (:>))
import qualified Data.Sequence as S

pattern Empty <- (S.viewl -> S.EmptyL) where
  Empty = S.empty
pattern x :< xs <- (S.viewl -> x S.:< xs) where
  x :< xs = x S.<| xs
pattern xs :> x <- (S.viewr -> xs S.:> x) where
  xs :> x = xs S.|> x

infixr 5 :<
infixl 5 :>
