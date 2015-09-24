{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Cursor where

import Control.Monad ((<=<))
import Data.Monoid
import Seq (Seq, pattern (:<), pattern (:>), pattern Empty)
import qualified Seq

-- | A pointer to a position in a non-empty sequence
data Cursor a = Cursor { left :: !(Seq a)
                       , here :: !a
                       , right :: !(Seq a)
                       }

atLeft, atRight :: Seq a -> Maybe (Cursor a)
atLeft  (x :< xs) = Just $ Cursor Empty x xs
atLeft  _         = Nothing
atRight (xs :> x) = Just $ Cursor xs    x Empty
atRight _         = Nothing

toSeq :: Cursor a -> Seq a
toSeq (Cursor l x r) = l <> Seq.singleton x <> r

moveR :: Cursor a -> Maybe (Cursor a)
moveR (Cursor _  _ Empty)     = Nothing
moveR (Cursor ls x (r :< rs)) = Just $ Cursor (ls :> x) r rs

moveL :: Cursor a -> Maybe (Cursor a)
moveL (Cursor Empty     _ _)  = Nothing
moveL (Cursor (l :< ls) x rs) = Just $ Cursor ls x (x :< rs)

-- | Delete the current element and shift right if possible, left if not
delete :: Cursor a -> Maybe (Cursor a)
delete (Cursor ls        _ (x :< rs)) = Just $ Cursor ls x rs
delete (Cursor (ls :> x) _ rs       ) = Just $ Cursor ls x rs
delete _                              = Nothing

-- | Eliminate adjacent pairs of elements which satisfy
-- the given predicate.
collapseCursor :: forall a. (a -> a -> Bool) -> Seq a -> Seq a
collapseCursor eq =
    maybe mempty toSeq . (lookRight <=< atLeft)
  where
    lookRight :: Cursor a -> Maybe (Cursor a)
    lookRight c@(Cursor ls x (r :< rs)) | x `eq` r =
       case rs of
         x' :< rs' -> lookLeft (Cursor ls x' rs')
         Empty
           | ls' :> l <- ls -> pure (Cursor ls' l Empty)
           | otherwise      -> Nothing

    lookRight c@(Cursor _ _ Empty) = pure c
    lookRight c = moveR c >>= lookRight

    lookLeft :: Cursor a -> Maybe (Cursor a)
    lookLeft c@(Cursor (ls :> l) x rs) | l `eq` x =
      case ls of
        ls' :> x' -> lookRight (Cursor ls' x' rs)
        Empty     -> Nothing
    lookLeft c = lookRight c
