{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedLists #-}

import qualified Data.Map as M
import Data.Char (chr, ord)
import Data.List
import Data.Foldable
import Data.Monoid
import qualified Seq
import Seq (Seq, pattern (:<), pattern (:>), pattern Empty)

data Signed a = Pos a | Neg a
              deriving (Show, Eq, Ord)

showSignedGen :: Signed Generator -> Char
showSignedGen (Pos (Gen i)) = ['a'..] !! i
showSignedGen (Neg (Gen i)) = ['A'..] !! i

showPath = map showSignedGen

negateS :: Signed a -> Signed a
negateS (Pos a) = Neg a
negateS (Neg a) = Pos a

newtype Generator = Gen Int
                  deriving (Show, Eq, Ord)

type Path = Seq (Signed Generator)
type Relator = Path

isIdentity :: Relator -> Path -> Bool
isIdentity rel path = undefined

equals :: Relator -> Path -> Path -> Bool
equals rel a b = isIdentity rel $ a <> negatePath b

collapse' :: Path -> Maybe Path
collapse' (Neg i :< Pos j :< rest) | i == j = Just rest
collapse' (Pos i :< Neg j :< rest) | i == j = Just rest
collapse' _                                 = Nothing

collapse :: Path -> Path
collapse (x :< rest)
  | Just rest' <- collapse' rest = collapse (x :< rest')
collapse (x :< rest)             = x :< collapse rest
collapse Empty                   = Empty

data Cursor a = Cursor (Seq a) (Seq a)

atLeft :: Seq a -> Cursor a
atLeft = Cursor Empty

toSeq :: Cursor a -> Seq a
toSeq (Cursor l r) = l <> r

moveLeft :: Cursor a -> Maybe (Cursor a)
moveLeft (Cursor _ Empty)      = Nothing
moveLeft (Cursor ls (r :< rs)) = Just $ Cursor (ls :> r) rs

substitute :: Substs -> Path -> Maybe Path
substitute (Substs substLen subs) = go mempty
  where
    go :: Path -> Path -> Maybe Path
    go accum path
      | Just sub <- M.lookup (Seq.take substLen path) subs
      = Just $ accum <> sub <> Seq.drop substLen path

    go accum (g :< path) = go (accum <> [g]) path
    go _     []          = Nothing

data Substs = Substs Int (M.Map Path Path)
            deriving (Show)

-- | Produce all of the tails of a path
pathTails :: Path -> [Path]
pathTails path =
    take n $ map (Seq.take n) $ toList
    $ Seq.tails $ fold $ Seq.replicate 2 path
  where n = Seq.length path

substitutions :: Path -> Substs
substitutions rel = Substs substLen (M.fromList substs)
  where
    n = Seq.length rel
    substLen = (n `div` 2) + 1
    pairs = map (Seq.splitAt substLen) $ pathTails rel
    substs = pairs
          ++ map (\(a,b) -> (negatePath a, b)) pairs
          ++ map (\(a,b) -> (a, negatePath b)) pairs

negatePath :: Path -> Path
negatePath = Seq.reverse . fmap negateS

----- Testing

testPath = head $ drop 1 $ pathTails testRelator
  where p = Pos
        n = Neg

testRelator = [ p a, p b, n a, n b
              , p c, p d, n c, n d ]
  where p = Pos
        n = Neg

[a,b,c,d] = map Gen [0,1,2,3]
