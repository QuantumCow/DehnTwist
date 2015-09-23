{-# LANGUAGE DeriveFunctor #-}

data Generator = Around Int  -- ^ Around the circumference of hole @i@
               | Through Int -- ^ Through the hole of torus @i@
               deriving (Eq, Ord, Show)

type Path = [Signed Generator]

showGenerator :: Generator -> String
showGenerator (Around i) = (['a'..] !! i) : []
showGenerator (Through i) = (['a'..] !! i) : "'"

-- | @dropPrefix prefix list@ is @Just list'@ if @list == prefix++list'@
dropPrefix :: Eq a => [a] -> [a] -> Maybe [a]
dropPrefix [] rest = Just rest
dropPrefix (x:xs) (y:rest)
  | x == y = dropPrefix xs rest
dropPrefix _ _ = Nothing

-- | Put a path into canonical form
canonicalize :: Path -> Path
canonicalize (Pos g0 : Neg g1 : rest)
  | g0 == g1            = canonicalize rest
canonicalize (Neg g0 : Pos g1 : rest)
  | g0 == g1            = canonicalize rest
canonicalize (p : rest) = p : canonicalize rest
canonicalize [] = []

data Signed a = Pos a | Neg a
              deriving (Show, Functor)

-- | Extract the @a@ from a @Signed a@
unSigned :: Signed a -> a
unSigned (Pos a) = a
unSigned (Neg a) = a

test :: Path
test = [Pos $ Around 0, Neg $ Around 1, Neg $ Through 0, Pos $ Through 1]

-- | @dehnTwist rot path@ is the Dehn twist of @path@ twisted
-- along path @rot@.
dehnTwist :: Path -> Path -> Path
dehnTwist rot path = concatMap go path
  where
    go :: Signed Generator -> Path
    go (Pos gen) | a@(_:_) <- intersection gen rot =
      concat a ++ [Pos gen]
    go (Neg gen) | a@(_:_) <- intersection gen rot =
      Neg gen : concatMap reverse a
    go gen = [gen]

-- | Do two generators intersect?
intersects :: Generator -> Generator -> Bool
intersects (Around i)  (Through j) | i == j = True
intersects (Through i) (Around j)  | i == j = True
intersects _           _                    = False

-- | @intersection path1 path2@ is @Nothing@ if the given paths
-- do not intersect. If @Just path2'@ then they intersect and
-- @path2'@ starts at one of the generators in @path1@.
intersection :: Generator -> Path -> [Path]
intersection gen = go []
  where
    go :: Path -> Path -> [Path]
    go accum (x:xs)
      | unSigned x `intersects` gen = (x:xs++reverse accum) : go (x:accum) xs
      | otherwise                   = go (x:accum) xs
    go accum []                     = []

genusNRelators :: Int -> Path
genusNRelators n = go n 0
  where
    go :: Int -> Int -> Path
    go n b | (n==b) =
      []
    go n b =
      concat [[(Pos (Around b)) (Pos (Through b)) (Neg (Around b)) (Neg (Around b))] (go n b+1)]