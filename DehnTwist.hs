{-# LANGUAGE DeriveFunctor #-}

import Data.Foldable
import Data.Monoid
import Data.List

data Generator = Around Int  -- ^ Around the circumference of hole @i@
               | Through Int -- ^ Through the hole of torus @i@
               deriving (Eq, Ord, Show)

data Homology = Homology { genus :: Int,
                           A :: [Int],
                           B :: [Int] }
  deriving (Show)
  
type HomologyPath = HomologyPath [Homology]
  
homologyDotProduct :: Homology -> Homology -> Int
homologyDotProduct h1 h2 = go ((genus h1) - 1) 0
  where
    go :: Int -> Int -> Int
    go 0 acc = acc + ((A h1)!!0)*((B h2)!!0) - ((A h2)!!0)*((B h1)!!0)
    go n acc = go (n - 1) (acc + ((A h1)!!n)*((B h2)!!n) - ((A h2)!!n)*((B h1)!!n))

homologyAdd :: Homology -> Homology -> Homology
homologyAdd h1 h2 = Homology (genus h1) (zipWith + (A h1) (A h2)) (zipWith + (B h1) (B h2))

homologyMultiply :: Homology -> Int -> Homology
homologyMultiply h1 r = Homology (genus h1) (map (* r) (A h1)) (map (* r) (B h1))

homologyDehnTwist :: Homology -> Homology -> Homology
homologyDehnTwist twist path = (homologyAdd path (homologyMultiply twist (homologyDotProduct twist path)))

homologyDehnTwistSequence :: HomologyPath -> Homology -> Homology
homologyDehnTwistSequence [] h1 = h1
homologyDehnTwistSequence [] (x:xs) h1 = homologyDehnTwistSequence xs (homologyDehnTwist x h1)

homologySingle Int -> Int -> Int -> Homology
homologySingle homChoice homIndex genus 
  | (homChoice == 0) = Homology genus (replicate homIndex 0)++[1]++(replicate (genus-homIndex-1)) (replicate genus 0)
  | (homChoice == 1) = Homology genus (replicate genus 0) (replicate homIndex 0)++[1]++(replicate (genus-homIndex-1))

findNonZeroIntersection :: Homology -> Maybe Homology
findNonZeroIntersection h1 homChoice = go homChoice 0
  where
    go :: Int -> Maybe Int
    go count
      | (count ==(genus h1)) 
        = Nothing
      | (Not ((homologyDotProduct (homologySingle 0 count (genus h1)) h1) == 0)
        = Just (homologySingle 0 count (genus h1))
      | (Not ((homologyDotProduct (homologySingle 1 count (genus h1)) h1) == 0)
        = Just (homologySingle 1 count (genus h1))
      | otherwise 
        = go homChoice (count + 1)

calculateSignature :: HomologyPath -> Int
calculateSignature p1 = 

data Path = Path { unPath :: RawPath}
  deriving (Eq, Show)
instance Monoid Path where
  mempty = Path []
  Path a `mappend` Path b = Path (a `mappend` b)

type PathList = [Path]

type RawPath = [Signed Generator]

type RelationPairList = [PathList]

showGenerator :: Generator -> String
showGenerator (Around i) = "a" ++ (show i)
showGenerator (Through i) = "b" ++ (show i)

showSignedGenerator :: (Signed Generator) -> String
showSignedGenerator (Pos g0) = showGenerator g0
showSignedGenerator (Neg g0) = (showGenerator g0) ++ "'"

showPath :: Path -> String
showPath (Path (Pos g0 : rest)) =
  showGenerator g0 ++ " " ++ showPath (Path rest)
showPath (Path (Neg g0 : rest)) =
  showGenerator g0 ++ "' " ++ showPath (Path rest)
showPath (Path []) =
  ""

-- | @dropPrefix prefix list@ is @Just list'@ if @list == prefix++list'@
dropPrefix :: Eq a => [a] -> [a] -> Maybe [a]
dropPrefix [] rest = Just rest
dropPrefix (x:xs) (y:rest)
  | x == y = dropPrefix xs rest
dropPrefix _ _ = Nothing

-- | Put a path into canonical form
canonicalize :: Path -> Path
canonicalize (Path (Pos g0 : Neg g1 : rest))
  | g0 == g1            = canonicalize (Path rest)
canonicalize (Path (Neg g0 : Pos g1 : rest))
  | g0 == g1            = canonicalize (Path rest)
canonicalize (Path (p : rest)) = (Path (p : unPath (canonicalize (Path rest))))
canonicalize (Path []) = (Path [])

data Signed a = Pos a | Neg a
              deriving (Eq, Show, Functor)

-- | Extract the @a@ from a @Signed a@
unSigned :: Signed a -> a
unSigned (Pos a) = a
unSigned (Neg a) = a

test :: Path
test = Path [Pos $ Around 0, Neg $ Around 1, Neg $ Through 0, Pos $ Through 1]

-- | @dehnTwist rot path@ is the Dehn twist of @path@ twisted
-- along path @rot@.
dehnTwist :: Path -> Path -> Path
dehnTwist rot path = foldMap go (unPath path)
  where
    go :: Signed Generator -> Path
    go (Pos gen) | a@(_:_) <- intersection gen rot =
      (fold a) <> (Path [Pos gen])
    go (Neg gen) | a@(_:_) <- intersection gen rot =
      (fold a) <> (Path [Pos gen])
--    Path (Neg gen : concatMap reverse a)
    go gen = (Path [gen])

-- | Do two generators intersect?
intersects :: Generator -> Generator -> Bool
intersects (Around i)  (Through j) | i == j = True
intersects (Through i) (Around j)  | i == j = True
intersects _           _                    = False

-- | @intersection path1 path2@ is @Nothing@ if the given paths
-- do not intersect. If @Just path2'@ then they intersect and
-- @path2'@ starts at one of the generators in @path1@.
intersection :: Generator -> Path -> [Path]
intersection gen = go (Path [])
  where
    go :: Path -> Path -> [Path]
    go (Path (accum)) (Path (x:xs))
      | unSigned x `intersects` gen = (Path (x:xs++reverse accum)) : go (Path (x:accum)) (Path xs)
      | otherwise                   = go (Path (x:accum)) (Path xs)
    go accum (Path [])              = []

genusNRelators :: Int -> Path
genusNRelators n = go n 0
  where
    go :: Int -> Int -> Path
    go n b | (n==b) =
      Path []
    go n b = 
      Path ([Pos (Around b), Pos (Through b), Neg (Around b), Neg (Through b)]) <> go n (b+1)

isEquivalent :: Path -> Path -> Int -> Bool
isEquivalent p1 p2 genus = isIdentity (p1 <> (invert p2)) genus
      
isIdentity :: Path -> Int -> Bool
isIdentity (Path p) genus = go p 0
  where
    go :: RawPath -> Int -> Bool
    go path n | (n == genus*4) = ((cancelInverses path) == [])
    go [] n = True
    go path n = if (simplifiable path genus n)
                  then go (cancelInverses (simplify path genus n)) 0
                  else go path (n + 1)

subList :: Eq a => [a] -> [a] -> Int
subList _ [] = -1
subList as xxs@(x:xs)
  | all (uncurry (==)) $ zip as xxs = 0
  | otherwise                       = 1 + subList as xs

simplify :: RawPath -> Int -> Int -> RawPath
simplify p genus index =
 go (subList (matchCycleByGenus genus index) p) (2*genus + 1) (unPath (invert (Path (replaceCycleByGenus genus index))))
  where
    go :: Int -> Int -> RawPath -> RawPath
    go (-1) length replacement = p
    go index length replacement = (take index p) ++ replacement ++ (drop (index + length) p)

-- | 
cancelInverses :: RawPath -> RawPath
cancelInverses (Pos g0 : Neg g1 : rest)
  | g0 == g1      = cancelInverses rest
cancelInverses (Neg g0 : Pos g1 : rest)
  | g0 == g1      = cancelInverses rest
cancelInverses (p : rest) = (p : cancelInverses rest)
cancelInverses [] = []
                  
simplifiable :: RawPath -> Int -> Int -> Bool
simplifiable p genus index = isInfixOf (matchCycleByGenus genus index) p
                  
matchCycleByGenus :: Int -> Int -> RawPath
matchCycleByGenus genus index = matchCycle (genusNRelators genus) index

replaceCycleByGenus :: Int -> Int -> RawPath
replaceCycleByGenus genus index = replaceCycle (genusNRelators genus) index

matchCycle :: Path -> Int -> RawPath
matchCycle (Path raw) n = (take (ceiling (((fromIntegral (length raw)) + 1) / 2.0)) (drop n (cycle raw)))

replaceCycle :: Path -> Int -> RawPath
replaceCycle (Path raw) n =
   (take (floor (((fromIntegral (length raw)) - 1) / 2.0)) (drop (n + (ceiling (((fromIntegral (length raw)) + 1) / 2.0))) (cycle raw)))

invert :: Path -> Path
invert (Path raw) = (Path (go raw))
  where
    go :: RawPath -> RawPath
    go [] = []
    go (Pos x : rest) = (go rest) ++ [Neg x]
    go (Neg x : rest) = (go rest) ++ [Pos x]     
