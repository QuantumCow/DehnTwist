{-# LANGUAGE DeriveFunctor #-}

import Data.Foldable
import Data.Monoid
import Data.List
import Data.Ratio
import Data.Maybe
import Debug.Trace

tr :: Show a => a -> a
tr x = traceShow x x

data Generator = Around Int  -- ^ Around the circumference of hole @i@
               | Through Int -- ^ Through the hole of torus @i@
               deriving (Eq, Ord, Show)

isAround :: Generator -> Bool
isAround (Around x) = True
isAround (Through x) = False

isThrough :: Generator -> Bool
isThrough (Around x) = False
isThrough (Through x) = True

stripGenerator :: Generator -> Int
stripGenerator (Around x) = x
stripGenerator (Through x) = x

data Homology' a = Homology { aLoop :: [a]
                            , bLoop :: [a]
                            } deriving (Eq, Show)

instance Functor Homology' where
  fmap f (Homology a b) = Homology (map f a) (map f b)

type Homology = Homology' Integer
type RationalHomology = Homology' Rational
type HomologyPath' a = [Homology' a]
type HomologyPath = HomologyPath' Integer
type RationalHomologyPath = HomologyPath' Rational

genus :: Homology' a -> Int
genus h1 = length (aLoop h1)

rationalize :: Homology -> RationalHomology
rationalize = mapHom toRational

toIntegerHomology :: RationalHomology -> Homology
toIntegerHomology rh = mapHom (floor . ((toRational mult) *)) rh
    where
      mult = rationalHomologyLCM rh

rationalHomologyLCM :: RationalHomology -> Integer
rationalHomologyLCM rh = foldl lcm 1 (map denominator ((aLoop rh) ++ (bLoop rh)))

nonZero :: [Integer] -> [Integer]
nonZero = filter (/= 0)

homologyLCM :: Homology -> Integer
homologyLCM h1 = foldl lcm 1 (nonZero ((aLoop h1) ++ (bLoop h1)))

homologyPrint :: Homology -> String
homologyPrint h1 = go (aLoop h1) (bLoop h1) 0
  where
    go :: [Integer] -> [Integer] -> Integer -> String
    go [] [] count  = ""
    go (x:xs) (y:ys) count = (if x /= 0 then ((show x) ++ "a" ++ (show count) ++ "+") else "") ++
                             (if y /= 0 then ((show y) ++ "b" ++ (show count) ++ "+") else "") ++
                              go xs ys (count + 1)

homologyPathPrint :: HomologyPath -> String
homologyPathPrint = intercalate ", " . map homologyPrint

homologyDotProduct :: Num a => Homology' a -> Homology' a -> a
homologyDotProduct h1 h2 =
  sum (zipWith (*) (aLoop h1) (bLoop h2)) - sum (zipWith (*) (aLoop h2) (bLoop h1))

zipHom :: (a -> b -> c) -> Homology' a -> Homology' b -> Homology' c
zipHom f (Homology a1 b1) (Homology a2 b2) = Homology (zipWith f a1 a2) (zipWith f b1 b2)

mapHom :: (a -> b) -> Homology' a -> Homology' b
mapHom f (Homology a b) = Homology (map f a) (map f b)

homologyAdd :: Num a => Homology' a -> Homology' a -> Homology' a
homologyAdd = zipHom (+)

homologySubtract :: Num a => Homology' a -> Homology' a -> Homology' a
homologySubtract = zipHom (-)

homologyMultiply :: Num a => Homology' a -> a -> Homology' a
homologyMultiply h1 r = mapHom (* r) h1

homologyDivide :: Integral a => Homology' a -> a -> Homology' a
homologyDivide h1 r = mapHom (`div` r) h1

homologyDehnTwist :: Num a => Homology' a -> Homology' a -> Homology' a
homologyDehnTwist twist path =
  path `homologyAdd` (twist `homologyMultiply` homologyDotProduct twist path)

homologyDehnTwistSequence :: HomologyPath -> Homology -> Homology
homologyDehnTwistSequence [] h1 = h1
homologyDehnTwistSequence (x:xs) h1 = homologyDehnTwistSequence xs (homologyDehnTwist x h1)

homologySingle :: Generator -> Int -> Homology
homologySingle (Around homIndex) genus
   = Homology ((replicate homIndex 0) ++ [1] ++ (replicate (genus-homIndex-1) 0)) (replicate genus 0)
homologySingle (Through homIndex) genus
   = Homology (replicate genus 0) ((replicate homIndex 0) ++ [1] ++ (replicate (genus-homIndex-1) 0))

homologyNegate :: Homology -> Homology
homologyNegate = mapHom negate

euc :: (Integral a) => a -> a -> (a, a)
euc a b = case b of
            1 -> (0, 1)
            _ -> let (e, f) = euc b d
                 in (f, e - c*f)
  where c = a `div` b
        d = a `mod` b

-- | This will return a homology which is a simple closed curve
-- the original homology will be some multiple of this
homologySCC :: Homology -> Homology
homologySCC h1
    | (testZeroHomology h1) = h1
    | otherwise             = homologyDivide h1 (tr (homologyLCM (tr h1)))

-- | This will return true if the homology represents a simple closed curve
isSCC :: Homology -> Bool
isSCC h1 = ((homologyLCM h1) == 1)

generateAllHomologyPairs :: Int -> [HomologyPath]
generateAllHomologyPairs g = go (generateAllHomologies g) []
  where
    go :: HomologyPath ->  [HomologyPath] -> [HomologyPath]
    go [] acc = acc
    go (x:y:rest) acc = go rest (acc ++ [[x, y]])

generateRemainingBasis :: Homology -> [HomologyPath]
generateRemainingBasis h1A = go [[h1A, (fromJust (homologyComplement h1A))]] (generateAllHomologyPairs g)
  where
    g = (genus h1A)
    go :: [HomologyPath] -> [HomologyPath] -> [HomologyPath]
    go hAcc [] = hAcc
    go hAcc (x:rest)
      | (length hAcc) == g
        = hAcc
      | otherwise
        = if (nextPair == []) then (go hAcc rest) else (go (hAcc ++ [nextPair]) rest)
            where
               nextPair = (nextBasisPair x hAcc)

nextBasisPair :: HomologyPath -> [HomologyPath] -> HomologyPath
nextBasisPair [h1A, h1B] hAcc = go h1A h1B hAcc
  where
    go :: Homology -> Homology -> [HomologyPath] -> HomologyPath
    go h2A h2B [] = if (not ((testZeroHomology h2A) || (testZeroHomology h2B))) then [h2A, h2B] else []
    go h2A h2B (x:xs) = go (homologySCC (subtractOutAcc h2A x)) (homologySCC (subtractOutAcc h2B x)) xs

subtractOutAcc :: Homology -> HomologyPath -> Homology
subtractOutAcc h1 [h1A, h1B] = homologyAdd (homologySubtract h1 (homologyMultiply h1A (homologyDotProduct h1 h1B)))
                                           (homologyMultiply h1B (homologyDotProduct h1 h1A))


-- | This will return a homology b such that a . b = 1
homologyComplement :: Homology -> Maybe Homology
homologyComplement h1
    | not (unit == Nothing)
      = Just (unitHomologyComplement (fromJust unit) g)
    | not ((mGen == Nothing) || (nGen == Nothing))
      = Just (primeHomologyComplement h1 (fromJust mGen) (fromJust nGen))
    | otherwise
      = Nothing
    where
      g = genus h1
      unit = findUnit h1
      mGen = findNonZero h1
      nGen = findRelPrime h1 (fromJust mGen)

-- | This will return a homology represented by two generators
doubleHomology :: Int -> Integer -> Generator -> Integer -> Generator -> Homology
doubleHomology g a (Around x) b (Around y)
  | x < y
   = Homology ((replicate x 0) ++ [a] ++ (replicate (y - x - 1) 0) ++ [b] ++ (replicate (g - y - 1) 0))
              (replicate g 0)
   | otherwise
   = Homology ((replicate y 0) ++ [b] ++ (replicate (x - y - 1) 0) ++ [a] ++ (replicate (g - x - 1) 0))
              (replicate g 0)
doubleHomology g a (Around x) b (Through y)
   = Homology ((replicate x 0) ++ [a] ++ (replicate (g - x - 1) 0))
              ((replicate y 0) ++ [b] ++ (replicate (g - y - 1) 0))
doubleHomology g a (Through x) b (Through y)
    | x < y
   = Homology (replicate g 0)
              ((replicate x 0) ++ [a] ++ (replicate (y - x - 1) 0) ++ [b] ++ (replicate (g - y - 1) 0))
   | otherwise
   = Homology (replicate g 0)
              ((replicate y 0) ++ [b] ++ (replicate (x - y - 1) 0) ++ [a] ++ (replicate (g - x - 1) 0))
doubleHomology g a (Through x) b (Around y)
   = Homology ((replicate y 0) ++ [b] ++ (replicate (g - y - 1) 0))
              ((replicate x 0) ++ [a] ++ (replicate (g - x - 1) 0))

getHomology :: Homology -> Generator -> Integer
getHomology h1 (Around g1) = (aLoop h1)!!g1
getHomology h1 (Through g1) = (bLoop h1)!!g1

primeHomologyComplement :: Homology -> Generator -> Generator -> Homology
primeHomologyComplement h1 (Around g1) (Around g2)
      = doubleHomology g a (Through g1) b (Through g2)
      where
        (a, b) = (euc ((aLoop h1)!!g1) ((aLoop h1)!!g2))
        g = genus h1
primeHomologyComplement h1 (Around g1) (Through g2)
      = (doubleHomology g a (Through g1) (-b) (Around g2))
      where
        (a, b) = (euc ((aLoop h1)!!g1) ((bLoop h1)!!g2))
        g = genus h1
primeHomologyComplement h1 (Through g1) (Through g2)
      = (doubleHomology g (-a) (Around g1) (-b) (Around g2))
      where
        (a, b) = (euc ((bLoop h1)!!g1) ((bLoop h1)!!g2))
        g = genus h1
primeHomologyComplement h1 (Through g1) (Around g2)
      = (doubleHomology g (-a) (Around g1) b (Through g2))
      where
        (a, b) = (euc ((bLoop h1)!!g1) ((aLoop h1)!!g2))
        g = genus h1


unitHomologyComplement :: Signed Generator -> Int -> Homology
unitHomologyComplement (Pos (Around x)) g = homologySingle (Through x) g
unitHomologyComplement (Pos (Through x)) g = homologyNegate (homologySingle (Around x) g)
unitHomologyComplement (Neg (Around x)) g = homologyNegate (homologySingle (Through x) g)
unitHomologyComplement (Neg (Through x)) g = homologySingle (Around x) g

findNonZero :: Homology -> Maybe Generator
findNonZero h1
    | not (firstA == Nothing)
       = Just (Around (fromJust firstA))
    | not (firstB == Nothing)
       = Just (Through (fromJust firstB))
    | otherwise
       = Nothing
    where
      isNotZero :: Integer -> Bool
      isNotZero n = (not (0 == n))
      firstA = (findIndex (isNotZero) (aLoop h1))
      firstB = (findIndex (isNotZero) (bLoop h1))

findUnit :: Homology -> Maybe (Signed Generator)
findUnit h1
    | not (firstAOne == Nothing)
      = Just (Pos (Around (fromJust firstAOne)))
    | not (firstANegOne == Nothing)
      = Just (Neg (Around (fromJust firstANegOne)))
    | not (firstBOne == Nothing)
      = Just (Pos (Through (fromJust firstBOne)))
    | not (firstBNegOne == Nothing)
      = Just (Neg (Through (fromJust firstBNegOne)))
    | otherwise
      = Nothing
    where
      firstAOne = (elemIndex 1 (aLoop h1))
      firstANegOne = (elemIndex (-1) (aLoop h1))
      firstBOne = (elemIndex 1 (bLoop h1))
      firstBNegOne = (elemIndex (-1) (bLoop h1))

findRelPrime :: Homology -> Generator -> Maybe Generator
findRelPrime h1 g1
    | not (firstAPrime == Nothing)
      = Just (Around (fromJust firstAPrime))
    | not (firstBPrime == Nothing)
      = Just (Through (fromJust firstBPrime))
    | otherwise
      = Nothing
    where
      m = if (isAround g1) then (aLoop h1)!!(stripGenerator g1) else (bLoop h1)!!(stripGenerator g1)
      isRelPrime :: Integer -> Bool
      isRelPrime n = (1 == (gcd m n))
      firstAPrime = (findIndex (isRelPrime) (aLoop h1))
      firstBPrime = (findIndex (isRelPrime) (bLoop h1))

findNonZeroIntersection :: Homology -> Maybe Homology
findNonZeroIntersection h1 = go 0
  where
    go :: Int -> Maybe Homology
    go count
      | (count == (genus h1))
        = Nothing
      | (not ((homologyDotProduct (homologySingle (Around count) (genus h1)) h1) == 0))
        = Just (homologySingle (Around count) (genus h1))
      | (not ((homologyDotProduct (homologySingle (Through count) (genus h1)) h1) == 0))
        = Just (homologySingle (Through count) (genus h1))
      | otherwise
        = go (count + 1)

showMatrix :: [[Rational]] -> [[Rational]]
showMatrix [] = []
showMatrix (x:xs) = traceShow (map numerator x) ([x]++(showMatrix xs))

rref :: Eq a => Fractional a => [[a]] -> [[a]]
rref m = f m 0 [0 .. rows - 1]
  where rows = length m
        cols = length $ head m

        f m _    []              = m
        f m lead (r : rs)
            | indices == Nothing = m
            | otherwise          = f m' (lead' + 1) rs
          where indices = find p l
                p (col, row) = m !! row !! col /= 0
                l = [(col, row) |
                    col <- [lead .. cols - 1],
                    row <- [r .. rows - 1]]

                Just (lead', i) = indices
                newRow = map (/ m !! i !! lead') $ m !! i

                m' = zipWith g [0..] $
                    replace r newRow $
                    replace i (m !! r) m
                g n row
                    | n == r    = row
                    | otherwise = zipWith h newRow row
                  where h = subtract . (* row !! lead')

replace :: Int -> a -> [a] -> [a]
{- Replaces the element at the given index. -}
replace n e l = a ++ e : b
  where (a, _ : b) = splitAt n l

runTest :: Int
runTest = calculateSignature testGenusOne

printHomology :: Homology -> Homology
printHomology h1 = go h1 [aLoop h1, bLoop h1]
  where
    go :: Homology -> [[Integer]] -> Homology
    go h1 [] = h1
    go h1 (x:xs) = traceShow x (go h1 xs)

testZeroHomology :: Homology -> Bool
testZeroHomology h1 = go (aLoop h1) (bLoop h1)
  where
    go :: [Integer] -> [Integer] -> Bool
    go [] [] = True
    go (x:xs) (y:ys)
      | ((x == 0) && (y == 0)) = go xs ys
      | otherwise = False

printAllTests :: [(Integer, Integer)]
printAllTests = (zip [-8, -4, -12, -18, -24, -48, -42] (map (toInteger . calculateSignature) [testGenusOne, matsumoto, matsumotoA, matsumotoB, matsumotoC, fullerA, fullerB]))

runAllTests :: String
runAllTests
  | ((calculateSignature testGenusOne) /= -8) = "Genus One Failed"
  | ((calculateSignature matsumoto) /= -4) = "matsumoto Failed"
  | ((calculateSignature matsumotoA) /= -12) = "matsumotoA Failed"
  | ((calculateSignature matsumotoB) /= -18) = "matsumotoB Failed"
  | ((calculateSignature matsumotoC) /= -24) = "matsumotoC Failed"
  | ((calculateSignature fullerA) /= -48) = "fullerA Failed"
  | ((calculateSignature fullerB) /= -42) = "fullerB Failed"


testGenusOne :: HomologyPath
testGenusOne = lefschetzFibration [(homologySingle (Around 0) 1), (homologySingle (Through 0) 1)] [0, 1] 6

matsumoto :: HomologyPath
matsumoto = lefschetzFibration (go 0) [0, 1, 2, 3] 2
  where
    go :: Integer-> HomologyPath
    go 0 = [Homology [1, 1] [0, 0]] ++ go 1
    go 1 = [Homology [0, 0] [0, 0]] ++ go 2
    go 2 = [Homology [0, 0] [-1, -1]] ++ go 3
    go 3 = [Homology [1, 1] [-1, -1]]

matsumotoPath :: Int -> Int -> Homology
matsumotoPath index genus
    | (band == 0) = Homology (replicate genus 1) (replicate genus 0)
    | ((odd genus) && (index == a)) = Homology
            (replicate genus 0)
            ((replicate (div genus 2) 0) ++ [1] ++ (replicate (div genus 2) 0))
    | ((odd genus) && (index == b)) = Homology
            (replicate genus 0)
            ((replicate (div genus 2) 0) ++ [-1] ++ (replicate (div genus 2) 0))
    | ((odd genus) && (index == genus)) = Homology
            (replicate genus 0)
            ((replicate (div genus 2) 0) ++ [-2] ++ (replicate (div genus 2) 0))
    | ((even genus) && (index == c)) = Homology (replicate genus 0) (replicate genus 1)
    | (index < maxIndex) = Homology
            ((replicate (hole - 1) 0) ++ (replicate (genus - (2*(hole - 1))) 1) ++ (replicate (hole - 1) 0))
            ((replicate (band - 1) 0) ++ [-1] ++ (replicate (genus - (2*band)) 0) ++ [-1] ++ (replicate (band -1) 0))
    where
      hole = (div index 2) + 1
      band = (div (index + 1) 2)
      c = genus + 1
      a = genus + 1
      b = genus + 2
      maxIndex = if (even genus) then c else b

genusNMatsumoto :: Int -> HomologyPath
genusNMatsumoto genus
    | (even genus) = lefschetzFibration paths [0 .. c] 2
    | (odd genus) = lefschetzFibration paths ([0 .. a] ++ [a, b, b]) 2
    where
      c = genus + 1
      a = genus + 1
      b = genus + 2
      maxIndex = if (even genus) then c else b
      paths = concatMap (\x -> [(matsumotoPath x genus)]) [0 .. maxIndex]

testNotGenusOne :: HomologyPath
testNotGenusOne = lefschetzFibration [(homologySingle (Around 0) 1), (homologySingle (Through 0) 1)] [0, 1] 1

matsumotoA :: HomologyPath
matsumotoA = lefschetzFibration genusTwoGenerators [0, 1, 2, 3, 4, 4, 3, 2, 1, 0] 2

matsumotoB :: HomologyPath
matsumotoB = lefschetzFibration genusTwoGenerators [0, 1, 2, 3, 4] 6

matsumotoC :: HomologyPath
matsumotoC = lefschetzFibration genusTwoGenerators [0, 1, 2, 3] 10

genusTwoGenerators :: HomologyPath
genusTwoGenerators = [(Homology [0, 0] [-1, 0]),
                      (Homology [1, 0] [0, 0]),
                      (Homology [0, 0] [1, -1]),
                      (Homology [0, 1] [0, 0]),
                      (Homology [0, 0] [0, 1])]

fullerA :: HomologyPath
fullerA = lefschetzFibration genusThreeGenerators [0, 1, 2, 3, 4, 5] 14

fullerB :: HomologyPath
fullerB = (lefschetzFibration genusThreeGenerators [7, 8, 3, 2, 1, 0, 4, 3, 2, 1, 5, 4, 3, 2] 1) ++
          (lefschetzFibration genusThreeGenerators [0, 1, 2, 3, 4, 5] 10)

genusThreeGenerators :: HomologyPath
genusThreeGenerators = [(Homology [0, 0, 0] [1, 0, 0]),
                        (Homology [1, 0, 0] [0, 0, 0]),
                        (Homology [0, 0, 0] [-1, 1, 0]),
                        (Homology [0, 1, 0] [0, 0, 0]),
                        (Homology [0, 0, 0] [0, -1, 1]),
                        (Homology [0, 0, 1] [0, 0, 0]),
                        (Homology [0, 0, 0] [0, 0, -1]),
                        (Homology [0, 0, 0] [0, 1, 0]),
                        (Homology [0, 0, 0] [0, -1, 0])]


generateAllHomologies :: Int -> HomologyPath
generateAllHomologies genus = go genus 0
  where
    go :: Int -> Int -> HomologyPath
    go genus index
      | (index == genus) = []
      | otherwise = [(homologySingle (Around index) genus), (homologySingle (Through index) genus)] ++ (go genus (index + 1))

isIdentityOn :: HomologyPath -> Homology -> Bool
isIdentityOn path h1 = (h1 == (homologyDehnTwistSequence path h1))

checkLefschetzFibration :: HomologyPath -> Bool
checkLefschetzFibration [] = True
checkLefschetzFibration paths = foldr (&&) True (map (isIdentityOn paths) (generateAllHomologies (length (aLoop (paths!!0)))))

lefschetzFibration :: HomologyPath -> [Int] -> Int -> HomologyPath
lefschetzFibration paths order 0 = go paths order
  where
    go :: HomologyPath -> [Int] -> HomologyPath
    go paths [] = []
    go paths (x:xs) = [(paths!!x)] ++ (go paths xs)
lefschetzFibration paths order n = concat $ replicate n (lefschetzFibration paths order 0)

rotateMonodromy :: HomologyPath -> Int -> HomologyPath
rotateMonodromy h1 n = take (length h1) (drop n (cycle h1))

homologyToList :: Real a => Homology' a -> [Rational]
homologyToList h1 = map toRational ((aLoop h1) ++ (bLoop h1))

homologyToMatrices :: Homology -> Homology -> [Homology] -> [[Rational]]
homologyToMatrices l m mod = transpose ([(homologyToList l), (homologyToList m)] ++ (map homologyToList mod))

calculateABC :: Homology -> Homology -> [Homology] -> [Rational]
calculateABC l m mod = [(last (out!!0))] ++ [(last (out!!1))]
  where
    out = showMatrix (rref (showMatrix (homologyToMatrices l m mod)))

calculateDelta :: [Rational] -> Int
calculateDelta abc
  | (result < 0) = 1
  | (result == 0) = 0
  | (result > 0) = -1
  where
    result = (abc!!0 + abc!!1)*(abc!!0)

generateRelationBasis :: Homology -> Homology -> HomologyPath
generateRelationBasis gamma e = map (toIntegerHomology . go) (delete e (generateAllHomologies (genus e)))
  where
    norm = homologyDotProduct gamma e
    go :: Homology -> RationalHomology
    go hom = homologySubtract (rationalize hom) (homologyMultiply (rationalize e) ((toRational (homologyDotProduct gamma hom)) / (toRational norm)))

generateRelation :: HomologyPath -> Homology -> Homology
generateRelation phi l = homologySubtract l (homologyDehnTwistSequence phi l)

calculateSignatureStep :: HomologyPath -> Homology -> Int
calculateSignatureStep phi attachingCircle
  | testZeroHomology attachingCircle = trace ("Signature Step: Null Homology, Add -1") (-1)
  | testZeroHomology m = trace ("Signature Step: m is Null, Add 0") 0
  | otherwise = trace ("Signature Step:") (calculateDelta (calculateABC l m mod))
    where
      l = attachingCircle
      basis = generateRemainingBasis l
      e = (basis!!0)!!1
      m = homologyDivide (tr (homologySubtract (tr e) (tr (homologyDehnTwistSequence phi e))))  (homologyDotProduct l e)
      mod = map (generateRelation phi) ([l]++(drop 2 (concat basis)))

calculateSignature :: HomologyPath -> Int
calculateSignature p1 = go [] p1 0
  where
    go :: HomologyPath -> HomologyPath -> Int -> Int
    go phi [] acc = (tr acc)
    go phi (x : xs) acc = go (phi ++ [x]) xs ((tr acc) + (calculateSignatureStep phi x))

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
    go n b | (n == b) =
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
