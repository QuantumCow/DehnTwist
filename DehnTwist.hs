{-# LANGUAGE DeriveFunctor #-}
import Control.Applicative
import Data.Foldable
import Data.Monoid
import Data.List (transpose, delete, findIndex, intercalate, elemIndex, isInfixOf)
import Data.Ratio
import Data.Maybe
import Debug.Trace
import Prelude hiding (concatMap, foldr, foldl, foldl', concat, all, maximum, find, sum, notElem)


trA :: Show a => a -> a
trA x = traceShow x x

trLabel :: Show a => String -> a -> a
trLabel text x = traceShow (text ++ " " ++ (show x)) x

trxLabel :: Show a => String -> a -> a
trxLabel text x = x

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

data SignatureTestCase = SignatureTestCase { lf :: HomologyPath
                                           , name :: String
                                           , signature :: Int
                                           , cycleLength :: Int
                                           }

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

rationalizeMatrix :: [[Integer]] -> [[Rational]]
rationalizeMatrix [] = []
rationalizeMatrix (x:xs) = [(map toRational x)] ++ (rationalizeMatrix xs)

roundMatrix :: [[Rational]] -> [[Integer]]
roundMatrix [] = []
roundMatrix (x:xs) = [(map round x)] ++ (roundMatrix xs)

toIntegerHomology :: RationalHomology -> Homology
toIntegerHomology rh = mapHom (floor . ((toRational mult) *)) rh
    where
      mult = rationalHomologyLCM rh

rationalHomologyLCM :: RationalHomology -> Integer
rationalHomologyLCM rh = foldl lcm 1 (map denominator ((aLoop rh) ++ (bLoop rh)))

homologyLCM :: Homology -> Integer
homologyLCM h1 = foldl lcm 1 (filter (/= 0) (aLoop h1 ++ bLoop h1))

homologyPrint :: Homology -> String
homologyPrint h1 = go (aLoop h1) (bLoop h1) 0
  where
    go :: [Integer] -> [Integer] -> Integer -> String
    go [] [] count  = ""
    go (x:xs) (y:ys) count = (if x /= 0 then ((show x) ++ "a" ++ (show count) ++ "+") else "") ++
                             (if y /= 0 then ((show y) ++ "b" ++ (show count) ++ "+") else "") ++
                              go xs ys (count + 1)

pathPrintHom :: HomologyPath -> String
pathPrintHom = intercalate ", " . map homologyPrint

dotHom :: Num a => Homology' a -> Homology' a -> a
dotHom h1 h2 =
  sum (zipWith (*) (aLoop h1) (bLoop h2)) - sum (zipWith (*) (aLoop h2) (bLoop h1))

zipHom :: (a -> b -> c) -> Homology' a -> Homology' b -> Homology' c
zipHom f (Homology a1 b1) (Homology a2 b2) = Homology (zipWith f a1 a2) (zipWith f b1 b2)

mapHom :: (a -> b) -> Homology' a -> Homology' b
mapHom f (Homology a b) = Homology (map f a) (map f b)

addHom :: Num a => Homology' a -> Homology' a -> Homology' a
addHom = zipHom (+)

subHom :: Num a => Homology' a -> Homology' a -> Homology' a
subHom = zipHom (-)

mulHom :: Num a => Homology' a -> a -> Homology' a
mulHom h1 r = mapHom (* r) h1

divHom :: Integral a => Homology' a -> a -> Homology' a
divHom h1 r = mapHom (`div` r) h1

dehnTwistHom :: Num a => Homology' a -> Homology' a -> Homology' a
dehnTwistHom twist path =
  path `addHom` (twist `mulHom` dotHom twist path)

dehnTwistSeqHom :: HomologyPath -> Homology -> Homology
dehnTwistSeqHom xs h1 = foldl (flip dehnTwistHom) h1 xs

inverseDehnTwistHom :: Num a => Homology' a -> Homology' a -> Homology' a
inverseDehnTwistHom twist path =
  path `subHom` (twist `mulHom` dotHom twist path)

singleHom :: Generator -> Int -> Homology
singleHom (Around homIndex) genus
   = Homology ((replicate homIndex 0) ++ [1] ++ (replicate (genus-homIndex-1) 0)) (replicate genus 0)
singleHom (Through homIndex) genus
   = Homology (replicate genus 0) ((replicate homIndex 0) ++ [1] ++ (replicate (genus-homIndex-1) 0))

negateHom :: Homology -> Homology
negateHom = mapHom negate

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
    | testZeroHomology h1 = h1
    | otherwise           = divHom h1(homologyLCM h1)

-- | This will return true if the homology represents a simple closed curve
isSCC :: Homology -> Bool
isSCC h1 = homologyLCM h1 == 1

generateAllHomologyPairs :: Int -> [HomologyPath]
generateAllHomologyPairs g = go (generateAllHomologies g) []
  where
    go :: HomologyPath ->  [HomologyPath] -> [HomologyPath]
    go [] acc = acc
    go (x:y:rest) acc = go rest (acc ++ [[x, y]])
    -- This is just pairing off the homologies.
    -- Ben: Is this actually correct? It looks odd. Perhaps you should recurse
    -- with (y:rest)?

generateRemainingBasis :: Homology -> [HomologyPath]
generateRemainingBasis h1A = go [[h1A, (fromJust (homologyComplement h1A))]] (generateAllHomologyPairs g)
  where
    g = genus h1A
    go :: [HomologyPath] -> [HomologyPath] -> [HomologyPath]
    go hAcc [] = hAcc
    go hAcc (x:rest)
      | length hAcc == g
        = hAcc
      | otherwise
        = if nextPair == [] then go hAcc rest else go (hAcc ++ [nextPair]) rest
            where
               nextPair = nextBasisPair x hAcc

nextBasisPair :: HomologyPath -> [HomologyPath] -> HomologyPath
nextBasisPair [h1A, h1B] hAcc = go h1A h1B hAcc
  where
    go :: Homology -> Homology -> [HomologyPath] -> HomologyPath
    go h2A h2B [] = if not ((testZeroHomology h2A) || (testZeroHomology h2B)) then [h2A, h2B] else []
    go h2A h2B (x:xs) = go (homologySCC (subtractOutAcc h2A x)) (homologySCC (subtractOutAcc h2B x)) xs

subtractOutAcc :: Homology -> HomologyPath -> Homology
subtractOutAcc h1 [h1A, h1B] = addHom (subHom h1 (mulHom h1A (dotHom h1 h1B)))
                                           (mulHom h1B (dotHom h1 h1A))


-- | This will return a homology b such that a . b = 1
homologyComplement :: Homology -> Maybe Homology
homologyComplement h1
    | Just unit <- findUnit h1
      = Just (unitHomologyComplement unit (genus h1))
    | Just mGen <- findNonZero h1, Just nGen <- findRelPrime h1 mGen
      = Just (primeHomologyComplement h1 mGen nGen)
    | otherwise
      = Nothing

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

getHomology :: Homology' a -> Generator -> a
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
unitHomologyComplement (Pos (Around x)) g = singleHom (Through x) g
unitHomologyComplement (Pos (Through x)) g = negateHom (singleHom (Around x) g)
unitHomologyComplement (Neg (Around x)) g = negateHom (singleHom (Through x) g)
unitHomologyComplement (Neg (Through x)) g = singleHom (Around x) g

findNonZero :: Homology -> Maybe Generator
findNonZero h1
    = (Around <$> findIndex (/= 0) (aLoop h1)) <|> (Through <$> findIndex (/= 0) (bLoop h1))

findUnit :: Homology -> Maybe (Signed Generator)
findUnit h1
    =     (Pos . Around  <$> elemIndex 1    (aLoop h1))
      <|> (Neg . Around  <$> elemIndex (-1) (aLoop h1))
      <|> (Pos . Through <$> elemIndex 1    (bLoop h1))
      <|> (Neg . Through <$> elemIndex (-1) (bLoop h1))

findRelPrime :: Homology -> Generator -> Maybe Generator
findRelPrime h1 g1
    = (Around <$> findIndex isRelPrime (aLoop h1)) <|> (Through <$> findIndex isRelPrime (bLoop h1))
    where
      m = getHomology h1 g1
      isRelPrime :: Integer -> Bool
      isRelPrime n = 1 == gcd m n

findNonZeroIntersection :: Homology -> Maybe Homology
findNonZeroIntersection h1 = go 0
  where
    go :: Int -> Maybe Homology
    go count
      | count == genus h1
        = Nothing
      | (dotHom (singleHom (Around count) (genus h1)) h1) /= 0
        = Just (singleHom (Around count) (genus h1))
      | (dotHom (singleHom (Through count) (genus h1)) h1) /= 0
        = Just (singleHom (Through count) (genus h1))
      | otherwise
        = go (count + 1)

showxMatrix :: [[Rational]] -> [[Rational]]
showxMatrix x = x 
        
showMatrix :: [[Rational]] -> [[Rational]]
showMatrix [] = []
showMatrix (x:xs) = traceShow (map numerator x) ([x]++(showMatrix xs))

oneIndex :: [Rational] -> Maybe Int
oneIndex row = elemIndex 1 row

getOneCols :: [[Rational]] -> [Maybe Int]
getOneCols m = map oneIndex m

findMissingOne :: [Maybe Int] -> Int
findMissingOne ones = go ones 0
  where
    go :: [Maybe Int] -> Int -> Int
    go (x:xs) n | (x==Nothing) = n
                | ((fromJust x)==n) = go xs (n+1)
                | otherwise = n
    go [] n = n

isGoodPair :: (Rational, Rational) -> Bool
isGoodPair (0, 0) = False
isGoodPair (x, y) = True
    
getPQ :: [[Rational]] -> Int    
getPQ m | ((firstOne == Nothing) || ((fromJust firstOne) > 1)) = calculateDelta ((m!!0)!!1, -1)
        | otherwise = if (pairs == []) then 0 else (calculateDelta (pairs!!0))
  where
    firstOne = oneIndex (m!!1)
    pairs = filter isGoodPair (drop 2 (zip (m!!0) (m!!1)))
  
   
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

{-Convert a vector of homologies into a list of homologies, genus n-}
{-Note this will fail if the length of v is not a multiple of 2n -}
vectorToHomologyPath :: [Integer] -> Int -> HomologyPath
vectorToHomologyPath [] n = []
vectorToHomologyPath v n = [(vectorToHomology v n)] ++ (vectorToHomologyPath (drop (2*n) v) n)               
                  
{- Take the first 2n terms from v, and make a homology out of them -}
{- a1 b1 a2 b2 -> Homology (a1 a2) (b1 b2))-}
vectorToHomology :: [Integer] -> Int -> Homology
vectorToHomology v n = Homology left right      
  where
    (left, right) = go v n
    go :: [Integer] -> Int -> ([Integer],[Integer])
    go va 0 = ([],[])
    go (v1:v2:vx) na = ([v1]++nextL, [v2]++nextR)
      where (nextL, nextR) = go vx (na-1)
    
generateIdentity :: Int -> [[Rational]]
generateIdentity n = go n
  where
    go :: Int -> [[Rational]]
    go 0 = []
    go m = [(replicate (n - m) (toRational 0/1)) ++ [(toRational 1/1)] ++ (replicate (m-1) (toRational 0/1))] ++ (go (m-1))
                  
{- Note this function will fail if given an odd vector, but we want that since symplectic spaces must be even -}                  
symplecticDot :: Eq a => Fractional a => [a] -> [a] -> a
symplecticDot [] [] = 0/1
symplecticDot (x1:x2:xs) (y1:y2:ys) = ((x1*y2) - (x2*y1)) + (symplecticDot xs ys)                  
                  
negateMatrix :: Eq a => Fractional a => [[a]] -> [[a]]
negateMatrix m = map (\x -> (map (\y -> -y) x)) m                  

findMissing :: [Int] -> [Int]
findMissing l = filter (\x -> notElem x l) [0..top]
  where top = maximum l

insertIdentity :: [[Rational]] -> [[Rational]] -> [Int] -> [[Rational]]
insertIdentity m i [] = m ++ i
insertIdentity m (i:is) (missing:missings) = insertRowN (insertIdentity m is missings) i missing 
{- Note that the order here is important since adding a row changes the indices. We must add later first -}

extractKernel :: [[Rational]] -> [[Rational]]
extractKernel m = transpose (insertIdentity mOut (generateIdentity (length (mOut!!0))) (findMissing (getPivots rf)))
  where mOut = (negateMatrix (removePivots rf))
        rf   = rref m
                  
removeRowN :: [[Rational]] -> Int -> [[Rational]]
removeRowN m r = let (ys,zs) = splitAt r m   in   ys ++ (tail zs)

insertRowN :: [[Rational]] -> [Rational] -> Int -> [[Rational]]
insertRowN m r n = let (ys,zs) = splitAt n m   in   ys ++ [r] ++ zs

removePivots :: [[Rational]] -> [[Rational]]
removePivots m = (transpose (go (transpose m) (getPivots m)))
  where
    go :: [[Rational]] -> [Int] -> [[Rational]]
    go m1 []                   = m1
    go m1 (x : xs) | (x < 0)   = m1
                   | otherwise = removeRowN (go m1 xs) x {- notice order here is important. remove later rows first so indexing is accurate -}
                  
getPivots :: Eq a => Fractional a => [[a]] -> [Int]
getPivots [] = []
getPivots (x:xs) = [(getPivot x)] ++ (getPivots xs)

getPivot :: Eq a => Fractional a => [a] -> Int
getPivot r | Just i <- firstOne = i
           | otherwise          = -1
  where firstOne = elemIndex 1 r

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
testZeroHomology h1 = all (==0) (aLoop h1) && all (==0) (bLoop h1)

printAllTests :: [(Integer, Integer)]
printAllTests = (zip [-8, -4, -12, -18, -24, -18, -10, -20, -30, -48, -42, -1, -8, -11, -16] (map (toInteger . calculateSignature)
    [testGenusOne, matsumoto, matsumotoA, matsumotoB, matsumotoC, matsumotoD, genusTwoDiscA, genusTwoDiscB, genusTwoDiscC,
    fullerA, fullerB, genusThreeDiscA, genusThreeDiscB, genusThreeDiscC, genusThreeDiscD]))

allTestCases :: [SignatureTestCase]
allTestCases = [(SignatureTestCase testGenusOne "testGenusOne" (-8) 2),
                (SignatureTestCase matsumoto "matsumoto" (-4) 4),
                (SignatureTestCase matsumotoA "matsumotoA" (-12) 10),
                (SignatureTestCase matsumotoB "matsumotoB" (-18) 5),
                (SignatureTestCase matsumotoC "matsumotoC" (-24) 4),
                (SignatureTestCase matsumotoD "matsumotoD" (-18) 15),
                (SignatureTestCase genusTwoDiscA "genusTwoDiscA" (-10) 1),
                (SignatureTestCase genusTwoDiscB "genusTwoDiscB" (-20) 1),
                (SignatureTestCase genusTwoDiscC "genusTwoDiscC" (-30) 1),
                (SignatureTestCase fullerA "fullerA" (-48) 6),
                (SignatureTestCase fullerB "fullerB" (-42) 74),
                (SignatureTestCase genusThreeDiscA "genusThreeDiscA" (-1) 1),
                (SignatureTestCase genusThreeDiscB "genusThreeDiscB" (-8) 1),
                (SignatureTestCase genusThreeDiscC "genusThreeDiscC" (-11) 1),
                (SignatureTestCase genusThreeDiscD "genusThreeDiscD" (-16) 1)]
    
runAllTests :: String
runAllTests
  | ((calculateSignature testGenusOne) /= -8) = "Genus One Failed"
  | ((calculateSignature matsumoto) /= -4) = "matsumoto Failed"
  | ((calculateSignature matsumotoA) /= -12) = "matsumotoA Failed"
  | ((calculateSignature matsumotoB) /= -18) = "matsumotoB Failed"
  | ((calculateSignature matsumotoC) /= -24) = "matsumotoC Failed"
  | ((calculateSignature matsumotoD) /= -18) = "matsumotoD Failed"
  | ((calculateSignature genusTwoDiscA) /= -10) = "genusTwoDiscA Failed"
  | ((calculateSignature genusTwoDiscB) /= -20) = "genusTwoDiscB Failed"
  | ((calculateSignature genusTwoDiscC) /= -30) = "genusTwoDiscC Failed"
  | ((calculateSignature fullerA) /= -48) = "fullerA Failed"
  | ((calculateSignature fullerB) /= -42) = "fullerB Failed"
  | ((calculateSignature genusThreeDiscA) /= -1) = "genusTwoDiscA Failed"
  | ((calculateSignature genusThreeDiscB) /= -8) = "genusTwoDiscB Failed"
  | ((calculateSignature genusThreeDiscC) /= -11) = "genusTwoDiscC Failed"
  | ((calculateSignature genusThreeDiscD) /= -16) = "genusTwoDiscD Failed"
  | otherwise = "All worked!"

bigTest :: [SignatureTestCase] -> Bool
bigTest [] = (trLabel "All Tests Passed" True)
bigTest (x:xs) = if (nextTest == Nothing)
                           then (trLabel (name x) (bigTest xs)) 
                           else (trLabel ((name x)++" Failed on "++(show (snd (fromJust nextTest)))++" with "++(show (fst (fromJust nextTest)))) False)
   where
     nextTest = checkRotations (lf x) (cycleLength x) (signature x)
  
checkRotations :: HomologyPath -> Int -> Int -> Maybe (Int, Int)
checkRotations lf 0 answer = Nothing
checkRotations lf n answer = if (nextAnswer == answer) then (checkRotations lf (n-1) answer) else (Just (nextAnswer, (n-1)))
   where
     nextAnswer = testRotation lf (n-1)
     
testRotation :: HomologyPath -> Int -> Int
testRotation lf n = calculateSignature ((drop n lf)++(take n lf))
  
testAllRotations :: HomologyPath -> [Int]
testAllRotations lf = testRotations lf (length lf)
  
testRotations :: HomologyPath -> Int -> [Int]
testRotations lf n = go lf [] [] n
  where
    go :: HomologyPath -> HomologyPath -> [Int] -> Int -> [Int]
    go x y acc 0 = acc
    go [] y acc n = acc
    go (x:xs) y acc n = go xs (y++[x]) (acc ++ [(calculateSignature (([x]++xs)++y))]) (n-1)
  
testGenusOne :: HomologyPath
testGenusOne = lefschetzFibration [(singleHom (Around 0) 1), (singleHom (Through 0) 1)] [0, 1] 6

matsumoto :: HomologyPath
matsumoto = lefschetzFibration (go 0) [0, 1, 2, 3] 2
  where
    go :: Integer -> HomologyPath
    go 0 = [Homology [1, 1] [0, 0]] ++ go 1
    go 1 = [Homology [0, 0] [0, 0]] ++ go 2
    go 2 = [Homology [0, 0] [-1, -1]] ++ go 3
    go 3 = [Homology [1, 1] [-1, -1]]

matsumotoPath :: Int -> Int -> Homology
matsumotoPath index genus
    | (band == 0) = Homology (replicate genus 1) (replicate genus 0)
    | ((odd genus) && (index == a)) = Homology
            (replicate genus 0)
            ((replicate (div genus 2) 0) ++ [-1] ++ (replicate (div genus 2) 0))
    | ((odd genus) && (index == b)) = Homology
            (replicate genus 0)
            ((replicate (div genus 2) 0) ++ [-1] ++ (replicate (div genus 2) 0))
    | ((odd genus) && (index == genus)) = Homology
            ((replicate (div genus 2) 0) ++ [1] ++ (replicate (div genus 2) 0))
            ((replicate (div genus 2) 0) ++ [-2] ++ (replicate (div genus 2) 0))
    | ((even genus) && (index == c)) = Homology (replicate genus 0) (replicate genus 0)
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
    | (even genus) = lefschetzFibration paths (reverse [0 .. c]) 2
    | (odd genus) = lefschetzFibration paths (reverse ([0 .. a]++[a, b, b])) 2
    where
      c = genus + 1
      a = genus + 1
      b = genus + 2
      maxIndex = if (even genus) then c else b
      paths = concatMap (\x -> [(matsumotoPath x genus)]) [0 .. maxIndex]

genusNChain :: Int -> HomologyPath
genusNChain genus = lefschetzFibration paths (reverse ([0 .. (2*genus -1)])) (4*genus + 2)
    where
      paths = concatMap (\x -> [(genusNGenerators genus x)]) [0 .. 2*genus]
     
genusNInvolution :: Int -> HomologyPath
genusNInvolution genus = lefschetzFibration paths ([0 .. 2*genus]++(reverse [0 .. 2*genus])) 2
    where
      paths = concatMap (\x -> [(genusNGenerators genus x)]) [0 .. 2*genus]
      
genusNGenerators :: Int -> Int -> Homology
genusNGenerators genus 0 = Homology
               (replicate genus 0)
               ([-1]++(replicate (genus - 1) 0))
genusNGenerators genus index | (index == 2*genus) = Homology
               (replicate genus 0)
               ((replicate (genus - 1) 0)++[1])
genusNGenerators genus index 
            | (even index) = Homology
               (replicate genus 0)
               ((replicate ((div index 2)-1) 0)++[1, -1]++(replicate (genus - (div index 2) - 1) 0))            
            | (odd index) = Homology
                ((replicate (div index 2) 0)++[1]++(replicate (genus - (div index 2) - 1) 0))
                (replicate genus 0)
                
testNotGenusOne :: HomologyPath
testNotGenusOne = lefschetzFibration [(singleHom (Around 0) 1), (singleHom (Through 0) 1)] [0, 1] 1

matsumotoA :: HomologyPath
matsumotoA = lefschetzFibration genusTwoGenerators [0, 1, 2, 3, 4, 4, 3, 2, 1, 0] 2

matsumotoB :: HomologyPath
matsumotoB = lefschetzFibration genusTwoGenerators [0, 1, 2, 3, 4] 6

matsumotoC :: HomologyPath
matsumotoC = lefschetzFibration genusTwoGenerators [0, 1, 2, 3] 10

matsumotoD :: HomologyPath
matsumotoD = lefschetzFibration genusTwoGenerators [4, 0, 3, 1, 2, 3, 1, 4, 0, 3, 1, 2, 3, 1, 2] 2

genusTwoDiscA :: HomologyPath
genusTwoDiscA = lefschetzFibration genusTwoGenerators [0, 2, 4, 1, 3, 1, 0, 0, 0, 2, 4, 2, 4, 1, 3, 4] 1

genusTwoDiscB :: HomologyPath
genusTwoDiscB = lefschetzFibration genusTwoGenerators [0, 2, 4, 1, 3, 1, 0, 0, 0, 2, 4, 2, 4, 1, 3, 4] 2

genusTwoDiscC :: HomologyPath
genusTwoDiscC = lefschetzFibration genusTwoGenerators [0, 2, 4, 1, 3, 1, 0, 0, 0, 2, 4, 2, 4, 1, 3, 4] 3


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

genusThreeDiscA :: HomologyPath
genusThreeDiscA = lefschetzFibration genusThreeGenerators [0, 2, 4, 6, 1, 3, 5] 1

genusThreeDiscB :: HomologyPath
genusThreeDiscB = lefschetzFibration genusThreeGenerators [0, 2, 4, 6, 1, 3, 5] 2

genusThreeDiscC :: HomologyPath
genusThreeDiscC = lefschetzFibration genusThreeGenerators [0, 2, 4, 6, 1, 3, 5] 3

genusThreeDiscD :: HomologyPath
genusThreeDiscD = lefschetzFibration genusThreeGenerators [0, 2, 4, 6, 1, 3, 5] 4

          
          
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
      | otherwise = [(singleHom (Around index) genus), (singleHom (Through index) genus)] ++ (go genus (index + 1))

isIdentityOn :: HomologyPath -> Homology -> Bool
isIdentityOn path h1 = (h1 == (dehnTwistSeqHom path h1))

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

calculateABC :: Homology -> Homology -> [Homology] -> Int
calculateABC l m mod = getPQ (showxMatrix (rref (showxMatrix (homologyToMatrices l m mod))))

calculateDelta :: (Rational, Rational) -> Int
calculateDelta (a, b)
  | (result < 0) = 1
  | (result == 0) = 0
  | (result > 0) = -1
  where
    result = (a + b)*(a)

generateRelationBasis :: Homology -> Homology -> HomologyPath
generateRelationBasis gamma e = map (toIntegerHomology . go) (delete e (generateAllHomologies (genus e)))
  where
    norm = dotHom gamma e
    go :: Homology -> RationalHomology
    go hom = subHom (rationalize hom) (mulHom (rationalize e) ((toRational (dotHom gamma hom)) / (toRational norm)))

generateRelation :: HomologyPath -> Homology -> Homology
generateRelation phi l = subHom l (dehnTwistSeqHom phi l)

calculateSignatureStep :: HomologyPath -> Homology -> Int
calculateSignatureStep phi attachingCircle
  | testZeroHomology attachingCircle = trxLabel ("Signature Step: Attaching handle null, Add -1") (-1)
  | testZeroHomology m = trxLabel ("Signature Step: crossing loop e(m) is Null, Add 0") 0
  | otherwise = trxLabel ("Signature Step:") (calculateABC l m mod)
    where
      l = attachingCircle
      basis = trxLabel "RemainingBasis" (generateRemainingBasis l)
      e = (basis!!0)!!1
      m = divHom (trxLabel "DivOut" (subHom (trxLabel "SubInA" e) (trxLabel "SubInB" (dehnTwistSeqHom phi e))))  (dotHom l e)
      mod = map (generateRelation phi) ([l]++(drop 2 (concat basis)))

calculateSignature :: HomologyPath -> Int
calculateSignature p1 | traceShow ("calculate Signature " ++ (show (length p1))) False = 0
calculateSignature p1 = go [] p1 0 1
  where
    go :: HomologyPath -> HomologyPath -> Int -> Int -> Int
    go phi [] acc stepCount = (trxLabel "calculateSignatureEnd" acc)
    go phi (x : xs) acc stepCount = go (phi ++ [x]) xs ((trxLabel ("calculateSignature"++(show stepCount)) acc) + (calculateSignatureStep phi x)) (stepCount + 1)

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
genusNRelators n = foldMap go [0..n-1]
  where
    go :: Int -> Path
    go b = Path ([Pos (Around b), Pos (Through b), Neg (Around b), Neg (Through b)])

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

    
testNosaka :: [[Integer]]
testNosaka = calculateQMatrix (generateGammaKernel 2 matsumotoA) matsumotoA


calculateQMatrix :: [HomologyPath] -> HomologyPath -> [[Integer]]
calculateQMatrix kernel monodromy = go kernel
  where
    go :: [HomologyPath] -> [[Integer]]
    go [] = []
    go (x:xs) = [calculateQMatrixRow x kernel monodromy]++(go xs)

calculateQMatrixRow :: HomologyPath -> [HomologyPath] -> HomologyPath -> [Integer]
calculateQMatrixRow x [] monodromy = []
calculateQMatrixRow x (y:ys) monodromy = [calculateQ x y monodromy] ++ (calculateQMatrixRow x ys monodromy)

calculateQ :: HomologyPath -> HomologyPath -> HomologyPath -> Integer
calculateQ x y monodromy = go (generateLeft x monodromy) (generateRight y monodromy)
  where
    go :: HomologyPath -> HomologyPath -> Integer
    go [] []         = 0
    go (x:xs) (y:ys) = (dotHom x y) + (go xs ys)

generateLeft :: HomologyPath -> HomologyPath -> HomologyPath
generateLeft x monodromy = go (x!!0) 1 {-x!!0 is a dummy variable -}
  where
    stop = (length monodromy)
    xiDiff :: Int -> Homology
    xiDiff n = subHom (x!!(n-1)) (x!!n)
    go :: Homology -> Int -> HomologyPath
    go acc 1 = [xiDiff 1] ++ (go (xiDiff 1) 2)
    go acc n | (n == stop) = []
             | otherwise   = [addHom (dehnTwistHom (monodromy!!(n-1)) acc) (xiDiff n)] ++ (go (addHom (dehnTwistHom (monodromy!!(n-1)) acc) (xiDiff n)) (n+1))

generateRight :: HomologyPath -> HomologyPath -> HomologyPath
generateRight y monodromy = go 1
  where
    stop = (length monodromy)
    go :: Int -> HomologyPath
    go n | (n == stop) = []
         | otherwise   = [subHom (y!!n) (inverseDehnTwistHom (monodromy!!n) (y!!n))] ++ (go (n+1))

generateGammaKernel :: Int -> HomologyPath -> [HomologyPath]
generateGammaKernel genus monodromy = go (extractKernel (generateGammaMatrix (generateAllHomologies genus) monodromy))
  where
    go :: [[Rational]] -> [HomologyPath]
    go [] = []
    go (x:xs) = [(vectorToHomologyPath (map round x) genus)] ++ (go xs)

generateGammaMatrix :: HomologyPath -> HomologyPath -> [[Rational]]
generateGammaMatrix hBasis monodromy = transpose (go monodromy)
  where 
    go :: HomologyPath -> [[Rational]]
    go [] = []
    go (x:xs) = (generateGammaRow hBasis (x:xs)) ++ (go xs)

generateGammaRow :: HomologyPath -> HomologyPath -> [[Rational]]
generateGammaRow hBasis (x:xs) = (map homologyToList (map (\y -> go (firstStep y x) xs) hBasis))
  where
    go :: Homology -> HomologyPath -> Homology
    go output [] = output
    go output (x:xs) = go (dehnTwistHom x output) xs
    firstStep :: Homology -> Homology -> Homology
    firstStep h1 oper = (subHom h1 (dehnTwistHom oper h1))
    
isDiagonal :: HomologyPath -> Bool
isDiagonal [] = True
isDiagonal (x:xs) | (length xs)==0 = True
                  | otherwise = ((x == (xs!!0)) && (isDiagonal xs))

isZero :: HomologyPath -> HomologyPath -> Bool
isZero [] [] = True
isZero (v:vs) (m:ms) = ((v == (dehnTwistHom m v)) && (isZero vs ms))

countZeros :: [HomologyPath] -> HomologyPath -> Int
countZeros [] m = 0
countZeros (v:vs) m | ((isDiagonal v) || (isZero v m)) = (1 + (countZeros vs m))
                    | otherwise = countZeros vs m
   
generateZeros :: [HomologyPath] -> HomologyPath -> [Int]
generateZeros v m = go v 0
  where
    go :: [HomologyPath] -> Int -> [Int]
    go [] current = []
    go (v:vs) current | ((isDiagonal v) || (isZero v m)) = ([current] ++ (go vs (current + 1)))
                      | otherwise = go vs (current + 1)

removeZeroRows :: [HomologyPath] -> HomologyPath -> [HomologyPath]
removeZeroRows v m = go v
  where
    go :: [HomologyPath] -> [HomologyPath]
    go [] = []
    go (v:vs) | ((isDiagonal v) || (isZero v m)) = (go vs)
              | otherwise = ([v] ++ (go vs))
              


   