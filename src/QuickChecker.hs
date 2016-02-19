module QuickChecker where

import Test.QuickCheck
import Data.List
import Semantics

-- Transformation
tr :: Transformation
tr = ([(A,C),(B,D),(E,F)], computeBinding, computeReverseBinding)

-- sourceModel -> matchedElements -> resultingSourceElements
computeBinding :: Model -> SetOf Element -> SetOf Element
computeReverseBinding :: Model -> Link -> SetOf Element
-- computeBinding (_,_,links) = inverseImage links
computeBinding (_,_,links) = imageR links
computeReverseBinding (_,_,_) (from, to) = [from]

-- Quicheck generation of source models and transformations

-- all possible subsets
subSet :: [a] -> [[a]]
subSet []     = [[]]
subSet (e:es) = ess ++ map (e:) ess
    where ess = subSet es

-- split into two non empty
split :: [a] -> [([a],[a])]
split [x1,x2] = [([x1],[x2])]
split (x:xs)  = ([x],xs):map (\(s,t) -> (x:s,t)) xss
    where xss = split xs

-- all combinations
sourceAndTargetElements :: [([Element],[Element])]
sourceAndTargetElements = concat $ map split $ filter (\es -> length es>1) $ subSet [A .. F]

sourceAndTargetElementsGen :: Gen ([Element],[Element])
sourceAndTargetElementsGen = elements sourceAndTargetElements

-- total links
allLinks :: [a] -> [(a,a)]
allLinks es = [ (from,to) | from <- es, to <- es ]

-- total transformation
allTransfos :: [a] -> [a] -> [(a,a)]
allTransfos eSource eTarget = [ (a,b) | a <- eSource, b <- eTarget ]


newtype Config = Config { unConfig::(Model,Transformation) }
instance Show Config where
   show x = let (mS,(r,cb, crb)) = unConfig x
            in show (mS, r)

configs :: Gen Config
configs = do
  -- take a subset of at leat two elements and split it in two
  (elementS,elementT) <- elements $ sourceAndTargetElements
  -- a subset of all possible source links
  linkS <- elements $ subSet $ allLinks elementS
  let rootS = head elementS -- source root is always the first element
      rootT = head elementT -- target root is always the first element
  -- a subset of all possible transfo (does not include root mapping)
  transfo <- elements $ subSet $ allTransfos (tail elementS) elementT
  -- a configuration
  return $ Config ((rootS,elementS,linkS),((rootS,rootT):transfo, computeBinding, computeReverseBinding))

instance Arbitrary Config where
    arbitrary = configs

assertion config =
    let (mS,t) = unConfig config
        c = (mS,t,undefined)
    in --valid mS t ==>
       length (nub [ fst $ getNFromTarget 3 $ apply $ TransformationStrict c
                   , fst $ getNFromTarget 3 $ apply $ TransformationLazy c
                   , fst $ getNFromTarget 3 $ apply $ TransformationIncremental c
                   , fst $ getNFromTarget 3 $ apply $ TransformationReactive c]) == 1

test1 = verboseCheckWith stdArgs { maxSuccess = 10 } assertion
test2 = verboseCheck assertion

-- for debugging purpose only (generated source models and transformations are valid by construction)
valid :: Model -> Transformation -> Bool
valid (root, es, links) (t,_,_) = elem root es && length es == length (nub es) && all (`elem` es) (map fst links) && all (`elem` es) (map snd links) &&
                            all (`notElem` es) (map snd t) && not (null t) && root `elem` (map fst t)

-- Quickchecking updates
-- updateSource ts = addLinkToSource (A, E) (addElementToSource E ts)

-- delete an element but root, and return this element and its links
deleteAnElement :: Element -> Model -> (Model,[Instruction])
deleteAnElement e (root,es,links) = ((root, filter (/=e) es, filter (not . (involving e)) links),AddElement e:map AddLink (filter (involving e) links))
    where involving :: Element -> Link -> Bool
          involving e (from,to) = e==from || e==to

deleteElements :: [Element] -> Model -> (Model,[Instruction]) -- MONADIC
deleteElements []     m = (m,[])
deleteElements (e:es) m = let (m1,is1) = deleteAnElement e m
                              (m2,is2) = deleteElements es m1
                          in (m2,is1++is2) -- beware of the order l2r or r2l of instructions

data Instruction = AddElement Element | AddLink Link deriving (Show,Eq)

--delayI :: (Instruction,Instruction) -> [(Instruction,Instruction)]
--delayI (AddLink    l,i) = [(AddLink    l,i),(i,AddLink l)]
--delayI (AddElement e,i) = [(AddElement e,i)]

permutI :: [Instruction] -> [[Instruction]]
permutI (AddElement e:is) = map (AddElement e:) (permutI is) -- AddElement cannot be delayed
permutI (AddLink    l:is) = concat (map (insertI (AddLink l)) (permutI is))
permutI []                = [[]]

insertI :: Instruction -> [Instruction] -> [[Instruction]]
insertI i0 [] = [[i0]]
insertI i0 (i:is) = (i0:i:is) : map (i:) (insertI i0 is)

runI :: TransformationI m => [Instruction] -> m -> m
runI []                m = m
runI (AddElement e:is) m = runI is (addElementToSource e m)
runI (AddLink    l:is) m = runI is (addLinkToSource l m)

newtype Config' = Config' { unConfig'::([Instruction],Model,Transformation) }
instance Show Config' where
   show x = let (is,mS,(r,cb, crb)) = unConfig' x
            in show (is, mS, r)

configs' :: Gen Config'
configs' = do
  -- take a subset of at leat two elements and split it in two
  (elementS,elementT) <- elements $ concat $ map split $ filter (\es -> length es>=2) $ subSet [A .. F]
  -- a subset of all possible source links
  linkS <- elements $ subSet $ allLinks elementS
  let rootS = head elementS -- source root is always the first element
      rootT = head elementT -- target root is always the first element
  -- a subset of all possible transfo (does not include root mapping)
  transfo <- elements $ subSet $ allTransfos (tail elementS) elementT
  -- a subset of elements (but root)
  elementsToBeDeleted <- elements $ subSet $ elementS \\ [rootS]
  -- delete them
  let (mStripped,is) = deleteElements elementsToBeDeleted (rootS,elementS,linkS)
  -- and generate a sequence of instructions to restore them
  instructions <- elements $ permutI is
  -- a configuration
  return $ Config' (instructions,mStripped,((rootS,rootT):transfo, computeBinding, computeReverseBinding))

instance Arbitrary Config' where
    arbitrary = configs'

quickCheckTest = verboseCheckWith stdArgs { maxSuccess = 100 } assertion'

assertion' config =
    let (is,mS,t) = unConfig' config
        c = (mS,t,undefined)
    in --valid mS t ==>
       length (nub [ fst $ getNFromTarget 3 $ apply $ runI is $ apply $ TransformationStrict c
                   , fst $ getNFromTarget 3 $ apply $ runI is $ apply $ TransformationLazy c
                   , fst $ getNFromTarget 3 $ runI is $ apply $ TransformationIncremental c
                   , fst $ getNFromTarget 3 $ runI is $ apply $ TransformationReactive c]) == 1

-- ([AddElement C,AddLink (A,C)],(A,[A,B],[(A,A),(A,B),(B,B)]),[(A,D),(C,D),(C,F)])

-- bug = fst $ getN 3 $ apply $ runI [AddElement C,AddLink (A,C)] $ apply $ TransformationReactive ((A,[A,B],[(A,A),(A,B),(B,B)]),[(A,D),(C,D),(C,F)], undefined)
