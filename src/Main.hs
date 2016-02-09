-- Abstract (semantics-like) version
-- Restriction ReactiveATL w.r.t. standard ATL
-- * allInstances is not Reactive
-- * inverse (that is implemented by allInstances) is not reactive either
--
-- Simplifications w.r.t. ReactiveATL:
-- * no attribute
-- * only one reference for each metaelement
-- * no multiple output pattern elements
-- * all references have the same binding
-- * multiple input pattern elements are encoded as couples (not a restriction)

module Main where

import Data.Tuple
import Data.List
import Debug.Trace
import Test.QuickCheck

-- MATHS
type SetOf a = [a]

--distinguish relation and function? and bijection?
type Relation = SetOf (Element,Element)

image :: Relation -> SetOf Element -> SetOf Element
image r es = nub (concatMap (image1 r) es)
    where image1 :: Relation -> Element -> SetOf Element
          image1 r1 e = [ e2 | (e1,e2) <- r1, e1==e ]

inverseImage :: Relation -> SetOf Element -> SetOf Element
inverseImage = image . map swap

crossProduct :: Element -> SetOf Element -> Relation
crossProduct e1 es2 = [ (e1,e2) | e2 <- es2 ]

type Link = (Element,Element)

-- (root, all elements, all links)
-- in lazy semantics (root, all elements with valid outgoing references, all links from valid elements)
type Model = (Element,SetOf Element,SetOf Link)

class TransformationI m where
    apply :: m -> m
    getFromTarget :: m -> Element -> (SetOf Element,m)
    getRootFromTarget :: m -> Element
    addElementToSource :: Element -> m -> m
    addLinkToSource :: Link -> m -> m

getAllFromTarget :: TransformationI m => m -> SetOf Element -> (SetOf Element, m)
getAllFromTarget m0 [] = ([],m0)
getAllFromTarget m0 (e:es) = let (est1,m1) = getFromTarget m0 e
                                 (est2,m2) = getAllFromTarget m1 es
                             in (est1 `union` est2,m2)

getN :: TransformationI m => Int -> m -> (SetOf Element, m)
getN 0 m = ([getRootFromTarget m], m)
getN n m = let (es', m') = getN (n-1) m
               (es'', m'') = getAllFromTarget m' es'
           in (union es' es'', m'')

newtype TransformationStrict = TransformationStrict (Model,Transformation,Model) deriving Show

instance TransformationI TransformationStrict where
    getRootFromTarget (TransformationStrict (_,_,(root,_,_))) = root
    getFromTarget m@(TransformationStrict (_,_,(_,_,links))) e = (image links [e],m)
    addElementToSource e (TransformationStrict ((root,es,links),t,m')) = TransformationStrict ((root,e:es,links),t,m')
    addLinkToSource l (TransformationStrict ((rootS,elementsS,linksS),t,m')) = TransformationStrict ((rootS,elementsS,l:linksS), t, m')
    apply (TransformationStrict (m, t, _))  =
        let (targetRoot,targetElements) = matchingPhase t m
            targetLinks = applyPhase t m targetElements
        in TransformationStrict (m, t, (targetRoot,targetElements,targetLinks))


-- model strict transformation
-- it obtains the transformed root and all transformed elements
matchingPhase :: Transformation -> Model -> (Element,SetOf Element)
matchingPhase t (root,elements,_) = (head (image t [root]),image t elements)

applyPhase :: Transformation -> Model -> SetOf Element -> SetOf Link
applyPhase t m = concatMap (bindingApplication t m)

newtype TransformationLazy = TransformationLazy (Model,Transformation,Model) deriving Show
instance TransformationI TransformationLazy where
    getRootFromTarget (TransformationLazy (_,_,(rootT,_,_))) = rootT
    getFromTarget mL@(TransformationLazy (mS,t,mT@(rootT,elementsT,linksT))) e | e `elem` elementsT = (image linksT [e],mL)
                                                                               | otherwise
             = let ls = bindingApplication t mS e
                   mT1 = (rootT,e:elementsT,ls++linksT)
               in (image (ls++linksT) [e],TransformationLazy (mS, t, mT1))
    addElementToSource e (TransformationLazy ((root,es,links),t,m')) = TransformationLazy ((root,e:es,links),t,m')
    addLinkToSource l (TransformationLazy ((rootS,elementsS,linksS),t,m')) = TransformationLazy ((rootS,elementsS,l:linksS), t, m')
    apply (TransformationLazy (m,t,_)) = TransformationLazy (initialize t m)

initialize :: Transformation -> Model -> (Model,Transformation,Model)
initialize t m = (m,t,(rootT,[],[]))
     where (root,_,_) = m
           [rootT] = image t [root]

newtype TransformationIncremental = TransformationIncremental (Model, Transformation, Model) deriving Show
instance TransformationI TransformationIncremental where
    getRootFromTarget(TransformationIncremental (_,_,(rootT,_,_))) = rootT
    getFromTarget m@(TransformationIncremental (_, _, (_,_,links))) e = (image links [e],m)
    addElementToSource e (TransformationIncremental ((root,es,links), t, (root',es',links'))) =
                                   let [ne] = image t [e]
                                   in TransformationIncremental ((root,e:es,links), t, (root',ne:es',links'))
    addLinkToSource l (TransformationIncremental ((root,es,links), t, (root',es',links'))) =
                                   let msu = (root,es,l:links)
                                       ls = foldr union [] $ map (bindingApplication t msu) (image t (computeReverseBinding msu l))
                                   in TransformationIncremental (msu, t, (root',es',ls++links'))
    apply (TransformationIncremental (m, t, _)) =
            let (targetRoot,targetElements) = matchingPhase t m
                targetLinks = applyPhase t m targetElements
            in TransformationIncremental (m, t, (targetRoot,targetElements,targetLinks))


newtype TransformationReactive = TransformationReactive (Model, Transformation, Model) deriving Show
instance TransformationI TransformationReactive where
    getRootFromTarget(TransformationReactive (_,_,(rootT,_,_))) = rootT
    getFromTarget mL@(TransformationReactive (mS,t,mT@(rootT,elementsT,linksT))) e | e `elem` elementsT = (image linksT [e],mL)
                                                                                   | otherwise
                 = let ls = bindingApplication t mS e -- TODO: add also elements
                       mT1 = (rootT,e:elementsT,ls++linksT)
                   in (image (ls++linksT) [e],TransformationReactive (mS, t, mT1))
    addElementToSource e (TransformationReactive ((root,es,links), t, (root',es',links'))) =
                                   TransformationReactive ((root,e:es,links), t, (root',es',links'))
    addLinkToSource l (TransformationReactive ((root,es,links), t, (root',es',links'))) =
                                   let msu = (root,es,l:links)
                                       [ne] = image t (computeReverseBinding msu l)
                                   in TransformationReactive (msu, t, (root',delete ne es',links'))
    apply (TransformationReactive (m,t,_)) = TransformationReactive (initialize t m)

type Transformation = Relation

-- we resolve every time because we don't compute primitive attributes and elements are created by different rules
-- we compute the full binding (all the links)
-- transformation -> transformationSourceModel -> targetLinkSource -> targetLinks
bindingApplication :: Transformation -> Model -> Element -> SetOf Link
bindingApplication t m@(_,_,links) targetLinkSource = -- trace (show t ++ show m ++ show targetLinkSource ++ show (inverseImage t [targetLinkSource])) $
    targetLinkSource `crossProduct` (image t . computeBinding m . inverseImage t) [targetLinkSource]

-- EXAMPLE

-- Metamodel

data Element = A | B | C | D | E | F deriving (Show,Eq,Enum) -- distinguish source and target element types?

ts0 :: TransformationStrict
ts0 = TransformationStrict ((A,[A,B],[(A,B)]), tr, undefined)
tl0 :: TransformationLazy
tl0 = TransformationLazy ((A,[A,B],[(A,B)]), tr, undefined)
ti0 :: TransformationIncremental
ti0 = TransformationIncremental ((A,[A,B],[(A,B)]), tr, undefined)
tr0 :: TransformationReactive
tr0 = TransformationReactive ((A,[A,B],[(A,B)]), tr, undefined)

-- sourceModel -> matchedElements -> resultingSourceElements
computeBinding :: Model -> SetOf Element -> SetOf Element
computeReverseBinding :: Model -> Link -> SetOf Element

-- Transformation

tr :: Transformation
tr = [(A,C),(B,D),(E,F)]
-- computeBinding (_,_,links) = inverseImage links
computeBinding (_,_,links) = image links
computeReverseBinding (_,_,_) (from, to) = [from]

updateSource :: TransformationI m => m -> m
updateSource ts = addLinkToSource (A, E) (addElementToSource E ts)

mStrict :: TransformationStrict
mStrict = apply ts0
mLazy :: TransformationLazy
mLazy = apply tl0
mIncremental :: TransformationIncremental
mIncremental = apply ti0
mReactive :: TransformationReactive
mReactive = apply tr0

mStrict' :: TransformationStrict
mStrict' = apply $ updateSource $ apply ts0
mLazy' :: TransformationLazy
mLazy' = apply $ updateSource $ apply tl0
mIncremental' :: TransformationIncremental
mIncremental' = updateSource $ apply ti0
mReactive' :: TransformationReactive
mReactive' = updateSource $ apply tr0

main::IO()
main = do
    print $ show $ fst $ getN 3 mStrict
    print $ show $ fst $ getN 3 mLazy
    print $ show $ fst $ getN 3 mIncremental
    print $ show $ fst $ getN 3 mReactive

    print $ show $ fst $ getN 3 mStrict'
    print $ show $ fst $ getN 3 mLazy'
    print $ show $ fst $ getN 3 mIncremental'
    print $ show $ fst $ getN 3 mReactive'

    test1

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


newtype Config = Config { unConfig::(Model,Transformation) } deriving (Show,Eq)

configs :: Gen Config
configs = do
  -- take a subset of at leat two elements and split it in two
  (elementS,elementT) <- elements $ concat $ map split $ filter (\es -> length es>=2) $ subSet [A .. F]
  -- a subset of all possible source links
  linkS <- elements $ subSet $ allLinks elementS
  let rootS = head elementS -- source root is always the first element
      rootT = head elementT -- target root is always the first element
  -- a subset of all possible transfo (does not include root mapping)
  transfo <- elements $ subSet $ allTransfos (tail elementS) elementT
  -- a configuration
  return $ Config ((rootS,elementS,linkS),(rootS,rootT):transfo)

instance Arbitrary Config where
    arbitrary = configs

assertion config =
    let (mS,t) = unConfig config
        c = (mS,t,undefined)
    in --valid mS t ==>
       length (nub [ fst $ getN 3 $ apply $ TransformationStrict c
                   , fst $ getN 3 $ apply $ TransformationLazy c 
                   , fst $ getN 3 $ apply $ TransformationIncremental c
                   , fst $ getN 3 $ apply $ TransformationReactive c]) == 1

test1 = verboseCheckWith stdArgs { maxSuccess = 10 } assertion
test2 = verboseCheck assertion

-- for debugging purpose only (generated source models and transformations are valid by construction)
valid :: Model -> Transformation -> Bool
valid (root, es, links) t = elem root es && length es == length (nub es) && all (`elem` es) (map fst links) && all (`elem` es) (map snd links) &&
                            all (`notElem` es) (map snd t) && not (null t) && root `elem` (map fst t)
