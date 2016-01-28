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
    addLinkToSource (from, to) (TransformationIncremental ((root,es,links), t, (root',es',links'))) =
                                   let msu = (root,es,(from, to):links)
                                       ls = bindingApplication t msu (head (image t [from]))
                                   in TransformationIncremental (msu, t, (root',es',ls++links'))
    apply (TransformationIncremental (m, t, _))  =
            let (targetRoot,targetElements) = matchingPhase t m
                targetLinks = applyPhase t m targetElements
            in TransformationIncremental (m, t, (targetRoot,targetElements,targetLinks))


newtype TransformationReactive = TransformationReactive (Model, Transformation, Model) deriving Show
instance TransformationI TransformationReactive where
    getRootFromTarget(TransformationReactive (_,_,(rootT,_,_))) = rootT
    getFromTarget mL@(TransformationReactive (mS,t,mT@(rootT,elementsT,linksT))) e | e `elem` elementsT = (image linksT [e],mL)
                                                                                   | otherwise
                 = let ls = bindingApplication t mS e
                       mT1 = (rootT,e:elementsT,ls++linksT)
                   in (image (ls++linksT) [e],TransformationReactive (mS, t, mT1))
    addElementToSource e (TransformationReactive ((root,es,links), t, (root',es',links'))) =
                                   TransformationReactive ((root,e:es,links), t, (root',es',links'))
    addLinkToSource (from, to) (TransformationReactive ((root,es,links), t, (root',es',links'))) =
                                   let msu = (root,es,(from, to):links)
                                       [ne] = image t [from]
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

data Element = A | B | C | D | E | F deriving (Show,Eq) -- distinguish source and target element types?

tr :: Transformation
tr = [(A,C),(B,D),(E,F)]

ts0 :: TransformationStrict
ts0 = TransformationStrict ((A,[A,B],[(A,B)]), tr, undefined)
tl0 :: TransformationLazy
tl0 = TransformationLazy ((A,[A,B],[(A,B)]), tr, undefined)
ti0 :: TransformationIncremental
ti0 = TransformationIncremental ((A,[A,B],[(A,B)]), tr, undefined)
tr0 :: TransformationReactive
tr0 = TransformationReactive ((A,[A,B],[(A,B)]), tr, undefined)

-- Transformation

-- sourceModel -> matchedElements -> resultingSourceElements
computeBinding :: Model -> SetOf Element -> SetOf Element
computeBindingTraces :: Model -> SetOf Element -> SetOf Element

-- computeBinding (_,_,links) = inverseImage links
computeBinding (_,_,links) = image links

computeBindingTraces (_,_,links) elements = nub (elements ++ image links elements)
traces :: Transformation -> Element -> SetOf Element
traces t e = image t [e]

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
