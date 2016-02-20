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

module Semantics where

import Data.Tuple
import Data.List

-- # MODEL

-- (root, all elements, all links)
-- in lazy semantics (root, all elements with valid outgoing references, all links from valid elements)
type Model = (Element,SetOf Element,SetOf Link)

data Element = A | B | C | D | E | F deriving (Show,Eq,Enum) -- distinguish source and target element types?

type Link = (Element,Element)

type SetOf a = [a]

-- # TRANSFORMATION

-- Transformation = (Relation, computeBinding, computeReverseBinding)
-- computeBinding :: sourceModel -> matchedElements -> resultingSourceElements
type Transformation = (Relation, Model -> SetOf Element -> SetOf Element, Model -> Link -> SetOf Element)
--distinguish relation and function? and bijection?
type Relation = SetOf (Element,Element)

image :: Transformation -> SetOf Element -> SetOf Element
image (r, _, _) = imageR r

inverseImage :: Transformation -> SetOf Element -> SetOf Element
inverseImage (r, _, _) = inverseImageR r

imageR :: Relation -> SetOf Element -> SetOf Element
imageR r es = nub (concatMap (image1 r) es)
    where image1 :: Relation -> Element -> SetOf Element
          image1 r1 e = [ e2 | (e1,e2) <- r1, e1==e ]

inverseImageR :: Relation -> SetOf Element -> SetOf Element
inverseImageR = imageR . map swap

crossProductR :: Element -> SetOf Element -> Relation
crossProductR e1 es2 = [ (e1,e2) | e2 <- es2 ]

-- # TRANSFORMATION SYSTEM

class TransformationSystem m where  -- MONADIC (State) ?
    apply :: m -> m -- should be implicit in the constructor ?
    getFromTarget :: m -> Element -> (SetOf Element,m)
    getRootFromTarget :: m -> Element
    addElementToSource :: Element -> m -> m
    addLinkToSource :: Link -> m -> m

getAllFromTarget :: TransformationSystem m => m -> SetOf Element -> (SetOf Element, m)
getAllFromTarget m0 [] = ([],m0)
getAllFromTarget m0 (e:es) = let (est1,m1) = getFromTarget m0 e
                                 (est2,m2) = getAllFromTarget m1 es
                             in (est1 `union` est2,m2)

getNFromTarget :: TransformationSystem m => Int -> m -> (SetOf Element, m)
getNFromTarget 0 m = ([getRootFromTarget m], m)
getNFromTarget n m = let (es', m') = getNFromTarget (n-1) m
                         (es'', m'') = getAllFromTarget m' es'
                     in (union es' es'', m'')

-- # STRICT TRANSFORMATION SYSTEM

newtype TransformationStrict = TransformationStrict (Model,Transformation,Model)
instance TransformationSystem TransformationStrict where
    getRootFromTarget (TransformationStrict (_,_,(root,_,_))) = root
    getFromTarget m@(TransformationStrict (_,_,(_,_,links))) e = (imageR links [e],m)
    addElementToSource e (TransformationStrict ((root,es,links),t,m')) = TransformationStrict ((root,e:es,links),t,m')
    addLinkToSource l (TransformationStrict ((rootS,elementsS,linksS),t,m')) = TransformationStrict ((rootS,elementsS,l:linksS), t, m')
    apply (TransformationStrict (m, t, _))  = TransformationStrict (m, t, strictApply t m)

strictApply :: Transformation -> Model -> Model
strictApply t m = let (targetRoot,targetElements) = matchingPhase t m
                      targetLinks = applyPhase t m targetElements
                  in  (targetRoot,targetElements,targetLinks)
                  where
                      -- it obtains the transformed root and all transformed elements
                      matchingPhase :: Transformation -> Model -> (Element,SetOf Element)
                      matchingPhase t (root,elements,_) = (head (image t [root]),image t elements)

                      applyPhase :: Transformation -> Model -> SetOf Element -> SetOf Link
                      applyPhase t m = concatMap (bindingApplication t m)

-- we resolve every time because we don't compute primitive attributes and elements are created by different rules
-- we compute the full binding (all the links)
-- transformation -> transformationSourceModel -> targetLinkSource -> targetLinks
bindingApplication :: Transformation -> Model -> Element -> SetOf Link
bindingApplication t@(r,cb,crb) m@(_,_,links) targetLinkSource = -- trace (show t ++ show m ++ show targetLinkSource ++ show (inverseImage t [targetLinkSource])) $
    targetLinkSource `crossProductR` (image t . cb m . inverseImage t) [targetLinkSource]

-- # LAZY TRANSFORMATION SYSTEM

newtype TransformationLazy = TransformationLazy (Model,Transformation,Model)
instance TransformationSystem TransformationLazy where
    getRootFromTarget (TransformationLazy (_,_,(rootT,_,_))) = rootT
    getFromTarget mL@(TransformationLazy (mS,t,mT@(rootT,elementsT,linksT))) e | e `elem` elementsT = (imageR linksT [e],mL)
                                                                               | otherwise
             = let ls = bindingApplication t mS e
                   mT1 = (rootT,e:elementsT,ls++linksT)
               in (imageR (ls++linksT) [e],TransformationLazy (mS, t, mT1))
    addElementToSource e (TransformationLazy ((root,es,links),t,m')) = TransformationLazy ((root,e:es,links),t,m')
    addLinkToSource l (TransformationLazy ((rootS,elementsS,linksS),t,m')) = TransformationLazy ((rootS,elementsS,l:linksS), t, m')
    apply (TransformationLazy (m,t,_)) = TransformationLazy (initialize t m)

initialize :: Transformation -> Model -> (Model,Transformation,Model)
initialize t m = (m,t,(rootT,[],[]))
     where (root,_,_) = m
           [rootT] = image t [root]

-- # INCREMENTAL TRANSFORMATION SYSTEM

newtype TransformationIncremental = TransformationIncremental (Model, Transformation, Model)
instance TransformationSystem TransformationIncremental where
    getRootFromTarget(TransformationIncremental (_,_,(rootT,_,_))) = rootT
    getFromTarget m@(TransformationIncremental (_, _, (_,_,links))) e = (imageR links [e],m)
    addElementToSource e (TransformationIncremental ((root,es,links), t, (root',es',links'))) =
                                   let [ne] = image t [e]
                                   in TransformationIncremental ((root,e:es,links), t, (root',ne:es',links'))
    addLinkToSource l (TransformationIncremental ((root,es,links), t@(_,_,crb), (root',es',links'))) =
                                   let msu = (root,es,l:links)
                                       ls = foldr union [] $ map (bindingApplication t msu) (image t (crb msu l))
                                   in TransformationIncremental (msu, t, (root',es',ls++links'))
    apply (TransformationIncremental (m, t, _)) = TransformationIncremental (m, t,  strictApply t m)

-- # REACTIVE TRANSFORMATION SYSTEM

newtype TransformationReactive = TransformationReactive (Model, Transformation, Model)
instance TransformationSystem TransformationReactive where
    getRootFromTarget(TransformationReactive (_,_,(rootT,_,_))) = rootT
    getFromTarget mL@(TransformationReactive (mS,t,mT@(rootT,elementsT,linksT))) e | e `elem` elementsT = (imageR linksT [e],mL)
                                                                                   | otherwise
                 = let ls = bindingApplication t mS e
                       mT1 = (rootT,e:elementsT,ls++linksT)
                   in (imageR (ls++linksT) [e],TransformationReactive (mS, t, mT1))
    addElementToSource e (TransformationReactive ((root,es,links), t, (root',es',links'))) =
                                   TransformationReactive ((root,e:es,links), t, (root',es',links'))
    addLinkToSource l (TransformationReactive ((root,es,links), t@(_,_,crb), (root',es',links'))) =
                                   let msu = (root,es,l:links)
                                       [ne] = image t (crb msu l)
                                   in TransformationReactive (msu, t, (root',delete ne es',links'))
    apply (TransformationReactive (m,t,_)) = TransformationReactive (initialize t m)