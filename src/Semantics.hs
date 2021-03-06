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

import           Data.List
import           Data.Tuple

-- # MODEL

-- (root, all elements, all links)
-- in lazy semantics (root, all elements with valid outgoing references, all links from valid elements)
type Model = (Element,SetOf Element,SetOf Link)

deleteElement :: Element -> Model -> Model
deleteElement e (root,es,links) | e /= root = (root, filter (e/=) es ,filter (\ (s,t) -> s/=e && t/=e) links)

data Element = A | B | C | D | E | F deriving (Show,Eq,Enum) -- distinguish source and target element types?

type Link = (Element,Element)

type SetOf a = [a]

-- # TRANSFORMATION

-- Transformation = (Relation, computeBinding, computeReverseBinding)
-- computeBinding :: sourceModel -> matchedElements -> resultingSourceElements
type Transformation = (Relation, Model -> SetOf Element -> SetOf Element, Model -> Link -> SetOf Element)
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

-- # TRANSFORMATION SYSTEM

class TransformationSystem ts where
    apply :: ts -> ts
    getFromTarget :: ts -> Element -> (SetOf Element,ts)
    getRootFromTarget :: ts -> Element
    addElementToSource :: Element -> ts -> ts
    deleteElementFromSource :: Element -> ts -> ts
    addLinkToSource :: Link -> ts -> ts

getAllFromTarget :: TransformationSystem ts => ts -> SetOf Element -> (SetOf Element, ts)
getAllFromTarget ts0 [] = ([],ts0)
getAllFromTarget ts0 (e:es) = let (est1,ts1) = getFromTarget ts0 e
                                  (est2,ts2) = getAllFromTarget ts1 es
                              in (est1 `union` est2,ts2)

getNFromTarget :: TransformationSystem ts => Int -> ts -> (SetOf Element, ts)
getNFromTarget 0 ts = ([getRootFromTarget ts], ts)
getNFromTarget n ts = let (es', ts') = getNFromTarget (n-1) ts
                          (es'', ts'') = getAllFromTarget ts' es'
                      in (es' `union` es'', ts'')

-- # STRICT TRANSFORMATION SYSTEM

newtype TransformationStrict = TransformationStrict (Model,Transformation,Model)
instance TransformationSystem TransformationStrict where
    getRootFromTarget (TransformationStrict (_,_,(root,_,_))) = root
    getFromTarget m@(TransformationStrict (_,_,(_,_,links))) e = (image links [e],m)
    addElementToSource e (TransformationStrict ((root,es,links),t,m')) = TransformationStrict ((root,e:es,links),t,m')
    deleteElementFromSource e (TransformationStrict (m,t,m')) = TransformationStrict (deleteElement e m,t,m')
    addLinkToSource l (TransformationStrict ((rS,eS,lS),t,m')) = TransformationStrict ((rS,eS,l:lS), t, m')
    apply (TransformationStrict (m, t, _))  = TransformationStrict (m, t, strictApply t m)

strictApply :: Transformation -> Model -> Model
strictApply t m = let (targetRoot,targetElements) = matchPhase t m
                      targetLinks = applyPhase t m targetElements
                  in  (targetRoot,targetElements,targetLinks)
                  where
                      -- it obtains the transformed root and all transformed elements
                      matchPhase :: Transformation -> Model -> (Element,SetOf Element)
                      matchPhase (tr,_,_) (root,elements,_) = (head (image tr [root]),image tr elements)

                      applyPhase :: Transformation -> Model -> SetOf Element -> SetOf Link
                      applyPhase tr md = concatMap (bindingApplication tr md)

-- we resolve every time because we don't compute primitive attributes and elements are created by different rules
-- we compute the full binding (all the links)
-- transformation -> transformationSourceModel -> targetLinkSource -> targetLinks
bindingApplication :: Transformation -> Model -> Element -> SetOf Link
bindingApplication (r,cb,_) m targetLinkSource =
-- trace (show t ++ show m ++ show targetLinkSource ++ show (inverseImage t [targetLinkSource])) $
    targetLinkSource `crossProduct` (image r . cb m . inverseImage r) [targetLinkSource]

-- # LAZY TRANSFORMATION SYSTEM

newtype TransformationLazy = TransformationLazy (Model,Transformation,Model)
instance TransformationSystem TransformationLazy where
    getRootFromTarget (TransformationLazy (_,_,(rootT,_,_))) = rootT
    getFromTarget mL@(TransformationLazy (mS,t,(rootT,elementsT,linksT))) e =
        if e `elem` elementsT then (image linksT [e],mL)
        else let ls = bindingApplication t mS e
                 mT1 = (rootT,e:elementsT,ls++linksT)
             in (image (ls++linksT) [e],TransformationLazy (mS, t, mT1))
    addElementToSource e (TransformationLazy ((root,es,links),t,m')) = TransformationLazy ((root,e:es,links),t,m')
    deleteElementFromSource e (TransformationLazy (m,t,m')) = apply (TransformationLazy (deleteElement e m,t,m'))
    addLinkToSource l (TransformationLazy ((rS,eS,lS),t,m')) = TransformationLazy ((rS,eS,l:lS), t, m')
    apply (TransformationLazy (m,t,_)) = TransformationLazy (initialize t m)

initialize :: Transformation -> Model -> (Model,Transformation,Model)
initialize t@(r,_,_) m = (m,t,(rootT,[],[]))
     where (root,_,_) = m
           [rootT] = image r [root]

-- # INCREMENTAL TRANSFORMATION SYSTEM

newtype TransformationIncremental = TransformationIncremental (Model, Transformation, Model)
instance TransformationSystem TransformationIncremental where
    getRootFromTarget(TransformationIncremental (_,_,(rootT,_,_))) = rootT
    getFromTarget m@(TransformationIncremental (_, _, (_,_,links))) e = (image links [e],m)
    addElementToSource e (TransformationIncremental ((root,es,links), t@(r,_,_), (root',es',links'))) =
        let [ne] = image r [e]
        in TransformationIncremental ((root,e:es,links), t, (root',ne:es',links'))
    deleteElementFromSource e (TransformationIncremental (ms, t@(r,_,_), mt)) =
            let [ne] = image r [e]
            in TransformationIncremental (deleteElement e ms, t, deleteElement ne mt)
    addLinkToSource l (TransformationIncremental ((root,es,links), t@(r,_,crb), (root',es',links'))) =
        let msu = (root,es,l:links)
            ls = foldr (union . bindingApplication t msu) [] (image r (crb msu l))
        in TransformationIncremental (msu, t, (root',es',ls++links'))
    apply (TransformationIncremental (m, t, _)) = TransformationIncremental (m, t,  strictApply t m)

-- # REACTIVE TRANSFORMATION SYSTEM

newtype TransformationReactive = TransformationReactive (Model, Transformation, Model)
instance TransformationSystem TransformationReactive where
    getRootFromTarget(TransformationReactive (_,_,(rootT,_,_))) = rootT
    getFromTarget mL@(TransformationReactive (mS,t,(rootT,elementsT,linksT))) e =
        if e `elem` elementsT then (image linksT [e],mL)
        else let ls = bindingApplication t mS e
                 es2delete = image linksT [e] \\ image ls [e]
                 mT1 = (rootT,e:elementsT,ls++linksT)
                 mT2 = foldr deleteElement mT1 es2delete
             in (image (ls++linksT) [e],TransformationReactive (mS, t, mT2))
    addElementToSource e (TransformationReactive ((root,es,links), t, (root',es',links'))) =
        TransformationReactive ((root,e:es,links), t, (root',es',links'))
    deleteElementFromSource e (TransformationReactive (ms, t@(r,_,_), (root',es',links'))) =
                let [ne] = image r [e]
                in TransformationReactive (deleteElement e ms, t, (root', filter (\e ->  notElem (e, ne) links') es' ,links'))
    addLinkToSource l (TransformationReactive ((root,es,links), t@(r,_,crb), (root',es',links'))) =
        let msu = (root,es,l:links)
            [ne] = image r (crb msu l)
        in TransformationReactive (msu, t, (root',delete ne es',links'))
    apply (TransformationReactive (m,t,_)) = TransformationReactive (initialize t m)
