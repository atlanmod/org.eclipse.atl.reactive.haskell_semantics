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

fixedPoint :: Eq a => (a -> a) -> a -> [a]
fixedPoint f a | f a == a  = [a]
             | otherwise = a:fixedPoint f (f a)
-- MODELS

type Link = (Element,Element)

-- (root, all elements, all links)
-- in lazy semantics (root, all elements with valid outgoing references, all links from valid elements)
type Model = (Element,SetOf Element,SetOf Link)

type Transformation = Relation

-- sourceModel -> matchedElements -> resultingSourceElements
computeBinding :: Model -> SetOf Element -> SetOf Element

-- we resolve every time because we don't compute primitive attributes and elements are created by different rules
-- we compute the full binding (all the links)
-- transformation -> transformationSourceModel -> targetLinkSource -> targetLinks
bindingApplication :: Transformation -> Model -> Element -> SetOf Link
bindingApplication t m@(_,_,links) targetLinkSource =
    targetLinkSource `crossProduct` (image t . computeBinding m . inverseImage t) [targetLinkSource]

-- type Transformation a = a -> a
-- STRICT

-- model strict transformation
-- it obtains the transformed root and all transformed elements
matchingPhase :: Transformation -> Model -> (Element,SetOf Element)
matchingPhase t (root,elements,_) = (head (image t [root]),image t elements)

applyPhase :: Transformation -> Model -> SetOf Element -> SetOf Link
applyPhase t m = concatMap (bindingApplication t m)

transformationStrict :: Transformation -> Model -> Model
transformationStrict t m =
    let (targetRoot,targetElements) = matchingPhase t m
        targetLinks = applyPhase t m targetElements
    in (targetRoot,targetElements,targetLinks)

-- call a 'get' (i.e. navigate) on all the links outgoing from all the elements in the set
get :: (SetOf Element,Model) -> (SetOf Element,Model)
get (es,m@(_,_,links)) = (image links es,m)

-- Adds (strictly) element/link to Model
addElementS :: Element -> Model -> Model
addElementS e (rootS,elementsS,linksS) = (rootS,e:elementsS,linksS)

addLinkS :: Link -> Model -> Model
addLinkS l (rootS,elementsS,linksS) = (rootS,elementsS,l:linksS)

-- LAZY

type ModelL = (Model,Transformation,Model)

initializeL :: Transformation -> Model -> ModelL
initializeL t m = (m,t,(rootT,[],[]))
     where (root,_,_) = m
           [rootT] = image t [root]

-- call a 'get' (i.e. navigate) lazily on all the links outgoing from one element, by computing the element if necessary
get1L :: ModelL -> Element -> (SetOf Element, ModelL)
get1L mL@(mS,t,mT@(rootT,elementsT,linksT)) e | e `elem` elementsT = (fst (get ([e],mT)),mL)
                                              | otherwise
    = let ls = bindingApplication t mS e
          mT1 = (rootT,e:elementsT,ls++linksT)
          mL2 = (mS,t,mT1)
      in (fst (get ([e],mT1)),mL2)

-- get1L on a set of elements
getL :: (SetOf Element,ModelL) -> (SetOf Element, ModelL)
getL (  [],mL0) = ([],mL0)
getL (e:es,mL0) = let (est1,mL1) = get1L mL0 e
                      (est2,mL2) = getL (es,mL1)
                  in (est1 `union` est2,mL2)

-- INCREMENTAL
-- Adds element/link to Source Model (and updates the corresponding target model)
addElementU :: Element -> (Model, Transformation, Model) -> (Model, Transformation, Model)
addElementU e (ms, t, mt) =
        let [ne] = image t [e]
        in (addElementS e ms, t, addElementS ne mt)

-- this works only in our case where we just invert links
addLinkU :: Link -> (Model, Transformation, Model) -> (Model, Transformation, Model)
addLinkU (from, to) (ms, t, mt) =
        let msu = addLinkS (from, to) ms
            ls = bindingApplication t msu (head (image t [to]))
        in (msu, t, foldr addLinkS mt ls)

-- REACTIVE

initializeR :: Transformation -> Model -> ModelL
initializeR = initializeL

--get1R :: ModelL -> Element -> (SetOf Element, ModelL)

--getR :: (SetOf Element,ModelL) -> (SetOf Element, ModelL)

-- nothing happens on the target
addElementR :: Element -> ModelL -> ModelL
addElementR e (ms, t, mt) =
    (addElementS e ms, t, mt)

addLinkR :: Link -> ModelL -> ModelL
addLinkR (from, to) (ms, t, mt) =
    let msu = addLinkS (from, to) ms
    in (msu, t, )

-- isInvolvedIn :: Element ->


















-- EXAMPLE

-- Metamodel

data Element = A | B | C | D | E | F deriving (Show,Eq) -- distinguish source and target element types?

-- Source Model

m0 :: Model
m0 = (B,[A,B],[(A,B)])

-- Transformation

t1 :: Transformation
t1 = [(A,C),(B,D)]

computeBinding (_,_,links) = image links

-- Transformation launch configuration (Strict)
m1 :: Model
m1 = transformationStrict t1 m0

-- Requests (Strict)
traversal :: (SetOf Element,Model) -> [(SetOf Element,Model)]
traversal = fixedPoint get

-- Source model navigation
test0 :: [(SetOf Element, Model)]
test0 = traversal ([root],m0)
        where (root,_,_) = m0

-- Strictly transformed target model
test1 :: [SetOf Element]
test1 = map fst (traversal ([root],m1))
        where (root,_,_) = m1


-- Transformation launch configuration (lazy)
m2 :: ModelL
m2 = initializeL t1 m0

traversalL :: (SetOf Element,ModelL) -> [(SetOf Element,ModelL)]
traversalL = fixedPoint getL

-- Lazily transformed target model
test2 :: [SetOf Element]
test2 = map fst (traversalL ([rootT],m2))
        where (_,_,(rootT,_,_)) = m2

-- Incremental example
t2 :: Transformation
t2 = t1 ++ [(E, F)]

mu :: Model
mu = addLinkS (E, A) (addElementS E m0)

-- result of the strict transformation
mtu :: Model
mtu = transformationStrict t2 mu

test3 :: [SetOf Element]
test3 = map fst (traversal ([root],mtu))
        where (root,_,_) = mtu

mtui :: Model
mtui = mtui1
        where (_,_,mtui1) = addLinkU (E,A) (addElementU E (m0, t2, m1))

test4 :: [SetOf Element]
test4 = map fst (traversal ([root],mtui))
        where (root,_,_) = mtui



main::IO()
main = print (test3 == test4)