-- Abstract (semantics-like) version
module Main where

import Data.Tuple
import Data.List

-- MATHS

type Set a = [a]

--distinguish relation and function? and bijection?
type Relation = Set (Element,Element)

image :: Relation -> Set Element -> Set Element
image r es = nub (concatMap (image1 r) es)
    where image1 :: Relation -> Element -> Set Element
          image1 r1 e = [ e2 | (e1,e2) <- r1, e1==e ]

inverseImage :: Relation -> Set Element -> Set Element
inverseImage = image . map swap

crossProduct :: Element -> Set Element -> Relation
crossProduct e1 es2 = [ (e1,e2) | e2 <- es2 ]

fixedPoint :: Eq a => (a -> a) -> a -> [a]
fixedPoint f a | f a == a  = [a]
             | otherwise = a:fixedPoint f (f a)

-- MODELS

type Link = (Element,Element)

type LinkSet = Set Link

-- (root, all elements, all links)
type Model = (Element,Set Element,LinkSet)

type Transformation = Relation

-- we resolve every time because we don't compute primitive attributes and elements are created by different rules
-- we compute the full binding (all the links)
-- transformation -> transformationSourceModel -> targetLinkSource -> targetLinks
bindingApplication :: Transformation -> Model -> Element -> LinkSet
bindingApplication t (_,_,links) targetLinkSource =
    targetLinkSource `crossProduct` (image t . inverseImage links . inverseImage t) [targetLinkSource]

-- STRICT

-- model strict transformation
-- it obtains the transformed root and all transformed elements
matchingPhase :: Transformation -> Model -> (Element,Set Element)
matchingPhase t (root,elements,_) = (head (image t [root]),image t elements)

applyPhase :: Transformation -> Model -> Set Element -> LinkSet
applyPhase t m = concatMap (bindingApplication t m)

transformationStrict :: Transformation -> Model -> Model
transformationStrict t m =
    let (targetRoot,targetElements) = matchingPhase t m
        targetLinks = applyPhase t m targetElements
    in (targetRoot,targetElements,targetLinks)

-- call a 'get' (i.e. navigate) on all the links outgoing from all the elements in the set
get :: (Set Element,Model) -> (Set Element,Model)
get (es,m@(_,_,links)) = (image links es,m)

-- LAZY

type ModelL = (Model,Transformation,Model)

initialize :: Transformation -> Model -> ModelL
initialize t m = (m,t,(rootT,[],[]))
     where (root,_,_) = m
           [rootT] = image t [root]

-- call a 'get' (i.e. navigate) lazily on all the links outgoing from one element, by computing the element if necessary
get1L :: ModelL -> Element -> (Set Element, ModelL)
get1L mL@(mS,t,mT@(rootT,elementsT,linksT)) e | e `elem` elementsT = (fst (get ([e],mT)),mL)
                                              | otherwise
    = let ls = bindingApplication t mS e
          mT1 = (rootT,e:elementsT,ls++linksT)
          mL2 = (mS,t,mT1)
      in (fst (get ([e],mT1)),mL2)

-- get1L on a set of elements
getL :: (Set Element,ModelL) -> (Set Element, ModelL)
getL (  [],mL0) = ([],mL0)
getL (e:es,mL0) = let (est1,mL1) = get1L mL0 e
                      (est2,mL2) = getL (es,mL1)
                  in (est1 `union` est2,mL2)

-- EXAMPLE

-- Metamodel

data Element = A | B | C | D | E | F deriving (Show,Eq) -- distinguish source and target element types?

-- Source Model

m0 :: Model
m0 = (B,[A,B],[(A,B)])

-- Transformation

t1 :: Transformation
t1 = [(A,C),(B,D)]

-- Transformation launch configuration (Strict)
m1 :: Model
m1 = transformationStrict t1 m0

-- Requests (Strict)
traversal :: (Set Element,Model) -> [(Set Element,Model)]
traversal = fixedPoint get

-- Source model navigation
test0 :: [(Set Element, Model)]
test0 = traversal ([root],m0)
        where (root,_,_) = m0

-- Strictly transformed target model
test1 :: [Set Element]
test1 = map fst (traversal ([root],m1))
        where (root,_,_) = m1


-- Transformation launch configuration (lazy)
m2 :: ModelL
m2 = initialize t1 m0

traversalL :: (Set Element,ModelL) -> [(Set Element,ModelL)]
traversalL = fixedPoint getL

-- Lazily transformed target model
test2 :: [Set Element]
test2 = map fst (traversalL ([rootT],m2))
        where (_,_,(rootT,_,_)) = m2

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

-- Adds (strictly) element/link to Model
addElementS :: Element -> Model -> Model
addElementS e (rootS,elementsS,linksS) = (rootS,e:elementsS,linksS)

addLinkS :: Link -> Model -> Model
addLinkS l (rootS,elementsS,linksS) = (rootS,elementsS,l:linksS)

t2 :: Transformation
t2 = t1 ++ [(E, F)]

mu :: Model
mu = addLinkS (E, A) (addElementS E m0)

-- result of the strict transformation
mtu :: Model
mtu = transformationStrict t2 mu

test3 :: [Set Element]
test3 = map fst (traversal ([root],mtu))
        where (root,_,_) = mtu

mtui :: Model
mtui = mtui1
        where (_,_,mtui1) = addLinkU (E,A) (addElementU E (m0, t2, m1))

test4 :: [Set Element]
test4 = map fst (traversal ([root],mtui))
        where (root,_,_) = mtui

-- REACTIVE




main::IO()
main = print (test3 == test4)