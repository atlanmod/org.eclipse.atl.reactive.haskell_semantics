module Main where
-- Abstract (semantics-like) version

import Data.Tuple
import Data.List

main::IO()
main = putStrLn (show (test1 == test2))

type Set a = [a]

--distinguish relation and function? and bijection?

type Relation = Set (Element,Element)

type Link = (Element,Element)

type LinkS = Set Link

-- (root, all elements, all links)
type Model = (Element,Set Element,LinkS)

type Transformation = Relation

-- image of the set
navigate :: Relation -> Set Element -> Set Element
navigate r es = nub (concat (map (navigate1 r) es))
    where navigate1 :: Relation -> Element -> Set Element
          navigate1 r e = [ e2 | (e1,e2) <- r, e1==e ]

-- we resolve every time because we don't compute primitive attributes and elements are created by different rules
-- we compute the full binding (all the links)
bindingApplication :: Transformation -> Model -> Element -> LinkS
bindingApplication t (root,elements,links) targetReferenceSource =
    targetReferenceSource `cross` ((navigate t) . (inverse links) . (inverse t)) [targetReferenceSource]

inverse :: Relation -> Set Element -> Set Element
inverse = navigate . (map swap)

fixPoint :: Eq a => (a -> a) -> a -> [a]
fixPoint f a | f a == a  = [a]
             | otherwise = a:fixPoint f (f a)

cross :: Element -> Set Element -> Relation
cross e1 es2 = [ (e1,e2) | e2 <- es2 ]

-- STRICT

-- model strict transformation
-- it obtains the transformed root and all transformed elements
matchingPhase :: Transformation -> Model -> (Element,Set Element)
matchingPhase t (root,elements,links) = (head (navigate t [root]),navigate t elements)

applyPhase :: Transformation -> Model -> Set Element -> LinkS
applyPhase t m es = concat (map (bindingApplication t m) es)

transformationStrict :: Transformation -> Model -> Model
transformationStrict t m =
    let (targetRoot,targetElements) = matchingPhase t m
        targetLinks = applyPhase t m targetElements
    in (targetRoot,targetElements,targetLinks)

-- call a 'get' (i.e. navigate) on all the links outgoing from all the elements in the set
get :: (Set Element,Model) -> (Set Element,Model)
get (es,m@(root,elements,links)) = (navigate links es,m)

-- LAZY

type ModelL = (Model,Transformation,Model)

initialize :: Transformation -> Model -> ModelL
initialize t m = (m,t,(rootT,[],[]))
     where (root,_,_) = m
           [rootT] = navigate t [root]

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
traversal em = fixPoint get em

-- Source model navigation
test0 = traversal ([root],m0)
        where (root,_,_) = m0

-- Strictly transformed target model
test1 = map fst (traversal ([root],m1))
        where (root,_,_) = m1


-- Transformation launch configuration (lazy)
m2 :: ModelL
m2 = initialize t1 m0

traversalL :: (Set Element,ModelL) -> [(Set Element,ModelL)]
traversalL em = fixPoint getL em

-- Lazily transformed target model
test2 = map fst (traversalL ([rootT],m2))
        where (_,_,(rootT,_,_)) = m2

addElement :: Element -> (Model, Transformation, Model) -> (Model, Transformation, Model)
addElement e (ms, t, mt) =
        let [ne] = navigate t [e]
        in (addElementS e ms, t, addElementS ne mt)

addLink :: Link -> (Model, Transformation, Model) -> (Model, Transformation, Model)
addLink (from, to) (ms, t, mt) =
        let ls = bindingApplication t ms (head (navigate t [to]))
        in (addLinkS (from, to) ms, t, foldr addLinkS mt ls)

addElementS :: Element -> Model -> Model
addElementS e (rootS,elementsS,linksS) = (rootS,e:elementsS,linksS)

addLinkS :: Link -> Model -> Model
addLinkS l (rootS,elementsS,linksS) = (rootS,elementsS,l:linksS)

t2 :: Transformation
t2 = t1 ++ [(E, F)]

mu :: Model
mu = addLinkS (E, A) (addElementS E m0)

mtu :: Model
mtu = transformationStrict t2 mu

imu :: (Model, Transformation, Model)
imu = addLink (E,A) (addElement E (m0, t2, m1))
