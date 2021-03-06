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

--fixedPoint :: Eq a => ((a,state) -> (a,state)) -> (a, state) -> [a],
--fixedPoint f a | f a == a  = [a]
--               | otherwise = a:fixedPoint f (f a)

-- MODELS

type Link = (Element,Element)

-- (root, all elements, all links)
-- in lazy semantics (root, all elements with valid outgoing references, all links from valid elements)
type Model = (Element,SetOf Element,SetOf Link)

class ModelI m where
    getRoot :: m -> Element
    get1 :: m -> Element -> (SetOf Element,m)
    addElement :: Element -> m -> m
    addLink :: Link -> m -> m
    transform :: Transformation -> ModelStrict -> m

get :: ModelI m => m -> SetOf Element -> (SetOf Element, m)
get m0 [] = ([],m0)
get m0 (e:es) = let (est1,m1) = get1 m0 e
                    (est2,m2) = get m1 es
                in (est1 `union` est2,m2)

getN :: ModelI m => Int -> m -> (SetOf Element, m)
getN 0 m = ([getRoot m], m)
getN n m = let (es', m') = getN (n-1) m
               (es'', m'') = get m' es'
           in (union es' es'', m'')

class ModelI m => TransformedModelI m where
    addElementToSource :: Element -> m -> m
    addLinkToSource :: Link -> m -> m

-- data ModelStrict = ModelStrict Model deriving Show
data ModelStrict = ModelStrict Model deriving Show
instance ModelI ModelStrict where
    getRoot (ModelStrict (root,_,_)) = root
    get1 m@(ModelStrict (_,_,links)) e = (image links [e],m)
    addElement e (ModelStrict (root,es,links)) = ModelStrict (root,e:es,links)
    addLink l (ModelStrict (rootS,elementsS,linksS)) = ModelStrict (rootS,elementsS,l:linksS)
    transform t (ModelStrict m)  =
        let (targetRoot,targetElements) = matchingPhase t m
            targetLinks = applyPhase t m targetElements
        in ModelStrict (targetRoot,targetElements,targetLinks)

data ModelLazy = ModelLazy (Model,Transformation,Model) deriving Show
instance ModelI ModelLazy where
    getRoot (ModelLazy (_,_,(rootT,_,_))) = rootT
    get1 mL@(ModelLazy (mS,t,mT@(rootT,elementsT,linksT))) e | e `elem` elementsT = (fst (get (ModelStrict mT) [e]),mL)
                                                             | otherwise
             = let ls = bindingApplication t mS e
                   mT1 = (rootT,e:elementsT,ls++linksT)
                   mL2 = (mS,t,mT1)
               in (fst (get (ModelStrict mT1) [e]),ModelLazy mL2)
    addElement e m = undefined
    addLink l m = undefined
    transform t (ModelStrict m) = ModelLazy (initialize t m)

initialize :: Transformation -> Model -> (Model,Transformation,Model)
initialize t m = (m,t,(rootT,[],[]))
     where (root,_,_) = m
           [rootT] = image t [root]

--instance TransformedModelI ModelLazy where
--    addElementToSource e m = undefined
--    addLinkToSource l m = undefined

data ModelIncremental = ModelIncremental (ModelStrict, Transformation, ModelStrict) deriving Show
instance ModelI ModelIncremental where
    getRoot(ModelIncremental (_,_,(ModelStrict (rootT,_,_)))) = rootT
    get1 m@(ModelIncremental (_, _, (ModelStrict (_,_,links)))) e = (image links [e],m)
    addElement e m = undefined
    addLink l m = undefined
    transform t m =
        let m1 = transform t m
        in ModelIncremental (m, t, m1)
instance TransformedModelI ModelIncremental where
    addElementToSource e (ModelIncremental (ms, t, mt)) =
                               let [ne] = image t [e]
                               in ModelIncremental (addElement e ms, t, addElement ne mt)
    addLinkToSource (from, to) (ModelIncremental (ms, t, mt)) =
                                  let (ModelStrict msu) = addLink (from, to) ms
                                      ls = bindingApplication t msu (head (image t [to]))
                                  in ModelIncremental ((ModelStrict msu), t, foldr addLink mt ls)

type Transformation = Relation

-- sourceModel -> matchedElements -> resultingSourceElements
computeBinding :: Model -> SetOf Element -> SetOf Element
computeBindingTraces :: Model -> SetOf Element -> SetOf Element

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

--transformationStrict :: Transformation -> ModelStrict -> ModelStrict
--transformationStrict t (ModelStrict m)  =
--    let (targetRoot,targetElements) = matchingPhase t m
--        targetLinks = applyPhase t m targetElements
--    in ModelStrict (targetRoot,targetElements,targetLinks)

--transformationLazy :: Transformation -> ModelStrict -> ModelLazy
--transformationLazy t (ModelStrict m) = ModelLazy (initialize t m)

-- call a 'get' (i.e. navigate) on all the links outgoing from all the elements in the set
-- get :: (SetOf Element,Model) -> (SetOf Element,Model)
-- get (es,m@(_,_,links)) = (image links es,m)

-- Adds (strictly) element/link to Model
--addElementS :: Element -> Model -> Model
--addElementS e (rootS,elementsS,linksS) = (rootS,e:elementsS,linksS)

--addLinkS :: Link -> Model -> Model
--addLinkS l (rootS,elementsS,linksS) = (rootS,elementsS,l:linksS)

-- LAZY

-- type ModelL = (Model,Transformation,Model)

-- initialize :: Transformation -> Model -> (Model,Transformation,Model)
--initialize t m = (m,t,(rootT,[],[]))
--     where (root,_,_) = m
--           [rootT] = image t [root]

-- call a 'get' (i.e. navigate) lazily on all the links outgoing from one element, by computing the element if necessary
-- get1L :: ModelL -> Element -> (SetOf Element, ModelL)
-- get1L mL@(mS,t,mT@(rootT,elementsT,linksT)) e | e `elem` elementsT = (fst (get ([e],mT)),mL)
--                                               | otherwise
--     = let ls = bindingApplication t mS e
--           mT1 = (rootT,e:elementsT,ls++linksT)
--           mL2 = (mS,t,mT1)
--       in (fst (get ([e],mT1)),mL2)
--
-- -- get1L on a set of elements
-- getL :: (SetOf Element,ModelL) -> (SetOf Element, ModelL)
-- getL (  [],mL0) = ([],mL0)
-- getL (e:es,mL0) = let (est1,mL1) = get1L mL0 e
--                       (est2,mL2) = getL (es,mL1)
--                   in (est1 `union` est2,mL2)

-- INCREMENTAL
-- Adds element/link to Source Model (and updates the corresponding target model)
--addElementU :: Element -> (Model, Transformation, Model) -> (Model, Transformation, Model)
--addElementU e (ms, t, mt) =
--         let [ne] = image t [e]
--         in (addElementS e ms, t, addElementS ne mt)
--
-- -- this works only in our case where we just invert links
-- addLinkU :: Link -> (Model, Transformation, Model) -> (Model, Transformation, Model)
-- addLinkU (from, to) (ms, t, mt) =
--         let msu = addLinkS (from, to) ms
--             ls = bindingApplication t msu (head (image t [to]))
--         in (msu, t, foldr addLinkS mt ls)

-- REACTIVE

--get1R :: ModelL -> Element -> (SetOf Element, ModelL)

--getR :: (SetOf Element,ModelL) -> (SetOf Element, ModelL)

-- nothing happens on the target
-- addElementR :: Element -> (Model,Transformation,Model) -> (Model,Transformation,Model)
-- addElementR e (ms, t, mt) =
--     (addElementS e ms, t, mt)
--
-- addLinkR :: Link -> (Model,Transformation,Model) -> (Model,Transformation,Model)
-- addLinkR (from, to) (ms, t, mt) =
--     let msu = addLinkS (from, to) ms
--     in undefined -- (msu, t, )

-- isInvolvedIn :: Element






-- EXAMPLE

-- Metamodel

data Element = A | B | C | D | E | F deriving (Show,Eq) -- distinguish source and target element types?

-- Source Model

m0 :: ModelStrict
m0 = ModelStrict (A,[A,B],[(A,B)])

-- Transformation

t1 :: Transformation
t1 = [(A,C),(B,D),(E,F)]

-- computeBinding (_,_,links) = inverseImage links
computeBinding (_,_,links) = image links
computeBindingTraces (_,_,links) elements = nub (elements ++ image links elements)


traces :: Transformation -> Element -> SetOf Element
traces t e = image t [e]

test:: ModelI m => ModelStrict -> (SetOf Element, m)
test m0 = getN 3 (transform t1 m0)

update :: ModelStrict -> ModelStrict
update m = addLink (A, E) (addElement E m)

update' :: ModelStrict -> ModelStrict
update' m = addLinkToSource (A, E) (addElementToSource E m)
{-
test3 :: [SetOf Element]
test3 = map fst (traversal ([root],mtu))
        where (root,_,_) = mtu

mtui :: Model
mtui = mtui1
        where (_,_,mtui1) = addLinkU (E,A) (addElementU E (m0, t2, m1))

test4 :: [SetOf Element]
test4 = map fst (traversal ([root],mtui))
        where (root,_,_) = mtui
-}

mStrict :: ModelStrict
mStrict = transform t1 m0
mLazy :: ModelLazy
mLazy = transform t1 m0
mIncremental :: ModelIncremental
mIncremental = transform t1 m0
mStrict' :: ModelStrict
mStrict' = transform t1 $ update m0
mIncremental' :: ModelIncremental
mIncremental' = update' $ transform t1 m0

main::IO()
main = do
--    print $ show (fst ((test m0) :: (SetOf Element, ModelStrict)))
--    print $ show (fst ((test m0) :: (SetOf Element, ModelLazy)))
--    print $ show (fst ((test m0) :: (SetOf Element, ModelIncremental)))
    print $ show $ fst $ getN 3 mStrict
    print $ show $ fst $ getN 3 mLazy
    print $ show $ fst $ getN 3 mIncremental
    print $ show $ fst $ getN 3 mStrict'
    print $ show $ fst $ getN 3 m'

