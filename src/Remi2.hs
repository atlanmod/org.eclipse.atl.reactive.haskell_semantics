import Data.Tuple
import Data.List
    
type Set a = [a]

--distinguish relation and function? and bijection?

type Relation = Set (Element,Element)

apply :: Relation -> Set Element -> Set Element
apply r es = nub (concat (map (apply1 r) es))
    where apply1 :: Relation -> Element -> Set Element
          apply1 r e = [ e2 | (e1,e2) <- r, e1==e ]
            
inverse :: Relation -> Set Element -> Set Element
inverse = apply . (map swap)

cross :: Element -> Set Element -> Relation
cross e1 es2 = [ (e1,e2) | e2 <- es2 ] 

type Link = (Element,Element)

type LinkS = Set Link

type Model = (Element,Set Element,LinkS)

type Transformation = Relation

-- model strict transformation

matchingPhase :: Transformation -> Model -> (Element,Set Element)
matchingPhase t (root,elements,links) = (head (apply t [root]),apply t elements)

applyPhase :: Transformation -> Model -> Set Element -> LinkS
applyPhase t m es = concat (map (bindingApplication t m) es)

bindingApplication :: Transformation -> Model -> Element -> LinkS
bindingApplication t (root,elements,links) targetReferenceSource =
    targetReferenceSource `cross` ((apply t) . (inverse links) . (inverse t)) [targetReferenceSource]

transformationStrict :: Transformation -> Model -> Model
transformationStrict t m =
    let (targetRoot,targetElements) = matchingPhase t m
        targetLinks = applyPhase t m targetElements
    in (targetRoot,targetElements,targetLinks)       

get :: (Set Element,Model) -> (Set Element,Model)
get (es,m@(root,elements,links)) = (apply links es,m)

-- lazy transformation

type ModelL = (Model,Transformation,Model)

mkLazy :: Transformation -> Model -> ModelL
mkLazy t m = (m,t,(rootT,[],[]))
     where (root,_,_) = m
           [rootT] = apply t [root]
           
get1L :: ModelL -> Element -> (Set Element, ModelL)
get1L mL@(mS,t,mT@(rootT,elementsT,linksT)) e | e `elem` elementsT = (fst (get ([e],mT)),mL)
                                              | otherwise
    = let ls = bindingApplication t mS e
          mT1 = (rootT,e:elementsT,ls++linksT) 
          mL2 = (mS,t,mT1) 
      in (fst (get ([e],mT1)),mL2) 

getL :: (Set Element,ModelL) -> (Set Element, ModelL)
getL (  [],mL0) = ([],mL0)
getL (e:es,mL0) = let (est1,mL1) = get1L mL0 e
                      (est2,mL2) = getL  (es,mL1)
                  in (est1 `union` est2,mL2)
    
-- EXAMPLE

-- Metamodel

data Element = A | B | C | D deriving (Show,Eq) -- distinguish source and target element types?

-- Source Model

m0 :: Model
m0 = (B,[A,B],[(A,B)])

-- Transformation

t1 :: Transformation
t1 = [(A,C),(B,D)]

-- Transformation launch configuration (Strict)
m1 :: Model
m1 = transformationStrict t1 m0

fixPoint :: Eq a => (a -> a) -> a -> [a]
fixPoint f a | f a == a  = [a]
             | otherwise = a:fixPoint f (f a)

                           
-- Requests (Strict)
traversal :: (Set Element,Model) -> [(Set Element,Model)]
traversal em = fixPoint get em

-- original model
test0 = traversal ([root],m0)
        where (root,_,_) = m0
        
-- strictly transformed model
test1 = traversal ([root],m1)
        where (root,_,_) = m1


-- Transformation launch configuration (lazy)
m2 :: ModelL
m2 = mkLazy t1 m0

traversalL :: (Set Element,ModelL) -> [(Set Element,ModelL)]
traversalL em = fixPoint getL em

test2 = traversalL ([rootT],m2)
        where (_,_,(rootT,_,_)) = m2

