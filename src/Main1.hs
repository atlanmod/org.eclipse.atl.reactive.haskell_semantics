module Main where

main::IO()
main = putStrLn (show (test))

type Identifier = Int
              
type Element = (Identifier,Type)

type Set a = [a]
    
type Elements = Set Element

type Link = (Element,Reference,Element)

type Links = Set Link

-- STRICT
    
data Model =
    Model { getElements :: Elements
          , getLinks    :: Links } deriving (Show,Eq) 

type Match = Element -> Element
    
getType :: Element -> Type
getType = snd

getIdentifier :: Element -> Identifier
getIdentifier = fst
         
matchingPhase :: Match -> Model -> Elements
matchingPhase mf = (map mf) . getElements

applyPhase :: ReferenceBinding -> Model -> Elements -> Links
applyPhase rB m es = concat (map (bindingApplication rB m es) es)

bindingApplication :: ReferenceBinding -> Model -> Elements -> Element -> Links
bindingApplication rB m es targetReferenceSource =
    let sourceElement = traceLinkTraversal m targetReferenceSource
        sourceReferenceTargets = rB m sourceElement
        targetReferenceTargets = concat (map (traceLinkResolution es) sourceReferenceTargets)
    in map (\tRT -> (targetReferenceSource,R,tRT)) targetReferenceTargets

type ReferenceBinding = Model -> Element -> Elements 
                                
traceLinkTraversal :: Model -> Element -> Element
traceLinkTraversal m (i,_) = eSource
    where [eSource] = filter ((==i) . getIdentifier) (getElements m) 

traceLinkResolution :: Elements -> Element -> Elements
traceLinkResolution es (i,_) = filter ((==i) . getIdentifier) es

transformation :: Match -> ReferenceBinding -> Model -> Model
transformation mf rf m =
    let es = matchingPhase mf m
        ls = applyPhase rf m es
    in Model es ls       

get :: Model -> Element -> Elements
get m eS = [ eT | (eS',_,eT) <- getLinks m, eS'==eS]


-- LAZY STUFF
       
data ModelL = ModelL {
      sourceModel :: Model
    , matchFunction :: Match
    , referenceBindingFunction :: ReferenceBinding
    , validElements :: Elements
    , targetModel :: Model
    } 

transformationL :: Match -> ReferenceBinding -> Model -> Element -> ModelL
transformationL mf rB m sourceOfRoot = ModelL m mf rB [] (Model [targetRoot] [])
    where targetRoot = mf sourceOfRoot
                   
addValidElements :: Element -> ModelL -> ModelL
addValidElements e lm = lm { validElements = e:validElements lm } 

bindingApplicationL :: ModelL -> Element -> (Elements,Links)
bindingApplicationL lm targetReferenceSource =
    let sourceElement = traceLinkTraversal (sourceModel lm) targetReferenceSource
        sourceReferenceTargets = (referenceBindingFunction lm) (sourceModel lm) sourceElement
        --targetReferenceTargets = map (matchFunction lm) sourceReferenceTargets
        targetReferenceTargets = map (matchFunction' lm) sourceReferenceTargets
    in (targetReferenceTargets,map (\tRT -> (targetReferenceSource,R,tRT)) targetReferenceTargets)

matchFunction' :: ModelL -> Match
matchFunction' lm e | null targetElement = matchFunction lm e
                    | otherwise = head targetElement
                    where targetElement = traceLinkResolution (getElements (targetModel lm)) e                                   
       
getL :: ModelL -> Element -> (Elements, ModelL)
getL lm e | e `elem` validElements lm = (get (targetModel lm) e,lm)
          | otherwise
    = let (es,ls) = bindingApplicationL lm e
          tm1 = Model (es++getElements tm) (ls++getLinks tm) where tm = targetModel lm
          lm1 = lm { targetModel = tm1 }
          lm2 = addValidElements e lm1
      in (get (targetModel lm2) e,lm2) -- aka (tm1,lm2)
                        

-- EXAMPLE

-- Metamodel
data Type = A | B | C | D deriving (Show,Eq)
data Reference = R deriving (Show,Eq)

-- Source Model
m0 :: Model
m0 = Model [(1,A),(2,B)] [((1,A),R,(2,B))]

-- Transformation
myMatch :: Match
myMatch (i,A) = (i,C)
myMatch (i,B) = (i,D)

myReferenceBinding :: ReferenceBinding
myReferenceBinding m e = [ j | (j,R,k) <- getLinks m, k==e ] -- R <- opposite of R

-- Transformation launch configuration (Strict)
m1 :: Model
m1 = transformation myMatch myReferenceBinding m0

-- Requests (Strict)
dFS :: Model -> Element -> Elements
dFS m e = e:concat (map (dFS m) (get m e))

test1 = dFS m1 (2,D)

-- Transformation launch configuration (Lazy)
lm1 :: ModelL
lm1 = transformationL myMatch myReferenceBinding m0 (2,B)

-- Requests (Lazy)
dFSLs :: [Element] -> ModelL -> (Elements,ModelL)
dFSLs []     lm = ([],lm)
dFSLs (e:es) lm =
    let (es1,lm1) = getL lm e
        (es2,lm2) = dFSLs (es++es1) lm1
    in (e:es2,lm2)

test1L = fst (dFSLs [(2,D)] lm1)

-- Test
test = test1==test1L