module Main where

--main::IO()
--main = putStrLn (show (transformation m0))

type Identifier = Int
              
type Element = (Identifier,Type)

type Set a = [a]
    
type Elements = Set Element

type Link = (Element,Reference,Element)

type Links = Set Link

data Model =
    Model { getRoot     :: Element
          , getElements :: Elements
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

type BindingApplication = ReferenceBinding -> Model -> Elements -> Element -> Links

bindingApplication :: BindingApplication
bindingApplication rB m es sE = let sourceElement = traceLinkTraversal m sE
                                    sourceReferenceTargets = rB m sourceElement
                                    targetReferenceTargets = concat (map (traceLinkResolution es) sourceReferenceTargets)
                                in map (\tE -> (sE,R',tE)) targetReferenceTargets

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
    in Model (mf (getRoot m)) es ls       

-- Example
    
data Type = A | B | C | D deriving (Show,Eq)

data Reference = R | R' deriving (Show,Eq)

m0 :: Model
m0 = Model (1,A) [(1,A),(2,B)] [((1,A),R,(2,B))]

myMatch :: Match
myMatch (i,A) = (i,C)
myMatch (i,B) = (i,D)

myReferenceBinding :: ReferenceBinding
myReferenceBinding m e = [ j | (j,R,k) <- getLinks m, k==e ]

m1 :: Model
m1 = transformation myMatch myReferenceBinding m0

     
     
-- LAZY STUFF
       
data ModelL = ModelL {
      sourceModel :: Model
    , matchFunction :: Match
    , bindingFunction :: BindingApplication
    , validElements :: Elements
    , targetModel :: Model
    } 

transformationL :: Match -> Model -> Element -> ModelL
transformationL mf m sourceOfRoot = ModelL m mf bindingApplication [targetRoot] (Model targetRoot [targetRoot] [])
    where targetRoot = mf sourceOfRoot
                   
addValidElements :: Element -> ModelL -> ModelL
addValidElements e lm = lm { validElements = e:validElements lm } 
{-                                                       
               
-- ValidElement means that all outgoing references are valid (in ATL terminology)
get :: ModelL -> Element -> (Elements, ModelL)
get lm e | e `elem` validElements lm = ([s | (f,_,s) <- getLinks (sourceModel lm), f==e], lm)
         | otherwise                 = let lm1 = addValidElement e lm
                                           
                                       in get lm1 e

                                              , targetModel= Model (getElements (targetModel lm))
                                                                   (getLinks (targetModel lm)++bindingFunction lm (sourceModel lm) (validElements lm) e)} e 


                                                   {-


-- misc
--referenceBindingApplication :: Model -> Reference -> Element -> Elements
--referenceBindingApplication model r e =
--   let elementsOfTypeA = head (filter ((==A) . snd) (fst model))
--       linksToTheElementofTypeA = filter (\(_,r,i) -> fst elementsOfTypeA == i && r==R) (snd model)
--       in () 
---    let 
--applyPhase ::
    -}
-}