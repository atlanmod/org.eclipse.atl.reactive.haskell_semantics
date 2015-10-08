module Main where

main::IO()
main = putStrLn (show (transformation m0))

data Type = A | B | C | D deriving (Show,Eq)

data Reference = R | R' deriving (Show,Eq)

type Identifier = Int
              
type Element = (Identifier,Type)

type Set a = [a]
    
type Elements = Set Element

type Link = (Element,Reference,Element)

type Links = Set Link

type Model = (Elements,Links)

m0 :: Model
m0 = ([(1,A),(2,B)],[((1,A),R,(2,B))])

type Match = Element -> Element

match :: Match
match (i,A) = (i,C)
match (i,B) = (i,D)

typeOf :: Element -> Type
typeOf = snd

matchingPhase :: Model -> Elements
matchingPhase = (map match) . fst

e1 :: Elements
e1 = matchingPhase m0

applyPhase :: Model -> Elements -> Links
applyPhase m es = concat (map (bindingApplication m es) es)

type BindingApplication = Model -> Elements -> Element -> Links

bindingApplication :: BindingApplication
bindingApplication m es e | typeOf e == D = let b = traceLinkTraversal m e
                                                a = referenceBinding m b
                                                c = traceLinkResolution es a
                                            in [(e,R',c)]
bindingApplication m _  _     = []

referenceBinding :: Model -> Element -> Element 
referenceBinding m e = head [ j | (j,R,k) <- snd m, k==e ]

traceLinkTraversal :: Model -> Element -> Element
traceLinkTraversal m (i,_) = head (filter ((==i) . fst) (fst m)) 

traceLinkResolution :: Elements -> Element -> Element
traceLinkResolution es (i,_) = head (filter ((==i) . fst) es)

transformation :: Model -> Model
transformation m =
    let es = matchingPhase m
        ls = applyPhase m es
    in (es,ls)

-- ValidElement means that all outgoing references are valid (in ATL terminology)
get :: LazyModel -> Element -> (Elements, LazyModel)
get lm@(m0, match, ba, ves, m1) e | e `elem` ves = ([s | (f,r,s) <- snd m1, f==e], lm)
                                  | otherwise = get (m0, match, ba, e:ves, (fst m1, snd m1++(ba m0 ves e)) 

type LazyModel = (Model, Match, BindingApplication, ValidElements, Model)

type ValidElements = Set Element

-- misc
--referenceBindingApplication :: Model -> Reference -> Element -> Elements
--referenceBindingApplication model r e =
--   let elementsOfTypeA = head (filter ((==A) . snd) (fst model))
--       linksToTheElementofTypeA = filter (\(_,r,i) -> fst elementsOfTypeA == i && r==R) (snd model)
--       in () 
---    let 
--applyPhase ::
    