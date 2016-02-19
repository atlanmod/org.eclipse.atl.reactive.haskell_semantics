module Example where

import Semantics

tre :: Transformation
tre = ([(A,C),(B,D),(E,F)], computeBindingE, computeReverseBindingE)

-- sourceModel -> matchedElements -> resultingSourceElements
computeBindingE :: Model -> SetOf Element -> SetOf Element
computeReverseBindingE :: Model -> Link -> SetOf Element
-- computeBinding (_,_,links) = inverseImage links
computeBindingE (_,_,links) = imageR links
computeReverseBindingE (_,_,_) (from, to) = [from]

updateSource :: TransformationI m => m -> m
updateSource ts = addLinkToSource (A, E) (addElementToSource E ts)

ts0 :: TransformationStrict
ts0 = TransformationStrict ((A,[A,B],[(A,B)]), tre, undefined)
tl0 :: TransformationLazy
tl0 = TransformationLazy ((A,[A,B],[(A,B)]), tre, undefined)
ti0 :: TransformationIncremental
ti0 = TransformationIncremental ((A,[A,B],[(A,B)]), tre, undefined)
tr0 :: TransformationReactive
tr0 = TransformationReactive ((A,[A,B],[(A,B)]), tre, undefined)

mStrict :: TransformationStrict
mStrict = apply ts0
mLazy :: TransformationLazy
mLazy = apply tl0
mIncremental :: TransformationIncremental
mIncremental = apply ti0
mReactive :: TransformationReactive
mReactive = apply tr0

mStrict' :: TransformationStrict
mStrict' = apply $ updateSource $ apply ts0
mLazy' :: TransformationLazy
mLazy' = apply $ updateSource $ apply tl0
mIncremental' :: TransformationIncremental
mIncremental' = updateSource $ apply ti0
mReactive' :: TransformationReactive
mReactive' = updateSource $ apply tr0

exampleTest :: IO()
exampleTest = do
    print $ show $ fst $ getNFromTarget 3 mStrict
    print $ show $ fst $ getNFromTarget 3 mLazy
    print $ show $ fst $ getNFromTarget 3 mIncremental
    print $ show $ fst $ getNFromTarget 3 mReactive

    print $ show $ fst $ getNFromTarget 3 mStrict'
    print $ show $ fst $ getNFromTarget 3 mLazy'
    print $ show $ fst $ getNFromTarget 3 mIncremental'
    print $ show $ fst $ getNFromTarget 3 mReactive'