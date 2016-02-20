module Example where

import Semantics

-- # TRANSFORMATION

tre :: Transformation
tre = ([(A,C),(B,D),(E,F)], computeBindingE, computeReverseBindingE)

computeBindingE :: Model -> SetOf Element -> SetOf Element
computeBindingE (_,_,links) = imageR links
-- computeBindingE (_,_,links) = inverseImageR links

computeReverseBindingE :: Model -> Link -> SetOf Element
computeReverseBindingE (_,_,_) (from, to) = [from]

-- # UPDATE

updateSource :: TransformationSystem m => m -> m
updateSource ts = addLinkToSource (A, E) (addElementToSource E ts)

-- # TEST EXECUTION

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
    print $ "Example 1: "
        ++ (show $ fst $ getNFromTarget 3 mStrict)
        ++ "=" ++ (show $ fst $ getNFromTarget 3 mLazy)
        ++ "=" ++ (show $ fst $ getNFromTarget 3 mIncremental)
        ++ "=" ++ (show $ fst $ getNFromTarget 3 mReactive)

    print $ "Example 2: "
        ++ (show $ fst $ getNFromTarget 3 mStrict')
        ++ "=" ++ (show $ fst $ getNFromTarget 3 mLazy')
        ++ "=" ++ (show $ fst $ getNFromTarget 3 mIncremental')
        ++ "=" ++ (show $ fst $ getNFromTarget 3 mReactive')