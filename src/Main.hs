-- see Semantics.hs for limitations

module Main where

import Example
import QuickChecker

main::IO()
main = do
    exampleTest
    quickCheckTest