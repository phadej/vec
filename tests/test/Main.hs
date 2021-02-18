module Main   (main) where
-- https://gitlab.haskell.org/ghc/ghc/-/issues/19397
import qualified Tests
main :: IO ()
main = Tests.main
