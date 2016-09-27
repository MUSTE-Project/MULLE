import Test.Framework
import Test.Framework.Providers.HUnit
import Test.Framework.Providers.QuickCheck2
import Test.HUnit
import qualified Test.Grammar as G
import qualified Test.Tree as T

tests = (hUnitTestToTests $ TestList [ G.hunit_tests, T.hunit_tests ]) ++ (map (uncurry testProperty) T.quickcheck_tests)

main = defaultMain tests
