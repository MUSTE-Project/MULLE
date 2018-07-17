import Test.Framework
import Test.Framework.Providers.HUnit
import Test.Framework.Providers.QuickCheck2
import Test.HUnit
import qualified Test.Grammar as G
import qualified Test.Tree as T
import qualified Test.Muste as M

tests = hUnitTestToTests ( TestList [ G.hunit_tests, T.hunit_tests, M.hunit_tests ]) ++ map (uncurry testProperty) ( G.quickcheck_tests ++ T.quickcheck_tests ++ M.quickcheck_tests)

main = defaultMain tests
