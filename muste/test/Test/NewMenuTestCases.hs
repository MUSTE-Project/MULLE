{-# Language UnicodeSyntax, OverloadedStrings #-}
module Test.NewMenuTestCases where

import Data.Text (Text)
import qualified Muste.Menu.New as Menu

-- | A test-case consists of the following (in order of appearance):
--
-- * The language that the two sentences are written in.
-- * The sentence to get suggestions from.
-- * A list of cases from that menu:
-- ** The "selection" to make. If the selection is [] then the test is supposed to fail.
-- ** A sentence to (alt.: not) expect to be at this position in the menu.
type LinTestCase = (Text, String, [(Menu.Selection, String)])

linTestCases :: [LinTestCase]
linTestCases=
    [ ("ExemplumSwe", "kungen älskar Paris",
       [ ([(0,0)], "en kung älskar Paris")
       , ([(0,1)], "Johan älskar Paris")
       , ([(1,2)], "kungen är Paris")
       ])
    , ("ExemplumSwe", "kungen är stor",
       [ ([(0,1)], "huset är stort")
       ])
    , ("ExemplumSwe", "kungen är Paris",
       [ ([(2,3)], "kungen är stor")
       , ([(2,3)], "kungen är en vän")
       ])
    , ("ExemplumSwe", "det kalla huset är stort",
       [ ([(0,2)], "huset är stort")
       ])
    , ("ExemplumSwe", "huset är stort",
       [ ([(0,0)], "det kalla huset är stort")
       ])
    , ("ExemplumSwe", "Johan älskar Paris",
       [ ([(0,1)], "en kung älskar Paris")
       , ([], "en stor kung älskar Paris")
       ])
    , ("ExemplumSwe", "en kung älskar Paris",
       [ ([(1,1)], "en stor kung älskar Paris")
       ])
    , ("ExemplumSwe", "Johan älskar vännen",
       [ ([(3,3)], "Johan älskar vännen idag")
       , ([(3,3)], "Johan älskar vännen i Paris")
       ])
    , ("ExemplumSwe", "Johan älskar vännen idag",
       [ ([(3,4)], "Johan älskar vännen")
       ])
    , ("ExemplumSwe", "Johan älskar vännen i Paris",
       [ ([(3,5)], "Johan älskar vännen")
       ])

    -- These are taken from issue #24:
    , ("ExemplumSwe", "flickan slår på en dator",
       [ ([] , "flickan slår på en dator")
       , ([(0,1)] , "flickor slår på en dator")
       , ([(0,1)] , "flickorna slår på en dator")

       , ([(0,0)] , "en flicka slår på en dator")
       , ([(0,0)] , "många flickor slår på en dator")
       , ([(0,0)] , "den blåa flickan slår på en dator")
       , ([(0,0)] , "den dåliga flickan slår på en dator")
       , ([(0,0)] , "pojken och flickan slår på en dator")

       , ([(0,1)] , "Johan slår på en dator")
       , ([(0,1)] , "boken slår på en dator")
       , ([(0,1)] , "datorn slår på en dator")
       , ([(0,1)] , "de slår på en dator")
       , ([(0,1)] , "hon slår på en dator")

       , ([(0,1),(2,2)] , "idag slår flickan på en dator")

       , ([(1,1)] , "flickan Johan slår på en dator")
       , ([(1,1)] , "flickan och pojken slår på en dator")
       , ([(1,1)] , "flickan i huset slår på en dator")

       , ([(1,2)] , "flickan läser på en dator")
       , ([(1,2)] , "flickan älskar på en dator")
       , ([] , "flickan läser Johan på en dator")
       , ([(1,2)] , "flickan slår sönder på en dator")
       , ([] , "flickan stänger dem på en dator")
       , ([] , "flickan älskar honom på en dator")
       , ([] , "flickan slår sönder Johan på en dator")

       , ([(1,3)] , "flickan slår en dator")
       , ([(1,3)] , "flickan älskar en dator")
       , ([(1,3)] , "flickan slår sönder en dator")

       , ([(2,5)] , "flickan slår")
       , ([(2,5)] , "flickan slår blå")
       , ([] , "flickan läser")
       , ([] , "flickan älskar")
       , ([] , "flickan slår sönder")
       , ([] , "flickan stänger god")
       , ([] , "flickan älskar kall")

       , ([(2,2)] , "flickan slår redan på en dator")
       , ([(2,2)] , "flickan slår honom på en dator")
       , ([(2,2)] , "flickan slår Paris på en dator")
       , ([(2,2)] , "flickan slår boken på en dator")

       , ([(2,3)] , "flickan slår i en dator")
       , ([(2,3)] , "flickan slår till en dator")
       , ([(2,3)] , "flickan slår en dator")

       , ([(2,5)] , "flickan slår")
       , ([(2,5)] , "flickan slår idag")
       , ([(2,5)] , "flickan slår henne")

       , ([(3,4)] , "flickan slår på datorerna")
       , ([(3,4)] , "flickan slår på många datorer")

       , ([(3,5)] , "flickan slår på dem")
       , ([(3,5)] , "flickan slår på Paris")

       , ([(4,4)] , "flickan slår på en blå dator")

       , ([(4,5)] , "flickan slår på en flicka")
       , ([(4,5)] , "flickan slår på ett hus")

       , ([(5,5)] , "flickan slår på en dator idag")
       , ([(5,5)] , "flickan slår på en dator i huset")
       ])
    ]
