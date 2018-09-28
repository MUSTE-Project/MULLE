{-# Language TemplateHaskell, OverloadedStrings, OverloadedLists #-}
{-# OPTIONS_GHC -Wall #-}
-- | Data used for inititializing the database

module DbInit.Data (exercises, lessons) where

import Data.Text (Text)
import qualified Data.Text as Text
import Data.Vector (Vector)
import qualified Data.Vector as Vector

-- | In order of appearance:
--   * Name
--   * Description
--   * Grammar
--   * SourceLanguage
--   * TargetLanguage
--   * ExerciseCount
--   * Enabled
--   * Repeatable
type Lesson = (Text,Text,Text,Text,Text,Int,Bool,Bool)

lessons :: Vector Lesson
lessons = Vector.fromList $ novomodoLessons ++ exemplumLessons

-- | List of exercises group by the lesson they belong to.  The lesson
-- is identified by 1. an identifier for the grammar for that lesson
-- and 2. by the name of that lesson (a PK in the DB).  Exercises are
-- identified by a pair of tree/language pairs.
exercises ∷ Vector (Text, Text, Text, Text, Vector (Text, Text))
exercises = Vector.fromList $ novomodoExercises ++ exemplumExercises


--------------------------------------------------------------------------------
-- Novo Modo lessons

novomodoLessons =
  [ (lesson, Text.concat ["Lektion ", lesson, " från boken 'Novo Modo'"],
     grammar, srcLng, trgLng, Vector.length exs, True, True)
  | (grammar, lesson, srcLng, trgLng, exs) <- novomodoExercises
  ]

novomodoExercises =
  [ (Text.append "novo_modo/" lesson, lesson, Text.append lesson "Lat", Text.append lesson "Swe", exerciseList)
  | (lesson, exerciseList) <- novomodoDB
  ]

novomodoDB =
    [ ("Prima"  , primaPars)
    , ("Secunda", secundaPars)
    -- , ("Tertia" , tertiaPars)
    -- , ("Quarta" , quartaPars)
    ]

primaPars =
  [ ("vinum sapiens est"                          ,"han är vis")
  , ("Augustus imperium tenet"                    ,"imperatorn håller riket")
  , ("Augustus felix est"                         ,"vännen är lycklig")
  , ("Augustus felix est"                         ,"fadern är lycklig")
  , ("Augustus imperator est"                     ,"Augustus är vännen")
  , ("Augustus amicus est"                        ,"Augustus är imperatorn")
  , ("Augustus imperator est"                     ,"Augustus är fadern")
  , ("Augustus pater est"                         ,"Augustus är imperatorn")
  , ("Caesar Augustus Galliam vincit"             ,"kejsaren Augustus besegrar Afrika")
  , ("Caesar Augustus Africam vincit"             ,"kejsaren Augustus besegrar Gallien")
  ]

secundaPars =
  [ ("(Pers.pron 3rd pers. Pl.) nolite"           ,"de glädjas")
  , ("(Pers.pron 3rd pers. Pl.) gaudent"          ,"vägra")
  , ("Romani eos vincebant"                       ,"de undervisade romarna")
  , ("(Pers.pron 3rd pers. Pl.) Romanos docebant" ,"romarna besegrade dem")
  , ("viri eos rapiebant"                         ,"de inbjöd männen")
  , ("(Pers.pron 3rd pers. Pl.) viros invitabant" ,"männen rövade dem")
  , ("Etrusci auspicia observabant"               ,"de var bönder")
  , ("Romani agricolae erant"                     ,"de iakttog omen")
  , ("rex terras observabat"                      ,"de var män")
  , ("Romani viri erant"                          ,"kungen iakttog länder")
  , ("autem Sabini feminas habebant"              ,"men var romarna svekfulla")
  , ("autem Romani fallaces erant"                ,"men hade sabinarna kvinnor")
  , ("etiam Sabini religionem habebant"           ,"redan var romarna besegrade")
  , ("iam Romani victi erant"                     ,"även hade sabinarna religionen")
  , ("Sabini libros amabant"                      ,"de var inte romanska barn")
  , ("iuvenes libri Romani non erant"             ,"sabinarna älskade barnen")
  , ("Sabini mulieres amabant"                    ,"de var sabinska barn")
  , ("iuvenes libri Sabini erant"                 ,"sabinarna älskade fruarna")
  , ("Sabini viris Romanis dicunt"                ,"de vill döda de romanska männen")
  , ("Romani cum eis contendebant"                ,"de sammandrabbade romarna")
  , ("Romani eos docebant"                        ,"de undervisade romarna")
  ]

-- tertiaPars
--   = []

-- quartaPars
--   = []


--------------------------------------------------------------------------------
-- Exemplum lessons

exemplumLessons =
  [ (lesson, Text.append "Example grammar: " lesson,
     grammar, srcLng, trgLng, length exs, True, True)
  | (grammar, lesson, srcLng, trgLng, exs) <- exemplumExercises
  ]

exemplumExercises =
  [ ("exemplum/Exemplum", Text.concat ["Exemplum ", l1, "-", l2],
     Text.append "Exemplum" l1, Text.append "Exemplum" l2, Vector.singleton (s1, s2))
  | let (l1, s1) = head exemplumSentences,
    (l2, s2) <- tail exemplumSentences
  ]

exemplumSentences =
    [ ("Eng", "many kings love Paris")
    , ("Swe", "en god kung läser en bok")
    , ("Lat", "rex bonus librum legit")
    , ("Spa", "un bueno rey lee un libro")
    , ("Chi", " 一 个 好 国 王 读 一 本 书 ")
    , ("Ara", " يَقْرَأُ مَلِكٌ جوَيِّدٌ كِتابً ")
    ]

