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
  [ ("vinum sapiens est"                          ,"han \228r vis")
  , ("Augustus imperium tenet"                    ,"imperatorn h\229ller riket")
  , ("Augustus felix est"                         ,"v\228nnen \228r lycklig")
  , ("Augustus felix est"                         ,"fadern \228r lycklig")
  , ("Augustus imperator est"                     ,"Augustus \228r v\228nnen")
  , ("Augustus amicus est"                        ,"Augustus \228r imperatorn")
  , ("Augustus imperator est"                     ,"Augustus \228r fadern")
  , ("Augustus pater est"                         ,"Augustus \228r imperatorn")
  , ("Caesar Augustus Galliam vincit"             ,"kejsaren Augustus besegrar Afrika")
  , ("Caesar Augustus Africam vincit"             ,"kejsaren Augustus besegrar Gallien")
  ]

secundaPars =
  [ ("(Pers.pron 3rd pers. Pl.) nolite"           ,"de gl\228djas")
  , ("(Pers.pron 3rd pers. Pl.) gaudent"          ,"v\228gra")
  , ("Romani eos vincebant"                       ,"de undervisade romarna")
  , ("(Pers.pron 3rd pers. Pl.) Romanos docebant" ,"romarna besegrade dem")
  , ("viri eos rapiebant"                         ,"de inbj\246d m\228nnen")
  , ("(Pers.pron 3rd pers. Pl.) viros invitabant" ,"m\228nnen r\246vade dem")
  , ("Etrusci auspicia observabant"               ,"de var b\246nder")
  , ("Romani agricolae erant"                     ,"de iakttog omen")
  , ("rex terras observabat"                      ,"de var m\228n")
  , ("Romani viri erant"                          ,"kungen iakttog l\228nder")
  , ("autem Sabini feminas habebant"              ,"men var romarna svekfulla")
  , ("autem Romani fallaces erant"                ,"men hade sabinarna kvinnor")
  , ("etiam Sabini religionem habebant"           ,"redan var romarna besegrade")
  , ("iam Romani victi erant"                     ,"\228ven hade sabinarna religionen")
  , ("Sabini libros amabant"                      ,"de var inte romanska barn")
  , ("iuvenes libri Romani non erant"             ,"sabinarna \228lskade barnen")
  , ("Sabini mulieres amabant"                    ,"de var sabinska barn")
  , ("iuvenes libri Sabini erant"                 ,"sabinarna \228lskade fruarna")
  , ("Sabini viris Romanis dicunt"                ,"de vill d\246da de romanska m\228nnen")
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

