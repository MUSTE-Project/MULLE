-- TODO In stead of using very long ad-hoc types, could we define a
-- local data-type?  Alternatively, and probably even better, could we
-- re-write this so to have a more declarative style?  What I mean is
-- that in stead of defining one chunk of data and then doing
-- operations on it seperately, could we define a small helper that
-- does it in place like so:
--
--     longPieceOfData =
--       [ h "..."
--       , h "..."
--       ]
--       where
--       h = _ -- magic here
{-# Language TemplateHaskell, OverloadedStrings, OverloadedLists #-}
{-# OPTIONS_GHC -Wall #-}
-- | Data used for inititializing the database

module DbInit.Data (exercises, lessons) where

import Data.Text (Text)
import qualified Data.Text as Text
import Data.Vector (Vector)
import qualified Data.Vector as Vector
import qualified Database.Types as Types

lessons :: Vector Types.Lesson
lessons = novomodoLessons <> exemplumLessons

-- | List of exercises group by the lesson they belong to.  The lesson
-- is identified by 1. an identifier for the grammar for that lesson
-- and 2. by the name of that lesson (a PK in the DB).  Exercises are
-- identified by a pair of tree/language pairs.
exercises ∷ Vector (Text, Text, Text, Text, Vector (Text, Text))
exercises = novomodoExercises <> exemplumExercises


--------------------------------------------------------------------------------
-- Novo Modo lessons

novomodoLessons ∷ Vector Types.Lesson
novomodoLessons = Vector.zipWith f [1..] novomodoDB
  where
  f nr (lesson, srcLng, trgLng, depthLimit, exerciseList)
    = Types.Lesson
    lesson (novomodoDescription nr)
    (novomodoGrammar lesson)
    srcLng
    trgLng
    (fromIntegral (Vector.length exerciseList))
    True
    depthLimit
    depthLimit
    True

-- TODO depthLimit is not used, is this a mistake?
novomodoExercises ∷ Vector (Text, Text, Text, Text, Vector (Text, Text))
novomodoExercises = f <$> novomodoDB
  where
  f (lesson, srcLng, trgLng, _depthLimit, exerciseList)
    = (novomodoGrammar lesson, lesson, srcLng, trgLng, exerciseList)

novomodoGrammar ∷ Text → Text
novomodoGrammar = mappend "novo_modo/"

novomodoDescription ∷ Integer → Text
novomodoDescription nr = Text.concat ["Lektion ", Text.pack (show nr), " från boken 'Novo Modo'"]

novomodoDepthLimit ∷ Maybe Int
novomodoDepthLimit = Just 1

novomodoDB ∷ Vector (Text, Text, Text, Maybe Int, Vector (Text, Text))
novomodoDB =
    [ ("Prima"  , "PrimaLat"  , "PrimaSwe"  , novomodoDepthLimit, primaPars  )
    , ("Secunda", "SecundaLat", "SecundaSwe", novomodoDepthLimit, secundaPars)
    -- , ("Tertia" , "TertiaLat" , "TertiaSwe" , novomodoDepthLimit, tertiaPars )
    -- , ("Quarta" , "QuartaLat" , "QuartaSwe" , novomodoDepthLimit, quartaPars )
    ]

primaPars ∷ Vector (Text, Text)
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

secundaPars ∷ Vector (Text, Text)
secundaPars =
  [ ("nolite"                                     ,"de glädjas")
  , ("gaudent"                                    ,"vägra")
  , ("Romani eos vincebant"                       ,"de undervisade romarna")
  , ("Romanos docebant"                           ,"romarna besegrade dem")
  , ("viri eos rapiebant"                         ,"de inbjöd männen")
  , ("viros invitabant"                           ,"männen rövade dem")
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

--------------------------------------------------------------------------------
-- Exemplum lessons

exemplumLessons ∷ Vector Types.Lesson
exemplumLessons = f <$> exemplumDB
  where
  f (lesson, srcLng, trgLng, depthLimit, exerciseList)
    = Types.Lesson
      lesson
      (Text.concat ["Example lesson: ", lesson])
      exemplumGrammar
      srcLng
      trgLng
      (fromIntegral (Vector.length exerciseList))
      True
      depthLimit
      depthLimit
      True

-- TODO depthLimit is not used, is this a mistake?
exemplumExercises ∷ Vector (Text, Text, Text, Text, Vector (Text, Text))
exemplumExercises = f <$> exemplumDB
  where
  f (lesson, srcLng, trgLng, _depthLimit, exerciseList)
    = (exemplumGrammar, lesson, srcLng, trgLng, exerciseList)
  -- [ (exemplumGrammar, lesson, srcLng, trgLng, exerciseList)
  -- | (lesson, srcLng, trgLng, _depthLimit, exerciseList) <- exemplumDB
  -- ]

exemplumGrammar ∷ Text
exemplumGrammar = "exemplum/Exemplum"

exemplumDepthLimit ∷ Maybe Int
exemplumDepthLimit = Just 4

exemplumDB ∷ Vector (Text, Text, Text, Maybe Int, Vector (Text, Text))
exemplumDB = f <$> Vector.tail exemplumSentences
  where
  f (trgLng, trg) = 
      (Text.concat [srcLng, "->", trgLng],
       Text.concat ["Exemplum", srcLng],
       Text.concat ["Exemplum", trgLng],
       exemplumDepthLimit,
       [(src, trg)])
  (srcLng, src) = Vector.head exemplumSentences

exemplumSentences ∷ Vector (Text, Text)
exemplumSentences =
    [ ("Eng", "many kings love Paris")
    , ("Swe", "en god kung läser en bok")
    , ("Lat", "rex bonus librum legit")
    , ("Spa", "un bueno rey lee un libro")
    , ("Chi", " 一 个 好 国 王 读 一 本 书 ")
    , ("Ara", " يَقْرَأُ مَلِكٌ جوَيِّدٌ كِتابً ")
    , ("Test", "the girl read book")
    ]

