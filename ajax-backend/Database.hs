{-# LANGUAGE OverloadedStrings #-}
module Main where

import Database.SQLite.Simple
import Crypto.Random.API

import Crypto.KDF.PBKDF2
import Crypto.Hash

import qualified Data.ByteString.Base64 as B64
import qualified Data.ByteString.Char8 as B
import qualified Data.ByteString.Lazy.Char8 as LB

foo = ()

-- | hashPasswd returns a SHA512 hash of a PBKDF2 encoded password (SHA512,10000 iterations,1024 bytes output)
hashPasswd :: B.ByteString -> B.ByteString -> B.ByteString
hashPasswd pass salt =
--  B64.encode $ fastPBKDF2_SHA512 (Parameters 10000 1024) pass salt
  fastPBKDF2_SHA512 (Parameters 10000 1024) pass salt

-- | createSalt returns a SHA512 hash of 512 bytes of random data as a bytestring 
createSalt :: IO (B.ByteString)
createSalt =
  do
    rng <- getSystemRandomGen
    -- return $ B64.encode $ fst $ genRandomBytes 512 rng
    return $ fst $ genRandomBytes 512 rng
    
addUser :: Connection -> String -> String -> IO ()
addUser conn user pass =
  do
    salt <- createSalt
    let safePw = hashPasswd (B.pack pass) salt
    -- putStrLn $ "Salt: " ++ show salt ++ "\nsafePw: " ++ show safePw
    let deleteQuery = "DELETE FROM User WHERE Username = ?;" :: Query
    let insertQuery = "INSERT INTO User (Username, Password, Salt) VALUES (?,?,?);" :: Query
    execute conn deleteQuery [user]
    execute conn insertQuery (user,safePw,salt)

authUser :: Connection -> String -> String -> IO (Bool)
authUser conn user pass =
  do
    let q = "SELECT Password,Salt FROM User WHERE (Username == ?);" :: Query
    r <- (query conn q [user]) :: IO [(B.ByteString,B.ByteString)]
    let (dbPass,dbSalt) = head r
--    let pwHash = either error (hashPasswd (B.pack pass)) $ B64.decode dbSalt
    let pwHash = hashPasswd (B.pack pass) dbSalt
    return $ pwHash == dbPass

initDB :: Connection -> IO ()
initDB conn =
  do
    execute_ conn "DROP TABLE IF EXISTS User;"
    execute_ conn "DROP TABLE IF EXISTS Session;"
    execute_ conn "DROP TABLE IF EXISTS Lesson;"
    execute_ conn "DROP TABLE IF EXISTS Exercise;"
    execute_ conn "DROP TABLE IF EXISTS FinishedExercise;"
    execute_ conn "DROP TABLE IF EXISTS StartedLesson;"
    execute_ conn "DROP TABLE IF EXISTS FinishedLesson;"
    execute_ conn "DROP TABLE IF EXISTS ExerciseList";
    execute_ conn "CREATE TABLE User (Username TEXT, Password BLOB, Salt BLOB, PRIMARY KEY(Username));"
    execute_ conn "CREATE TABLE Session (Token TEXT, Starttime NUMERIC DEFAULT CURRENT_TIMESTAMP, PRIMARY KEY(Token));"
    execute_ conn "CREATE TABLE Lesson (Name TEXT, Description TEXT, Grammar TEXT, ExerciseCount NUMERIC, PRIMARY KEY(Name));"
    execute_ conn "CREATE TABLE Exercise (SourceTree TEXT, TargetTree TEXT, Lesson TEXT, PRIMARY KEY(SourceTree, TargetTree, Lesson), FOREIGN KEY(Lesson) References Lesson(Name));"
    execute_ conn "CREATE TABLE FinishedExercise (User TEXT, SourceTree TEXT, TargetTree TEXT, Lesson TEXT, Time NUMERIC, ClickCount NUMERIC, PRIMARY KEY (User,SourceTree, TargetTree, Lesson), FOREIGN KEY (User) REFERENCES User(Username), FOREIGN KEY(SourceTree, TargetTree, Lesson) REFERENCES Exercise(SourceTree, TargetTree, Lesson));"
    execute_ conn "CREATE TABLE StartedLesson (Lesson TEXT, User TEXT, PRIMARY KEY(Lesson, User), FOREIGN KEY(Lesson) REFERENCES Lesson(Name), FOREIGN KEY(User) REFERENCES User(Username));"
    execute_ conn "CREATE TABLE FinishedLesson (Lesson TEXT, User TEXT, Time NUMERIC, FOREIGN KEY (User) REFERENCES User(Username), FOREIGN KEY (Lesson) REFERENCES Lesson(Name));"
    execute_ conn "CREATE TABLE ExerciseList (User TEXT, SourceTree TEXT, TargetTree TEXT, Lesson TEXT, PRIMARY KEY (User, SourceTree, TargetTree, Lesson), FOREIGN KEY(User) REFERENCES User(Username), FOREIGN KEY(SourceTree,TargetTree, Lesson) REFERENCES Exercise (SourceTree, TargetTree, Lesson));"
    addUser conn "user1" "pass1"
    addUser conn "user2" "pass2"
    addUser conn "user3" "pass3"
    addUser conn "user4" "pass4"
    addUser conn "user5" "pass5"
    execute_ conn "INSERT INTO Lesson (Name,Description,Grammar) VALUES ('Prima Pars','Den första Lektionen fran boken','Prima.pgf',5);"
    execute_ conn "INSERT INTO Lesson (Name,Description,Grammar) VALUES ('Seconda Pars','Den andra Lektionen fran boken','Secunda.pgf',8);"
    execute_ conn "INSERT INTO Lesson (Name,Description,Grammar) VALUES ('Tertia Pars','Den tredje Lektionen fran boken','Tertia.pgf',12);"
    execute_ conn "INSERT INTO Lesson (Name,Description,Grammar) VALUES ('Quarta Pars','Den fjärde Lektionen fran boken','Quarta.pgf',15);"
    -- First lesson one editing steps between the trees
    execute_ conn "INSERT INTO Exercise (SourceTree,TargetTree,Lesson) VALUES ('useS (useCl (simpleCl (useCNindefsg (useN vinum_N)) (complA sapiens_A)))','useS (useCl (simpleCl (usePron he_PP) (complA sapiens_A)))','Prima Pars');"
    execute_ conn "INSERT INTO Exercise (SourceTree,TargetTree,Lesson) VALUES ('useS (useCl (simpleCl (usePN Augustus_PN) (transV tenere_V2 (useCNdefsg (useN imperium_N)))))','useS (useCl (simpleCl (useCNdefsg (useN imperator_N)) (transV tenere_V2 (useCNdefsg (useN imperium_N)))))','Prima Pars');"

    execute_ conn "INSERT INTO Exercise (SourceTree,TargetTree,Lesson) VALUES ('useS (useCl (simpleCl (usePN Augustus_PN) (complA felix_A)))','useS (useCl (simpleCl (useCNdefsg (useN amicus_N)) (complA felix_A)))','Prima Pars');"
    execute_ conn "INSERT INTO Exercise (SourceTree,TargetTree,Lesson) VALUES ('useS (useCl (simpleCl (usePN Augustus_PN) (complA felix_A)))','useS (useCl (simpleCl (useCNdefsg (useN pater_N)) (complA felix_A)))','Prima Pars');"

    
    execute_ conn "INSERT INTO Exercise (SourceTree,TargetTree,Lesson) VALUES ('useS (useCl (simpleCl (usePN Augustus_PN) (complCN (useN imperator_N))))','useS (useCl (simpleCl (usePN Augustus_PN) (complCN (useN amicus_N))))','Prima Pars');"
    execute_ conn "INSERT INTO Exercise (SourceTree,TargetTree,Lesson) VALUES ('useS (useCl (simpleCl (usePN Augustus_PN) (complCN (useN amicus_N))))','useS (useCl (simpleCl (usePN Augustus_PN) (complCN (useN imperator_N))))','Prima Pars');"
    execute_ conn "INSERT INTO Exercise (SourceTree,TargetTree,Lesson) VALUES ('useS (useCl (simpleCl (usePN Augustus_PN) (complCN (useN imperator_N))))','useS (useCl (simpleCl (usePN Augustus_PN) (complCN (useN pater_N))))','Prima Pars');"
    execute_ conn "INSERT INTO Exercise (SourceTree,TargetTree,Lesson) VALUES ('useS (useCl (simpleCl (usePN Augustus_PN) (complCN (useN pater_N))))','useS (useCl (simpleCl (usePN Augustus_PN) (complCN (useN imperator_N))))','Prima Pars');"
    
    execute_ conn "INSERT INTO Exercise (SourceTree,TargetTree,Lesson) VALUES ('useS (useCl (simpleCl (apposCNdefsg (useN Caesar_N) (usePN Augustus_PN)) (transV vincere_V2 (usePN Gallia_PN))))','useS (useCl (simpleCl (apposCNdefsg (useN Caesar_N) (usePN Augustus_PN)) (transV vincere_V2 (usePN Africa_PN))))','Prima Pars');"
    execute_ conn "INSERT INTO Exercise (SourceTree,TargetTree,Lesson) VALUES ('useS (useCl (simpleCl (apposCNdefsg (useN Caesar_N) (usePN Augustus_PN)) (transV vincere_V2 (usePN Africa_PN))))','useS (useCl (simpleCl (apposCNdefsg (useN Caesar_N) (usePN Augustus_PN)) (transV vincere_V2 (usePN Gallia_PN))))','Prima Pars');"

-- | start a new lesson by randomly choosing the right number of exercises and adding them to the users exercise list
startLesson :: Connection -> String -> String -> IO ()
startLesson conn token lesson =
  do
    -- get user name
    -- let userQuery = "SELECT Username FROM Session WHERE Token = ?;" :: Query
    -- query conn userQuery [token]
    -- get exercise count
    -- get all exercises for lesson
    -- randomly select
    -- save in database
    return ()
main =
  do
    putStrLn "Starting"
    con <- open "muste.db"
    addUser con "user1" "pass1234"
