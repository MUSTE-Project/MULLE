BEGIN TRANSACTION;

DROP TABLE IF EXISTS User;
DROP TABLE IF EXISTS Session;
DROP TABLE IF EXISTS Lesson;
DROP TABLE IF EXISTS Exercise;
DROP TABLE IF EXISTS StartedLesson;
DROP TABLE IF EXISTS ExerciseList;

CREATE TABLE User (
  Id        INTEGER PRIMARY KEY,
  Username  TEXT NOT NULL UNIQUE,
  Password  BLOB NOT NULL,
  Salt      BLOB NOT NULL,
  Enabled   BOOL NOT NULL DEFAULT 0
);

CREATE TABLE Session (
  Id          INTEGER PRIMARY KEY,
  User        INTEGER NOT NULL,
  -- Should this be blob?
  Token       TEXT UNIQUE,
  Starttime   NUMERIC NOT NULL DEFAULT CURRENT_TIMESTAMP,
  LastActive  NUMERIC NOT NULL DEFAULT CURRENT_TIMESTAMP,

  FOREIGN KEY (User) REFERENCES User(Id)
);

CREATE TABLE Exercise (
  Id            INTEGER PRIMARY KEY,
  -- FIXME Rename to SourceLinearization
  SourceTree    BLOB,
  -- FIXME Rename to TargetLinearization
  TargetTree    BLOB,
  Lesson        INTEGER,
  Timeout       NUMERIC NOT NULL DEFAULT 0,
  -- The order in which exercises appear in a lesson.
  ExerciseOrder NUMERIC NOT NULL,

  FOREIGN KEY(Lesson) REFERENCES Lesson(Id)
);

-- FIXME We should change lesson to have a two foregin keys 'src' and
-- 'trg' to another table that describes a sentence.
CREATE TABLE Lesson (
  Id                INTEGER PRIMARY KEY,
  Name              TEXT,
  Description       TEXT NOT NULL,
  Grammar           TEXT NOT NULL,
  SourceLanguage    TEXT NOT NULL,
  TargetLanguage    TEXT NOT NULL,
  -- Exercise count does *not* say how many exercises are associated
  -- with this lesson.  Rather it says how many exercises the user is
  -- expected to complete for the lesson to be considered solved.
  ExerciseCount     NUMERIC NOT NULL,
  Enabled           BOOL NOT NULL DEFAULT 0,
  SearchLimitDepth  INT DEFAULT NULL,
  SearchLimitSize   INT DEFAULT NULL,
  Repeatable        BOOL NOT NULL DEFAULT 1,
  -- A value of 1 indicates RTL.
  SourceDirection   BOOL NOT NULL DEFAULT 0,
  TargetDirection   BOOL NOT NULL DEFAULT 0,
  HighlightMatches  BOOL NOT NULL DEFAULT 0,
  -- Should exercise appear in a randomized order?
  RandomizeOrder    BOOL NOT NULL DEFAULT 0
);

CREATE TABLE StartedLesson (
  Lesson   INTEGER,
  User     INTEGER,
  Round    NUMERIC NOT NULL DEFAULT 1,
  Score    BLOB,

  PRIMARY KEY(Lesson, User, Round),
  FOREIGN
    KEY              (Lesson)
    REFERENCES Lesson(Id),
  FOREIGN
    KEY            (User)
    REFERENCES User(Id)
);

DROP VIEW IF EXISTS FinishedLesson;
CREATE VIEW FinishedLesson AS
SELECT *
FROM StartedLesson
WHERE Score IS NOT NULL;

CREATE TABLE ExerciseList (
  User      INTEGER,
  Exercise  INTEGER,
  Round     NUMERIC NOT NULL DEFAULT 1,
  Score     BLOB, -- nullable!

  PRIMARY KEY (User, Exercise, Round),
  FOREIGN
    KEY            (User)
    REFERENCES User(Id),
  FOREIGN
    KEY                 (Exercise)
    REFERENCES Exercise (Id)
);

-- The most natural thing...
DROP VIEW IF EXISTS ExerciseLesson;
CREATE VIEW ExerciseLesson AS
  SELECT
    Exercise.Id AS Exercise,
    *
  FROM Lesson
  JOIN Exercise ON Lesson = Lesson.Id;

DROP VIEW IF EXISTS FinishedExerciseLesson;
CREATE VIEW FinishedExerciseLesson AS
  SELECT *
  FROM ExerciseList
  JOIN Exercise ON ExerciseList.Exercise     = Exercise.Id
  JOIN Lesson   ON Exercise.Lesson           = Lesson.Id
  JOIN User     ON ExerciseList.User         = User.Id
  WHERE Score NOT NULL;


-- The passed exercises by user and lesson
DROP VIEW IF EXISTS PassedLesson;
CREATE VIEW PassedLesson AS
  SELECT
    FinishedLesson.*,
    MIN(IFNULL(COUNT(*),0),1) AS Passed
  FROM FinishedLesson
  GROUP BY Lesson, User;

DROP VIEW IF EXISTS FinishedExercise;
CREATE VIEW FinishedExercise AS
SELECT *
FROM ExerciseList
WHERE Score IS NOT NULL;

COMMIT TRANSACTION;
