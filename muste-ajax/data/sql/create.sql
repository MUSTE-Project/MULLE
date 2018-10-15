BEGIN TRANSACTION;

DROP TABLE IF EXISTS User;
DROP TABLE IF EXISTS Session;
DROP TABLE IF EXISTS Lesson;
DROP TABLE IF EXISTS Exercise;
DROP TABLE IF EXISTS FinishedExercise;
DROP TABLE IF EXISTS StartedLesson;
DROP TABLE IF EXISTS FinishedLesson;
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
  Id          INTEGER PRIMARY KEY,
  SourceTree  BLOB,
  TargetTree  BLOB,
  Lesson      INTEGER,
  Timeout     NUMERIC NOT NULL DEFAULT 0,

  FOREIGN KEY(Lesson) REFERENCES Lesson(Id)
);

CREATE TABLE Lesson (
  Id                INTEGER PRIMARY KEY,
  Name              TEXT,
  Description       TEXT NOT NULL,
  Grammar           TEXT NOT NULL,
  SourceLanguage    TEXT NOT NULL,
  TargetLanguage    TEXT NOT NULL,
  -- TODO Create a view where this is a computed column.
  ExerciseCount     NUMERIC NOT NULL,
  Enabled           BOOL NOT NULL DEFAULT 0,
  SearchLimitDepth  INT DEFAULT NULL,
  SearchLimitSize   INT DEFAULT NULL,
  Repeatable        BOOL NOT NULL DEFAULT 1
);

-- FIXME Why not simply add a nullable column to the ExerciseList table?
CREATE TABLE FinishedExercise (
  User      INTEGER,
  Exercise  INTEGER,
  Round     INTEGER,
  Score     BLOB NOT NULL,

  PRIMARY
    KEY (User, Exercise, Round),
  FOREIGN
    KEY (User)
    REFERENCES User(Id),
  FOREIGN
    KEY (Exercise)
    REFERENCES Exercise(Id)
  FOREIGN
    KEY (User, Exercise, Round)
    REFERENCES ExerciseList(User, Exercise, Found)
);

CREATE TABLE StartedLesson (
  Lesson   INTEGER,
  User     INTEGER,
  Round    NUMERIC NOT NULL DEFAULT 1,

  PRIMARY KEY(Lesson, User, Round),
  FOREIGN
    KEY              (Lesson)
    REFERENCES Lesson(Id),
  FOREIGN
    KEY            (User)
    REFERENCES User(Id)
);

CREATE TABLE FinishedLesson (
  Lesson   INTEGER,
  User     INTEGER,
  Score    BLOB NOT NULL,
  Round    NUMERIC NOT NULL DEFAULT 1,

  PRIMARY KEY (Lesson, User, Round),
  FOREIGN
    KEY            (User)
    REFERENCES User(Id),
  FOREIGN
    KEY              (Lesson)
    REFERENCES Lesson(Id)
);

CREATE TABLE ExerciseList (
  User      INTEGER,
  Exercise  INTEGER,
  Round     NUMERIC NOT NULL DEFAULT 1,

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
  FROM FinishedExercise
  JOIN Exercise ON FinishedExercise.Exercise = Exercise.Id
  JOIN Lesson   ON Exercise.Lesson           = Lesson.Id
  JOIN User     ON FinishedExercise.User     = User.Id;


-- The passed exercises by user and lesson
DROP VIEW IF EXISTS PassedLesson;
CREATE VIEW PassedLesson AS
  SELECT
    FinishedLesson.*,
    MIN(IFNULL(COUNT(*),0),1) AS Passed
  FROM FinishedLesson
  GROUP BY Lesson, User;

DROP VIEW IF EXISTS ActiveLessonsForUser;
CREATE VIEW ActiveLessonsForUser AS
SELECT
  Lesson.Id,
  Lesson.Name,
  Lesson.Description,
  COALESCE(ExerciseCount,0),
  Score,
  FinishedExercise.Exercise IS NOT NULL AS Finished,
  -- Exercise.Id,
  -- User.Id
  Lesson.Enabled,
  -- ExerciseList
  ExerciseList.User

FROM Exercise
JOIN Lesson ON Exercise.Lesson = Lesson.Id
LEFT JOIN ExerciseList ON ExerciseList.Exercise = Exercise.Id

-- FROM Exercise
-- JOIN ExerciseList ON ExerciseList.Exercise = Exercise.Id
-- JOIN Lesson on Lesson = Lesson.Id
-- LEFT JOIN User ON ExerciseList.User = User.Id

LEFT JOIN FinishedExercise
  ON FinishedExercise.User = ExerciseList.User
  AND FinishedExercise.Exercise = Exercise.Id;

COMMIT TRANSACTION;

