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
  Id        INTEGER PRIMARY KEY ASC,
  Username  TEXT NOT NULL UNIQUE,
  Password  BLOB NOT NULL,
  Salt      BLOB NOT NULL,
  Enabled   BOOL NOT NULL DEFAULT 0
);

CREATE TABLE Session (
  Id          INTEGER PRIMARY KEY,
  User        INTEGER NOT NULL,
  Token       TEXT,
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

CREATE TABLE FinishedExercise (
  User      INTEGER,
  Exercise  INTEGER,
  Score     BLOB NOT NULL,
  Round     NUMERIC NOT NULL,

  PRIMARY
    KEY (User, Exercise, Round),
  FOREIGN
    KEY (User)
    REFERENCES User(Id),
  FOREIGN
    KEY (Exercise)
    REFERENCES Exercise(Id)
);

CREATE TABLE StartedLesson (
  Lesson   INTEGER,
  User     INTEGER,
  Round    NUMERIC NOT NULL DEFAULT 1,

  PRIMARY KEY(Lesson, User, Round),
  FOREIGN
    KEY (Lesson)
    REFERENCES Lesson(Id),
  FOREIGN
    KEY (User)
    REFERENCES User(Id)
);

CREATE TABLE FinishedLesson (
  Lesson   TEXT,
  User     TEXT,
  Score    BLOB NOT NULL,
  Round    NUMERIC NOT NULL DEFAULT 1,

  PRIMARY KEY (Lesson, User, Round),
  FOREIGN
    KEY (User)
    REFERENCES User(Username),
  FOREIGN
    KEY (Lesson)
    REFERENCES Lesson(Name)
);

CREATE TABLE ExerciseList (
  User      INTEGER,
  Exercise  INTEGER,
  Round     NUMERIC NOT NULL DEFAULT 1,

  PRIMARY KEY (User, Exercise, Round),
  FOREIGN KEY(User)     REFERENCES User(Id),
  FOREIGN KEY(Exercise) REFERENCES Exercise (Id)
);

-- The most natural thing...
DROP VIEW IF EXISTS ExerciseLesson;
CREATE VIEW ExerciseLesson AS
SELECT *
FROM Lesson
JOIN Exercise ON Name = Lesson;

DROP VIEW IF EXISTS FinishedExerciseLesson;
CREATE VIEW FinishedExerciseLesson AS
SELECT *
FROM FinishedExercise
JOIN Exercise ON FinishedExercise.Exercise = Exercise.Id
JOIN Lesson   ON Exercise.Lesson = Lesson.Id
JOIN User     ON User.Id = FinishedExercise.User;


-- The passed exercises by user and lesson
DROP VIEW IF EXISTS PassedLesson;
CREATE VIEW PassedLesson AS
SELECT
  FinishedLesson.*,
  MIN(IFNULL(COUNT(*),0),1) AS Passed
FROM FinishedLesson
GROUP BY Lesson, User;

DROP VIEW IF EXISTS ActiveLesson;
CREATE VIEW ActiveLesson AS
SELECT
  Lesson.Id as Lesson,
  Lesson.Name,
  Lesson.Description,
  Lesson.ExerciseCount,
  FinishedExercise.Score,
  -- FIXME Same as above.
  COALESCE(PassedLesson.Passed, 0) AS Finished,
  Lesson.Enabled,
  StartedLesson.User
FROM Lesson
LEFT JOIN StartedLesson    ON Lesson.Name = StartedLesson.Lesson
LEFT JOIN FinishedExerciseLesson ON Lesson.Name = FinishedExerciseLesson.Lesson
LEFT JOIN PassedLesson     ON Lesson.Name = PassedLesson.Lesson;


DROP VIEW IF EXISTS ActiveLesson;
CREATE VIEW ActiveLesson AS
SELECT
  Lesson.*,
  FinishedExerciseLesson.Score AS ExerciseScore,
  FinishedExerciseLesson.User
FROM Lesson
LEFT JOIN StartedLesson      ON Lesson.Name = StartedLesson.Lesson
LEFT JOIN FinishedExerciseLesson   ON Lesson.Name = FinishedExerciseLesson.Lesson
LEFT JOIN FinishedLesson     ON Lesson.Name = FinishedLesson.Lesson;

COMMIT TRANSACTION;

