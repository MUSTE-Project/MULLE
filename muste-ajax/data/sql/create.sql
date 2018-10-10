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
Username TEXT NOT NULL,
Password BLOB NOT NULL,
Salt BLOB NOT NULL,
Enabled BOOL NOT NULL DEFAULT 0,
PRIMARY KEY(Username));

CREATE TABLE Session (
User TEXT NOT NULL REFERENCES User(Username),
Token TEXT,
Starttime NUMERIC NOT NULL DEFAULT CURRENT_TIMESTAMP,
LastActive NUMERIC NOT NULL DEFAULT CURRENT_TIMESTAMP,
PRIMARY KEY(Token));

CREATE TABLE Exercise (
SourceTree BLOB,
TargetTree BLOB,
Lesson TEXT,
Timeout NUMERIC NOT NULL DEFAULT 0,
PRIMARY KEY(SourceTree, TargetTree, Lesson),
FOREIGN KEY(Lesson) References Lesson(Name));

CREATE TABLE Lesson (
Name TEXT,
Description TEXT NOT NULL,
Grammar TEXT NOT NULL,
SourceLanguage TEXT NOT NULL,
TargetLanguage TEXT NOT NULL,
-- TODO Create a view where this is a computed column.
ExerciseCount NUMERIC NOT NULL,
Enabled BOOL NOT NULL DEFAULT 0,
SearchLimitDepth INT DEFAULT NULL,
SearchLimitSize INT DEFAULT NULL,
Repeatable BOOL NOT NULL DEFAULT 1,
PRIMARY KEY(Name));

CREATE TABLE FinishedExercise (
  User TEXT,
  SourceTree BLOB,
  TargetTree BLOB,
  Lesson TEXT,
  Score BLOB NOT NULL,
  Round NUMERIC NOT NULL,
  PRIMARY
    KEY (User,SourceTree, TargetTree, Lesson, Round),
  FOREIGN
    KEY (User)
    REFERENCES User(Username),
  FOREIGN
    KEY (SourceTree, TargetTree, Lesson)
    REFERENCES Exercise(SourceTree, TargetTree, Lesson)
  -- I don't think this is what we want.
  -- UNIQUE (User, Lesson)
);

CREATE TABLE StartedLesson (
Lesson TEXT,
User TEXT,
Round NUMERIC NOT NULL DEFAULT 1,
PRIMARY KEY(Lesson, User, Round),
FOREIGN KEY(Lesson) REFERENCES Lesson(Name), FOREIGN KEY(User) REFERENCES User(Username));

CREATE TABLE FinishedLesson (
Lesson TEXT,
User TEXT,
Score BLOB NOT NULL,
Round NUMERIC NOT NULL DEFAULT 1,
PRIMARY KEY (Lesson, User, Round),
FOREIGN KEY (User) REFERENCES User(Username),
FOREIGN KEY (Lesson) REFERENCES Lesson(Name));

CREATE TABLE ExerciseList (
User TEXT,
SourceTree BLOB,
TargetTree BLOB,
Lesson TEXT,
Round NUMERIC NOT NULL DEFAULT 1,
PRIMARY KEY (User, SourceTree, TargetTree, Lesson, Round),
FOREIGN KEY(User) REFERENCES User(Username),
FOREIGN KEY(SourceTree,TargetTree, Lesson) REFERENCES Exercise (SourceTree, TargetTree, Lesson));

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
LEFT JOIN FinishedExercise ON Lesson.Name = FinishedExercise.Lesson
LEFT JOIN PassedLesson     ON Lesson.Name = PassedLesson.Lesson;


DROP VIEW IF EXISTS ActiveLesson;
CREATE VIEW ActiveLesson AS
SELECT
  Lesson.*,
  FinishedExercise.Score AS ExerciseScore,
FROM Lesson
LEFT JOIN StartedLesson      ON Lesson.Name = StartedLesson.Lesson
LEFT JOIN FinishedExercise   ON Lesson.Name = FinishedExercise.Lesson
LEFT JOIN FinishedLesson     ON Lesson.Name = FinishedLesson.Lesson;

COMMIT TRANSACTION;
