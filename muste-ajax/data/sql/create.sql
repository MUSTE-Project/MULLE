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
SourceTree TEXT,
TargetTree TEXT,
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
ExerciseCount NUMERIC NOT NULL,
Enabled BOOL NOT NULL DEFAULT 0,
Repeatable BOOL NOT NULL DEFAULT 1,
PRIMARY KEY(Name));

CREATE TABLE FinishedExercise (
User TEXT,
SourceTree TEXT,
TargetTree TEXT,
Lesson TEXT,
Time NUMERIC NOT NULL,
ClickCount NUMERIC NOT NULL,
Round NUMERIC NOT NULL,
PRIMARY KEY (User,SourceTree, TargetTree, Lesson, Round),
FOREIGN KEY (User) REFERENCES User(Username),
FOREIGN KEY(SourceTree, TargetTree, Lesson) REFERENCES Exercise(SourceTree, TargetTree, Lesson));

CREATE TABLE StartedLesson (
Lesson TEXT,
User TEXT,
Round NUMERIC NOT NULL DEFAULT 1,
PRIMARY KEY(Lesson, User, Round),
FOREIGN KEY(Lesson) REFERENCES Lesson(Name), FOREIGN KEY(User) REFERENCES User(Username));

CREATE TABLE FinishedLesson (
Lesson TEXT,
User TEXT,
Time NUMERIC NOT NULL,
ClickCount NUMERIC NOT NULL,
Round NUMERIC NOT NULL DEFAULT 1,
PRIMARY KEY (Lesson, User, Round),
FOREIGN KEY (User) REFERENCES User(Username),
FOREIGN KEY (Lesson) REFERENCES Lesson(Name));

CREATE TABLE ExerciseList (
User TEXT,
SourceTree TEXT,
TargetTree TEXT,
Lesson TEXT,
Round NUMERIC NOT NULL DEFAULT 1,
PRIMARY KEY (User, SourceTree, TargetTree, Lesson, Round),
FOREIGN KEY(User) REFERENCES User(Username),
FOREIGN KEY(SourceTree,TargetTree, Lesson) REFERENCES Exercise (SourceTree, TargetTree, Lesson));

COMMIT TRANSACTION;
