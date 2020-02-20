ThisBuild / organization := "ch.epfl"
ThisBuild / version      := "2020"
ThisBuild / maintainer   := "michel.schinz@epfl.ch"

ThisBuild / scalaVersion := "2.13.1"

val javaMemOptions = Seq("-Xss32M", "-Xms128M")

lazy val root = (project in file("."))
  // Enable packaging of the L3 compiler so that it can be run without SBT.
  // See documentation at https://www.scala-sbt.org/sbt-native-packager/
  // Among the tasks added by this plugin, the most useful are:
  // - "stage" to create the scripts locally in target/universal/stage/bin,
  // - "dist" to create a Zip archive in target/universal.
  .enablePlugins(JavaAppPackaging)
  .settings(
  name := "l3c",

  scalacOptions ++= Seq("-feature",
                        "-deprecation",
                        "-unchecked",
                        "-encoding", "utf-8"),

  // Main configuration
  scalaSource in Compile := baseDirectory.value / "src",
  libraryDependencies ++= Seq(
    "com.lihaoyi"   %% "fastparse"   % "2.2.2",
    "org.typelevel" %% "paiges-core" % "0.3.0"),

  fork in run := true,
  connectInput in run := true,
  outputStrategy in run := Some(StdoutOutput),
  javaOptions in run ++= javaMemOptions,

  // Test configuration
  scalaSource in Test := baseDirectory.value / "test",
  libraryDependencies += "com.lihaoyi" %% "utest" % "0.7.3" % "test",
  testFrameworks += new TestFramework("utest.runner.Framework"),

  fork in Test := true,
  javaOptions in Test ++= javaMemOptions,

  // Packaging configuration (sbt-native-packager)
  mappings in (Compile, packageDoc) := Seq(),
  javaOptions in Universal ++= javaMemOptions map ("-J" + _))

