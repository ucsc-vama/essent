organization := "ucsc.edu"
version := "0.4.8"
name := "essent"
scalaVersion := "2.12.11"

scalacOptions ++= Seq("-deprecation", "-unchecked")
libraryDependencies += "edu.berkeley.cs" %% "firrtl" % "1.4.2"
libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.0" % "test"

// Assembly
assemblyJarName in assembly := "essent.jar"
assemblyOutputPath in assembly := file("./utils/bin/essent.jar")

// Ignore disabled .scala files
unmanagedSources / excludeFilter := HiddenFileFilter || "*disabled*.scala"
