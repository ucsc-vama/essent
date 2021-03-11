organization := "ucsc.edu"
version := "0.5-SNAPSHOT"
name := "essent"
scalaVersion := "2.12.11"

scalacOptions ++= Seq("-deprecation", "-unchecked")

resolvers ++= Seq(Resolver.sonatypeRepo("snapshots"))
libraryDependencies += "edu.berkeley.cs" %% "firrtl" % "1.5-SNAPSHOT"
libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.0" % "test"

// Assembly
assemblyJarName in assembly := "essent.jar"
assemblyOutputPath in assembly := file("./utils/bin/essent.jar")

// Ignore disabled .scala files
unmanagedSources / excludeFilter := HiddenFileFilter || "*disabled*.scala"
