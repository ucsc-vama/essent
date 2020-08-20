organization := "ucsc.edu"

version := "0.8"

name := "essent"

scalaVersion := "2.12.10"

scalacOptions ++= Seq("-deprecation", "-unchecked")

libraryDependencies += "com.github.scopt" %% "scopt" % "3.7.0"

libraryDependencies += "com.typesafe.scala-logging" %% "scala-logging" % "3.9.0"

libraryDependencies += "ch.qos.logback" % "logback-classic" % "1.2.3"

libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.1" % "test"

libraryDependencies += "org.json4s" %% "json4s-native" % "3.6.7"

libraryDependencies += "edu.berkeley.cs" %% "firrtl" % "1.2.1"


// Assembly

assemblyJarName in assembly := "essent.jar"

assemblyOutputPath in assembly := file("./utils/bin/essent.jar")


// Ignore disabled .scala files
unmanagedSources / excludeFilter := HiddenFileFilter || "*disabled*.scala"
