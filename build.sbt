organization := "ucsc.edu"

version := "0.8"

name := "essent"

scalaVersion := "2.12.11"

scalacOptions ++= Seq("-deprecation", "-unchecked")

libraryDependencies += "com.github.scopt" %% "scopt" % "3.7.1"

libraryDependencies += "org.scalatest" %% "scalatest" % "3.1.2" % "test"

libraryDependencies += "org.json4s" %% "json4s-native" % "3.6.7"

libraryDependencies += "edu.berkeley.cs" %% "firrtl" % "1.3.3-HACK"

libraryDependencies += "org.scala-lang.modules" %% "scala-xml" % "2.0.0-RC1"

mainClass in (Compile, run) := Some("essent.Driver")

// Assembly

test in assembly := {} // FIXME - remove this hack
assemblyJarName in assembly := "essent.jar"

assemblyOutputPath in assembly := file("./utils/bin/essent.jar")

mainClass in (Compile, packageBin) := Some("essent.Driver")


// Ignore disabled .scala files
unmanagedSources / excludeFilter := HiddenFileFilter || "*disabled*.scala"

//scalacOptions += "-Xlog-implicits"