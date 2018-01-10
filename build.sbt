organization := "lbl.gov"

version := "0.1"

name := "essent"

scalaVersion := "2.11.11"

scalacOptions ++= Seq("-deprecation", "-unchecked")

libraryDependencies += "com.github.scopt" %% "scopt" % "3.6.0"

libraryDependencies += "com.typesafe.scala-logging" %% "scala-logging" % "3.7.2"

libraryDependencies += "ch.qos.logback" % "logback-classic" % "1.2.3"

lazy val firrtl = (project in file("firrtl"))

lazy val essent = (project in file(".")).dependsOn(firrtl)
