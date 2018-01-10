organization := "lbl.gov"

version := "0.1"

name := "essent"

scalaVersion := "2.11.11"

scalacOptions ++= Seq("-deprecation", "-unchecked")

libraryDependencies += "com.github.scopt" %% "scopt" % "3.5.0"

lazy val firrtl = (project in file("firrtl"))

lazy val essent = (project in file(".")).dependsOn(firrtl)
