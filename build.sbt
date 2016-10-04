organization := "lbl.gov"

version := "0.1"

name := "saga"

scalaVersion := "2.11.7"

scalacOptions ++= Seq("-deprecation", "-unchecked")

lazy val firrtl = (project in file("firrtl"))

lazy val root = (project in file(".")).dependsOn(firrtl)
