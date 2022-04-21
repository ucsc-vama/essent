organization := "io.github.ucsc-vama"

version := "0.8-SNAPSHOT"

name := "essent"

scalaVersion := "2.12.13"

scalacOptions ++= Seq("-deprecation", "-unchecked")

libraryDependencies += "com.github.scopt" %% "scopt" % "3.7.1"

libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.0" % "test"

libraryDependencies += "org.json4s" %% "json4s-native" % "3.6.9"

libraryDependencies += "edu.berkeley.cs" %% "firrtl" % "1.4.3"

libraryDependencies += "com.lihaoyi" %% "os-lib" % "0.2.7"


// Assembly

assemblyJarName in assembly := "essent.jar"

assemblyOutputPath in assembly := file("./utils/bin/essent.jar")


// Ignore disabled .scala files
unmanagedSources / excludeFilter := HiddenFileFilter || "*disabled*.scala"



// Publishing setup
publishMavenStyle := true
publishArtifact in Test := false
pomIncludeRepository := { x => false }

// POM info
pomExtra := (
<url>https://github.com/ucsc-vama/essent</url>
<licenses>
  <license>
    <name>BSD-style</name>
    <url>hhttps://opensource.org/licenses/BSD-3-Clause</url>
    <distribution>repo</distribution>
  </license>
</licenses>
<developers>
  <developer>
    <id>sbeamer</id>
    <name>Scott Beamer</name>
    <email>sbeamer@ucsc.edu</email>
    <organization>UC Santa Cruz</organization>
  </developer>
</developers>
)

publishTo := {
  val v = version.value
  val nexus = "https://s01.oss.sonatype.org/"
  if (v.trim.endsWith("SNAPSHOT")) {
    Some("snapshots".at(nexus + "content/repositories/snapshots"))
  } else {
    Some("releases".at(nexus + "service/local/staging/deploy/maven2"))
  }
}
