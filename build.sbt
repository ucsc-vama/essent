organization := "ucsc.edu"
name := "essent"
version := "0.5-SNAPSHOT"

// scala settings
scalaVersion := "2.12.14"
crossScalaVersions := Seq("2.13.6", "2.12.14")
scalacOptions ++= Seq("-deprecation", "-unchecked")
// Always target Java8 for maximum compatibility
javacOptions ++= Seq("-source", "1.8", "-target", "1.8")

resolvers ++= Seq(Resolver.sonatypeRepo("snapshots"))
libraryDependencies += "edu.berkeley.cs" %% "firrtl" % "1.5-SNAPSHOT"
libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.0" % "test"

// Assembly
assemblyJarName in assembly := "essent.jar"
assemblyOutputPath in assembly := file("./utils/bin/essent.jar")

// Ignore disabled .scala files
unmanagedSources / excludeFilter := HiddenFileFilter || "*disabled*.scala"

// publishing settings
publishMavenStyle := true
publishArtifact in Test := false
pomIncludeRepository := { x => false }

// scm is set by sbt-ci-release
pomExtra := (
<url>https://github.com/ucsc-vama/essent</url>
  <licenses>
    <license>
      <name>BSD-style</name>
      <url>http://www.opensource.org/licenses/bsd-license.php</url>
      <distribution>repo</distribution>
    </license>
  </licenses>
<developers>
  <developer>
    <id>sbeamer</id>
    <name>Scott Beamer</name>
  </developer>
</developers>
)

publishTo := {
  val v = version.value
  val nexus = "https://oss.sonatype.org/"
  if (v.trim.endsWith("SNAPSHOT")) {
    Some("snapshots".at(nexus + "content/repositories/snapshots"))
  } else {
    Some("releases".at(nexus + "service/local/staging/deploy/maven2"))
  }
}
