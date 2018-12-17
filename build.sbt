scalaVersion in ThisBuild := "2.12.6"

lazy val core = project.in(file("core"))
  .settings(
    organization := "local",
    name := "check-core",
    version := "0.1-SNAPSHOT",
    libraryDependencies ++= Seq(
      "org.typelevel" %% "cats-core" % "1.5.0",
      "org.atnos" %% "eff" % "5.3.0"
    ),
    initialCommands in console := "import check._, calculus._, Term._, Sandbox._, Typechecker._\n",
    resolvers += Resolver.sonatypeRepo("releases"),

    addCompilerPlugin("org.spire-math" %% "kind-projector" % "0.9.8"),

    scalacOptions += "-Ypartial-unification"
  )
