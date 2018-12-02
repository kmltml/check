scalaVersion in ThisBuild := "2.12.6"

lazy val core = project.in(file("core"))
  .settings(
    libraryDependencies ++= Seq(
      "org.typelevel" %% "cats-core" % "1.5.0"
    ),
    initialCommands in console := "import check._, calculus._, Term._, Sandbox._, Typechecker._\n"
  )
