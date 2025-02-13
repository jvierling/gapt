resolvers += Classpaths.sbtPluginReleases
logLevel := Level.Warn

libraryDependencies += "org.apache.commons" % "commons-compress" % "1.19"

addSbtPlugin( "org.scoverage" %% "sbt-scoverage" % "1.6.0" )

// Provides an assembly task which produces a fat jar with all dependencies included.
addSbtPlugin( "com.eed3si9n" % "sbt-assembly" % "0.14.10" )

addSbtPlugin( "com.eed3si9n" % "sbt-unidoc" % "0.4.2" )

addSbtPlugin( "org.scalariform" % "sbt-scalariform" % "1.8.3" )

addSbtPlugin( "org.xerial.sbt" % "sbt-sonatype" % "3.9.12" )

addSbtPlugin( "com.github.sbt" % "sbt-pgp" % "2.1.2" )
