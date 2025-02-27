plugins {
    application
    antlr

    id("com.gradleup.shadow") version "8.3.6"
}

repositories {
    mavenCentral()
}

dependencies {
    antlr("org.antlr:antlr4:4.13.2")
}

java {
    toolchain {
        languageVersion = JavaLanguageVersion.of(21)
    }
}

application {
    mainClass = "libslprinter.Main"
}

tasks.jar {
    manifest {
        attributes["Main-Class"] = application.mainClass
    }
}

tasks.generateGrammarSource {
    val pkg = "libslprinter"
    arguments = arguments + listOf("-package", pkg)
    outputDirectory = outputDirectory.resolve(pkg)
}