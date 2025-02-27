package libslprinter;

import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;

import java.io.IOException;
import java.nio.charset.StandardCharsets;

public class Main {
    public static void main(String[] args) {
        if (args.length != 1) {
            printUsage();
            System.exit(1);
        }

        try {
            new Main().run(args[0]);
        } catch (Exception e) {
            System.err.printf("Encountered a failure: %s!\n", e);
            e.printStackTrace(System.err);
            System.exit(1);
        }
    }

    private static void printUsage() {
        System.err.println("Usage: java -jar printer-java.jar <path to source file>");
    }

    private void run(String path) throws IOException {
        var stream = CharStreams.fromFileName(path, StandardCharsets.UTF_8);
        var lexer = new LibSLLexer(stream);
        var tokens = new CommonTokenStream(lexer);
        var parser = new LibSLParser(tokens);
        var printer = new ParseTreePrinter();
        parser.setBuildParseTree(false);
        parser.addParseListener(printer);
        parser.removeErrorListeners();
        parser.file();
    }
}
