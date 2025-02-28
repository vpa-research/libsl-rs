package libslprinter;

import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;

import java.io.IOException;
import java.nio.charset.StandardCharsets;

public class Main {
    public static void main(String[] args) {
        if (args.length != 2) {
            printUsage();
            System.exit(1);
        }

        var mode = switch (args[0].toLowerCase()) {
            case "tokens" -> Mode.TOKENS;
            case "parse-tree" -> Mode.PARSE_TREE;
            default -> {
                System.err.println("Invalid command: " + args[1]);
                printUsage();
                System.exit(1);
                throw new RuntimeException("unreachable");
            }
        };

        try {
            new Main().run(args[1], mode);
        } catch (Exception e) {
            System.err.printf("Encountered a failure: %s!\n", e);
            e.printStackTrace(System.err);
            System.exit(1);
        }
    }

    private static void printUsage() {
        System.err.println("Usage: java -jar printer-java.jar {tokens|parse-tree} <path to source file>");
    }

    private void run(String path, Mode mode) throws IOException {
        var stream = CharStreams.fromFileName(path, StandardCharsets.UTF_8);
        var lexer = new LibSLLexer(stream);

        if (mode == Mode.TOKENS) {
            printTokens(lexer);
            return;
        }

        printParseTree(lexer);
    }

    private void printTokens(LibSLLexer lexer) {
        for (int idx = 0;; ++idx) {
            var token = lexer.nextToken();
            var tokenName = lexer.getVocabulary().getSymbolicName(token.getType());
            System.out.printf(
                "Token %d: channel %s, type %s, %s\n",
                idx,
                getName(lexer.getChannelNames(), token.getChannel()),
                tokenName == null ? "[unknown]" : tokenName,
                token
            );

            if (token.getType() == LibSLLexer.EOF) {
                break;
            }
        }
    }

    private static String getName(String[] names, int idx) {
        return 0 <= idx && idx < names.length ? names[idx] : "[unknown]";
    }

    private void printParseTree(LibSLLexer lexer) {
        var tokens = new CommonTokenStream(lexer);
        var parser = new LibSLParser(tokens);
        var printer = new ParseTreePrinter();
        parser.setBuildParseTree(false);
        parser.addParseListener(printer);
        parser.removeErrorListeners();
        parser.file();
    }

    private enum Mode {
        TOKENS,
        PARSE_TREE,
    }
}
