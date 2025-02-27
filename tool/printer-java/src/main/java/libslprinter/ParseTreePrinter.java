package libslprinter;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.tree.ErrorNode;
import org.antlr.v4.runtime.tree.ParseTreeListener;
import org.antlr.v4.runtime.tree.TerminalNode;

import java.io.PrintStream;

public class ParseTreePrinter implements ParseTreeListener {
    private int level = 0;
    private final PrintStream out = System.out;

    private void printIndent() {
        out.print("  ".repeat(level));
    }

    private void printEscaped(String s) {
        out.print('"');

        for (char c : s.toCharArray()) {
            if (c == '\0') {
                out.print("\\0");
            } else if (c == '\n') {
                out.print("\\n");
            } else if (c == '\r') {
                out.print("\\r");
            } else if (c == '\t') {
                out.print("\\t");
            } else if (c == '"' || c == '\\') {
                out.print('\\');
                out.print(c);
            } else if (c < ' ' || c == 0x7f) {
                out.printf("\\x%02x", (int) c);
            } else {
                out.print(c);
            }
        }

        out.print('"');
    }

    @Override
    public void enterEveryRule(ParserRuleContext ctx) {
        printIndent();
        var ruleIdx = ctx.getRuleIndex();
        var ruleNames = LibSLParser.ruleNames;
        var ruleName = ruleIdx < ruleNames.length ? ruleNames[ruleIdx] : "error";
        out.printf("Entered rule `%s`\n", ruleName);

        ++level;
    }

    @Override
    public void exitEveryRule(ParserRuleContext parserRuleContext) {
        --level;
    }

    @Override
    public void visitErrorNode(ErrorNode node) {
        printIndent();
        out.printf("Entered an error node: %s\n", node);
    }

    @Override
    public void visitTerminal(TerminalNode node) {
        printIndent();
        out.printf("Terminal %s ", node.getSymbol());
        printEscaped(node.getSymbol().getText());
        out.println();
    }
}
