package de.uulm.sp.uvl.editor;

import java.util.Arrays;

import org.eclipse.jface.text.rules.ICharacterScanner;
import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.Token;


public class KeywordRule implements IRule {

    private final Token token;
    private String[] KEYWORDS;
    

    public KeywordRule(Token token, String[] keywords) {
        this.token = token;
        this.KEYWORDS = keywords;
    }

    @Override
    public IToken evaluate(ICharacterScanner scanner) {
        int c = scanner.read();
        int count = 1;
        String s = "";

        while (c != ICharacterScanner.EOF) {
        	s += (char)c;
        	if(Arrays.asList(this.KEYWORDS).contains(s)) {
        		return token;
        	}
        	if ('\n' == c || '\r' == c) {
                break;
            }
            count++;
            c = scanner.read();
        }

        // put the scanner back to the original position if no match
        for (int i = 0; i < count; i++) {
            scanner.unread();
        }

        return Token.UNDEFINED;
    }

}
