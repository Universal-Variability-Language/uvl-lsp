package de.uulm.sp.uvl.editor;

import org.eclipse.jface.text.rules.ICharacterScanner;
import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.Token;


public class StringRule implements IRule {

    private final Token token;
    

    public StringRule(Token token) {
        this.token = token;
    }

    @Override
    public IToken evaluate(ICharacterScanner scanner) {
        int c = scanner.read();
        int count = 2;

        if (!('"' == c || '\'' == c)) {
        	scanner.unread();
        	return Token.UNDEFINED;
    	}
        c = scanner.read();
        while (c != ICharacterScanner.EOF) {
        	if ('"' == c || '\'' == c) {
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
