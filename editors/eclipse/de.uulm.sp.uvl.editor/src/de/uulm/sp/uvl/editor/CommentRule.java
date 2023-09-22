package de.uulm.sp.uvl.editor;

import org.eclipse.jface.text.rules.ICharacterScanner;
import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.Token;


public class CommentRule implements IRule {

    private final Token token;
    

    public CommentRule(Token token) {
        this.token = token;
    }

    @Override
    public IToken evaluate(ICharacterScanner scanner) {
        int c = scanner.read();
        if ('/' == c) {
    		c = scanner.read();
    		if ('/' == c) {
    			while (c != ICharacterScanner.EOF) {
    	        	if ('\n' == c || '\r' == c) {
    	        		return token;
    	            }
    	            c = scanner.read();
    	        }
    		} else {
    			scanner.unread();
    		}
    	}
        scanner.unread();

        return Token.UNDEFINED;
    }

}
