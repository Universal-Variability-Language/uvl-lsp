package de.uulm.sp.uvl.editor;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.presentation.PresentationReconciler;
import org.eclipse.jface.text.rules.DefaultDamagerRepairer;
import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.NumberRule;
import org.eclipse.jface.text.rules.RuleBasedScanner;
import org.eclipse.jface.text.rules.Token;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Display;

public class PropertiesReconciler extends PresentationReconciler {

    public PropertiesReconciler() {
        RuleBasedScanner scanner = new RuleBasedScanner();
        IRule ruleTopLevel = new KeywordRule( new Token(new TextAttribute(Display.getCurrent().getSystemColor(
        		SWT.COLOR_MAGENTA))), 
        		new String[] {
        	    		"namespace",
        	    		"include",
        	    		"imports",
        	    		"features",
        	    		"constraints",
        	    		"incomplete_namespace"
        	    	});

        IRule ruleType = new KeywordRule( new Token(new TextAttribute(Display.getCurrent().getSystemColor(
        		SWT.COLOR_BLUE))), 
        		new String[] {
        	    		"String",
        	    		"Real",
        	    		"Integer",
        	    		"Boolean",
        	    	});

        IRule ruleGroup = new KeywordRule( new Token(new TextAttribute(Display.getCurrent().getSystemColor(
        		SWT.COLOR_MAGENTA))), 
        		new String[] {
        	    		"mandatory",
        	    		"or",
        	    		"optional",
        	    		"alternative",
        	    	});

        IRule ruleFunction = new KeywordRule( new Token(new TextAttribute(Display.getCurrent().getSystemColor(
        		SWT.COLOR_YELLOW))), 
        		new String[] {
        	    		"len",
        	    		"floor",
        	    		"cell",
        	    		"sum",
        	    		"avg"
        	    	});

        IRule ruleNumber = new NumberRule( new Token(new TextAttribute(Display.getCurrent().getSystemColor(
        		SWT.COLOR_DARK_YELLOW))));

        IRule ruleString = new StringRule( new Token(new TextAttribute(Display.getCurrent().getSystemColor(
        		SWT.COLOR_DARK_RED))));
        IRule ruleComment = new CommentRule( new Token(new TextAttribute(Display.getCurrent().getSystemColor(
        		SWT.COLOR_GREEN))));




        scanner.setRules(new IRule[] { ruleTopLevel, ruleType, ruleGroup, ruleFunction, ruleNumber, ruleComment, ruleString });
        DefaultDamagerRepairer dr = new DefaultDamagerRepairer(scanner);
        this.setDamager(dr, IDocument.DEFAULT_CONTENT_TYPE);
        this.setRepairer(dr, IDocument.DEFAULT_CONTENT_TYPE);
    }
}