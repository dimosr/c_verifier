package util.expressions;

import java.util.ArrayList;
import java.util.List;

/**
 * Contains the expression as a list of strings (variables-constants & operators)
 */
public class Expression {
    List<String> elements;
    
    public Expression() {
        elements = new ArrayList<String>();
    }
}
