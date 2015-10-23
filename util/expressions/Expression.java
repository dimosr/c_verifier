package util.expressions;

import java.util.ArrayList;
import java.util.List;

/**
 * Contains the expression as a list of strings (variables-constants & operators)
 */
public class Expression {
    private List<String> elements;
    
    public Expression() {
        elements = new ArrayList<String>();
    }
    
    public void addElement(String element) {
        elements.add(element);
    }
    
    
    @Override
    public String toString(){
        StringBuilder expressionString = new StringBuilder();
        for(String element : elements){
            expressionString.append(" ");
            expressionString.append(element);
            expressionString.append(" ");
        }
        return expressionString.toString();
    }
}
