package util.program;

import util.expressions.Expression;

public class Assignment {
    public String variableName;
    public Expression expression;
    
    public Assignment(String variableName,Expression expression) {
        this.variableName = variableName;
        this.expression = expression;
    }
}
