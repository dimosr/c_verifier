package util.expressions;

public class VarRefExpression extends Expression {
    
    public String variableName;
    
    public VarRefExpression(String variableName) {
        this.variableName = variableName;
    }
    
    public ExpressionType getType() {
        return ExpressionType.VARIABLE_REFERENCE;
    }
}
