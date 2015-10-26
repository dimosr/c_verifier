package util.expressions;

public class OldExpression extends Expression {
    
    public String variableName;
    
    public OldExpression(String variableName) {
        this.variableName = variableName;
    }
    
    public ExpressionType getType() {
        return ExpressionType.OLD;
    }
}
