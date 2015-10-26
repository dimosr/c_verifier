package util.expressions;

public class ParenthesisExpression extends Expression {
    
    public Expression expr;
    
    public ParenthesisExpression(Expression expr) {
        this.expr = expr;
    }
    
    public ExpressionType getType() {
        return ExpressionType.PARENTHESIS;
    }
}
