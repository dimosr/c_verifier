package util.expressions;

import tool.VariablesMapping;

public class ParenthesisExpression extends Expression {
    
    public Expression expr;
    
    public ParenthesisExpression(Expression expr) {
        this.expr = expr;
    }
    
    public ExpressionType getType() {
        return ExpressionType.PARENTHESIS;
    }
    
    public Expression applyMappings(VariablesMapping mapping, boolean inSummarisation, Expression result) {
        return new ParenthesisExpression(expr.applyMappings(mapping, inSummarisation, result));
    }
}
