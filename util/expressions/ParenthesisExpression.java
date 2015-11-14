package util.expressions;

import java.util.Map;
import tool.verif.structs.VariablesMapping;

public class ParenthesisExpression extends Expression {
    
    public Expression expr;
    
    public ParenthesisExpression(Expression expr) {
        this.expr = expr;
    }
    
    public ExpressionType getType() {
        return ExpressionType.PARENTHESIS;
    }
    
    public Expression applyMappings(VariablesMapping mapping, Expression result) {
        return new ParenthesisExpression(expr.applyMappings(mapping, result));
    }
    
    public Expression applySummarisationMappings(VariablesMapping mapping, Map<String, Expression> parametersMapping, Expression resultExpr) {
        return new ParenthesisExpression(expr.applySummarisationMappings(mapping, parametersMapping, resultExpr));
    }
}
