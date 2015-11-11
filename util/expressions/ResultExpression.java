package util.expressions;

import java.util.Map;
import tool.VariablesMapping;

public class ResultExpression extends Expression {

    public ExpressionType getType() {
        return ExpressionType.RESULT;
    }
    
    public Expression applyMappings(VariablesMapping mapping, Expression result) {
        return result.applyMappings(mapping, result);
    }
    
    public Expression applySummarisationMappings(VariablesMapping mapping, Map<String, Expression> parametersMapping, Expression resultExpr) {
        return resultExpr;
    }
}
