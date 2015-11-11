package util.expressions;

import java.util.Map;
import tool.VariablesMapping;

public class ConstantExpression extends Expression {
    
    public String intValue;    //string representation used
    
    public ConstantExpression(String value) {
        intValue = value;
    }
    
    public ExpressionType getType() {
        return ExpressionType.CONSTANT;
    }
    
    public Expression applyMappings(VariablesMapping mapping, Expression result) {
        return new ConstantExpression(intValue);
    }
    
    public Expression applySummarisationMappings(VariablesMapping mapping, Map<String, Expression> parametersMapping, Expression resultExpr) {
        return new ConstantExpression(intValue);
    }
}
