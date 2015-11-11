package util.expressions;

import tool.VariablesMapping;

public class ConstantExpression extends Expression {
    
    public String intValue;    //string representation used
    
    public ConstantExpression(String value) {
        intValue = value;
    }
    
    public ExpressionType getType() {
        return ExpressionType.CONSTANT;
    }
    
    public Expression applyMappings(VariablesMapping mapping, boolean inSummarisation, Expression result) {
        return new ConstantExpression(intValue);
    }
}
