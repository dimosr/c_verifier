package util.expressions;

import tool.VariablesMapping;

public class ResultExpression extends Expression {

    public ExpressionType getType() {
        return ExpressionType.RESULT;
    }
    
    public Expression applyMappings(VariablesMapping mapping, boolean inSummarisation, Expression result) {
        return result.applyMappings(mapping, inSummarisation, result);
    }
}
