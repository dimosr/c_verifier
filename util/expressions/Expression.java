package util.expressions;

import tool.VariablesMapping;

public abstract class Expression {
    public abstract ExpressionType getType();
    public abstract Expression applyMappings(VariablesMapping mapping, boolean inSummarisation, Expression result);
}
