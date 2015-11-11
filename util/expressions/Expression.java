package util.expressions;

import java.util.Map;
import tool.VariablesMapping;

public abstract class Expression {
    public abstract ExpressionType getType();
    public abstract Expression applyMappings(VariablesMapping mapping, Expression result);
    public abstract Expression applySummarisationMappings(VariablesMapping mapping, Map<String, Expression> parametersMapping, Expression resultExpr);
}
