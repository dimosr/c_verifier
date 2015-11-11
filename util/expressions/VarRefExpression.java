package util.expressions;

import java.util.Map;
import tool.VariablesMapping;

public class VarRefExpression extends Expression {
    
    public String variableName;
    
    public VarRefExpression(String variableName) {
        this.variableName = variableName;
    }
    
    public ExpressionType getType() {
        return ExpressionType.VARIABLE_REFERENCE;
    }
    
    public Expression applyMappings(VariablesMapping mapping, Expression result) {
        Integer variableIndex = mapping.getVarIndex(variableName);
        String variableSsaName = variableName;
        if(mapping.isLocal(variableSsaName))        
            variableSsaName = variableSsaName + variableIndex;
        else if(mapping.isGlobal(variableSsaName)) {
            variableSsaName = "G__" + variableSsaName + variableIndex;
        }
        return new VarRefExpression(variableSsaName);
    }
    
    public Expression applySummarisationMappings(VariablesMapping mapping, Map<String, Expression> parametersMapping, Expression resultExpr) {
        boolean isFormalParam = parametersMapping.containsKey(variableName);
        if(isFormalParam) {
            Expression actualParam = parametersMapping.get(variableName);
            return actualParam;
        }
        else{
            return this;
        }
    }
}
