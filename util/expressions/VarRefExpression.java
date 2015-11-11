package util.expressions;

import tool.VariablesMapping;

public class VarRefExpression extends Expression {
    
    public String variableName;
    
    public VarRefExpression(String variableName) {
        this.variableName = variableName;
    }
    
    public ExpressionType getType() {
        return ExpressionType.VARIABLE_REFERENCE;
    }
    
    public Expression applyMappings(VariablesMapping mapping, boolean inSummarisation, Expression result) {
        Integer variableIndex = mapping.getVarIndex(variableName);
        String variableSsaName = null;
        if(mapping.isLocal(variableName))        
            variableSsaName = variableName + variableIndex;
        else if(mapping.isGlobal(variableName)) {
            variableSsaName = "G__" + variableName + variableIndex;
        }
        return new VarRefExpression(variableSsaName);
    }
}
