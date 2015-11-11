package util.expressions;

import tool.VariablesMapping;


public class OldExpression extends Expression {
    public String variableName;
    
    public OldExpression(String variableName) {
        this.variableName = variableName;
    }

    public ExpressionType getType() {
        return ExpressionType.OLD;
    }
    
    public Expression applyMappings(VariablesMapping mapping, boolean inSummarisation, Expression result) {
        VarRefExpression oldExpr = null;
        if( !inSummarisation ){      //\old present in pre-post conditions or expressions of procedure under verification
            String ssaVariableName = "G__" + variableName + "0";
            oldExpr = new VarRefExpression(ssaVariableName);
        }
        else {           //\old present in pre-post conditions of called procedure
            String ssaVariableName = "G__" + variableName + mapping.getGlobalIndex(variableName);
            oldExpr = new VarRefExpression(ssaVariableName);
        }
        return oldExpr;
    }
}
