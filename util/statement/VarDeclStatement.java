package util.statement;

import java.util.Set;
import tool.VariablesMapping;
import util.expressions.Expression;


public class VarDeclStatement extends Statement {
    public String variable;
    
    public VarDeclStatement(String variable) {
        this.variable = variable;
    }
    
    public StatementType getType() {
        return StatementType.VARDECL;
    }
    
    public Set<String> getModifiedSet() {
        return null;
    }
    
}
