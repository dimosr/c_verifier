package util.statement;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import tool.verif.structs.VariablesMapping;
import util.expressions.Expression;
import util.program.Program;


public class VarDeclStatement extends Statement {
    public String variable;
    
    public VarDeclStatement(String variable) {
        this.variable = variable;
    }
    
    public StatementType getType() {
        return StatementType.VARDECL;
    }
    
    public Set<String> getModifiedSet(Program program, List<String> localVariables) {
        return new HashSet();
    }
    
}
