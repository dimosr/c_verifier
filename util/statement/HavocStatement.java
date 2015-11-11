package util.statement;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import util.program.Program;


public class HavocStatement extends Statement {
    public String variable;
    
    public HavocStatement(String variable) {
        this.variable = variable;
    }
    
    public StatementType getType() {
        return StatementType.HAVOC;
    }
    
    public Set<String> getModifiedSet(Program program, List<String> localVariables) {
        Set<String> modSet = new HashSet();
        modSet.add(variable);
        return modSet;
    }
}
