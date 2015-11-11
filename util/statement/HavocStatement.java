package util.statement;

import java.util.HashSet;
import java.util.Set;


public class HavocStatement extends Statement {
    public String variable;
    
    public HavocStatement(String variable) {
        this.variable = variable;
    }
    
    public StatementType getType() {
        return StatementType.HAVOC;
    }
    
    public Set<String> getModifiedSet() {
        Set<String> modSet = new HashSet();
        modSet.add(variable);
        return modSet;
    }
}
