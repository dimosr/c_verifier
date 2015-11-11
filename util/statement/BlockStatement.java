package util.statement;

import java.util.HashSet;
import java.util.List;
import java.util.Set;


public class BlockStatement extends Statement {
    public List<Statement> statements;
    
    public BlockStatement(List<Statement> statements) {
        this.statements = statements;
    }
    
    public StatementType getType() {
        return StatementType.BLOCK;
    }
    
    public Set<String> getModifiedSet() {
        Set<String> modSet = new HashSet();
        for(Statement statement : statements) {
            Set<String> stmtModSet = statement.getModifiedSet();;
            for(String variable : stmtModSet)
                modSet.add(variable);
        }
        return modSet;
    }
}
