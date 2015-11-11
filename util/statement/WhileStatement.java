package util.statement;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import util.expressions.Expression;
import util.program.Invariant;


public class WhileStatement extends Statement {
    public Expression loopCondition;
    public List<Invariant> invariants;
    public BlockStatement blockStatement;
    
    public WhileStatement(Expression loopCondition, List<Invariant> invariants, BlockStatement blockStatement) {
        this.loopCondition = loopCondition;
        this.invariants = invariants;
        this.blockStatement = blockStatement;
    }
    
    public StatementType getType() {
        return StatementType.WHILE;
    }
    
    public Set<String> getModifiedSet() {
        Set<String> modSet = new HashSet();
        Set<String> blockModSet = blockStatement.getModifiedSet();
        for(String variable : blockModSet)
                modSet.add(variable); 
        return modSet;
    }
}
