package util.statement;

import java.util.HashSet;
import java.util.Set;
import util.expressions.Expression;

public class IfStatement extends Statement {
    public Expression ifCondition;
    public BlockStatement ifStatement;
    public BlockStatement elseStatement;
    
    public IfStatement(Expression ifCondition, BlockStatement ifStatement) {
        this.ifCondition = ifCondition;
        this.ifStatement = ifStatement;
    }
    
    public IfStatement(Expression ifCondition, BlockStatement ifStatement, BlockStatement elseStatement) {
        this.ifCondition = ifCondition;
        this.ifStatement = ifStatement;
        this.elseStatement = elseStatement;
    }
    
    public StatementType getType() {
        return StatementType.IF;
    }
    
    public Set<String> getModifiedSet() {
        Set<String> modSet = new HashSet();
        Set<String> ifModSet = ifStatement.getModifiedSet();
        for(String variable : ifModSet)
                modSet.add(variable); 
        if(elseStatement != null) {
            Set<String> elseModSet = null;
            for(String variable : elseModSet)
                modSet.add(variable);
        }
        
        return modSet;
    }
}
