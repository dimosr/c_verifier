package util.statement;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import util.expressions.Expression;
import util.program.Program;

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
    
    public Set<String> getModifiedSet(Program program, List<String> localVariables) {
        Set<String> modSet = new HashSet();
        Set<String> ifModSet = ifStatement.getModifiedSet(program, localVariables);
        for(String variable : ifModSet)
                modSet.add(variable); 
        if(elseStatement != null) {
            Set<String> elseModSet = elseStatement.getModifiedSet(program, localVariables);
            for(String variable : elseModSet)
                modSet.add(variable);
        }
        
        return modSet;
    }
}
