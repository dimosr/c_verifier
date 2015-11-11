package util.statement;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import util.expressions.Expression;
import util.program.Procedure;
import util.program.Program;

public class CallStatement extends Statement {
    public String variableName;
    public String procedureName;
    public List<Expression> parameters;
    
    public CallStatement(String variableName, String procedureName, List<Expression> parameters) {
        this.variableName = variableName;
        this.procedureName = procedureName;
        this.parameters = parameters;
    }
    
    public StatementType getType() {
        return StatementType.CALL;
    }
    
    public Set<String> getModifiedSet(Program program, List<String> localVariables) {
        Set<String> modSet = new HashSet();
        Set<String> calledProcModSet = program.procedures.get(procedureName).modifiedSet;
        for(String variable : calledProcModSet) {
            if(program.globalVariables.contains(variable) || localVariables.contains(variable))
                modSet.add(variable);
        }
        modSet.add(variableName);
        return modSet;
    }
}
