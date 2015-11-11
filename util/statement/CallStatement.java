package util.statement;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import util.expressions.Expression;

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
    
    /** UNSUPPORTED - USE PROCEDURE getModifiedSet **/
    public Set<String> getModifiedSet() {
        throw new UnsupportedOperationException("Not supported yet.");
    }
}
