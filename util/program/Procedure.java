package util.program;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import util.expressions.Expression;
import util.statement.Statement;

public class Procedure {
    public List<String> parameters;
    
    public List<RequireCondition> preConditions;
    public List<EnsureCondition> postConditions;
    
    public List<Statement> statements;
    public Expression returnExpression;
    
    public Procedure(List<String> parameters, List<RequireCondition> preConditions, List<EnsureCondition> postConditions, List<Statement> statements, Expression returnExpression) {
        this.preConditions = preConditions;
        this.postConditions = postConditions;
        this.parameters = parameters;
        this.statements = statements;
        this.returnExpression = returnExpression;
    }
    
    public Set<String> getModifiedSet() {
        Set<String> procedureModSet = new HashSet();
        for(Statement statement : statements) {
            Set<String> stmtModSet = statement.getModifiedSet();;
            for(String variable : stmtModSet)
                procedureModSet.add(variable);
        }
        return procedureModSet;
    }
}
