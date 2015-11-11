package util.program;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import util.expressions.Expression;
import util.statement.Statement;

public class Procedure {
    public String procedureName;
    public List<String> parameters;
    
    public List<RequireCondition> preConditions;
    public List<EnsureCondition> postConditions;
    
    public List<String> localVariables;
    public List<Statement> statements;
    public Expression returnExpression;
    
    public Set<String> modifiedSet;
    
    public Procedure(String procedureName, List<String> parameters, List<RequireCondition> preConditions, List<EnsureCondition> postConditions, List<String> localVariables, List<Statement> statements, Expression returnExpression) {
        this.procedureName = procedureName;
        this.preConditions = preConditions;
        this.postConditions = postConditions;
        this.parameters = parameters;
        this.localVariables = localVariables;
        this.statements = statements;
        this.returnExpression = returnExpression;
        this.modifiedSet = new HashSet();       //populated by Program using fixed-point algorithm
    }
    
    public Set<String> getModifiedSet(Program program) {
        Set<String> procedureModSet = new HashSet();
        for(Statement statement : statements) {
            Set<String> stmtModSet = statement.getModifiedSet(program, this.localVariables);
            for(String variable : stmtModSet)
                procedureModSet.add(variable);
        }
        return procedureModSet;
    }
}
