package util.program;

import util.expressions.Expression;

public class EnsureCondition {
    public Expression expression;
    public boolean isCandidate;
    
    public EnsureCondition(Expression expression) {
        this.expression = expression;
        this.isCandidate = false;
    }
    
    public void setAsCandidate() {
        this.isCandidate = true;
    }
    
    public boolean isCandidate() {
        return isCandidate;
    }
}
