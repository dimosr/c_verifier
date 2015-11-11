package util.program;

import util.expressions.Expression;

public class RequireCondition {
    public Expression expression;
    public boolean isCandidate;
    
    public RequireCondition(Expression expression) {
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
