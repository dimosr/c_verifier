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
    
    public void setAsRegular() {
        this.isCandidate = false;
    }
    
    public boolean isCandidate() {
        return isCandidate;
    }
}
