package util.conditions;

public class InvertCondition {
    public LogicalOp operator;
    public Condition invertedCondition;
    
    public InvertCondition(Condition condition){
        operator = LogicalOp.NOT;
        invertedCondition = condition;
    }
            
    public boolean isSimple(){
        return false;
    }
}
