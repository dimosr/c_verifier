package util.operators;

public class UnaryOperator extends Operator {
    
   public UnaryOperatorType opType; 
   
   public UnaryOperator(UnaryOperatorType operator) {
       this.opType = operator;
   }
   
   public OperatorType getType() {
       return OperatorType.UNARY;
   }
}
