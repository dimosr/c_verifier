package util.operators;

public class UnaryOperator extends Operator {
    
   public UnaryOperatorType operator; 
   
   public UnaryOperator(UnaryOperatorType operator) {
       this.operator = operator;
   }
   
   public OperatorType getType() {
       return OperatorType.UNARY;
   }
}
