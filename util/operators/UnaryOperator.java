/**
 *  Copyright 2016 by Dimos Raptis <raptis.dimos@yahoo.gr>
 *  Licensed under GNU General Public License 2.0 or later. 
 *  Some rights reserved. See LICENSE.
 *
 *  @license GPL-2.0 <http://spdx.org/licenses/GPL-2.0.html>
 */

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
