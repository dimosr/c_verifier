/**
 *  Copyright 2016 by Dimos Raptis <raptis.dimos@yahoo.gr>
 *  Licensed under GNU General Public License 2.0 or later. 
 *  Some rights reserved. See LICENSE.
 *
 *  @license GPL-2.0 <http://spdx.org/licenses/GPL-2.0.html>
 */

package util.expressions;

import java.util.Map;
import tool.verif.structs.VariablesMapping;

public class ConstantExpression extends Expression {
    
    public String intValue;    //string representation used
    
    public ConstantExpression(String value) {
        intValue = value;
    }
    
    public ExpressionType getType() {
        return ExpressionType.CONSTANT;
    }
    
    public Expression applyMappings(VariablesMapping mapping, Expression result) {
        return new ConstantExpression(intValue);
    }
    
    public Expression applySummarisationMappings(VariablesMapping mapping, Map<String, Expression> parametersMapping, Expression resultExpr) {
        return new ConstantExpression(intValue);
    }
}
