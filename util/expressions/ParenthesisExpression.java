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

public class ParenthesisExpression extends Expression {
    
    public Expression expr;
    
    public ParenthesisExpression(Expression expr) {
        this.expr = expr;
    }
    
    public ExpressionType getType() {
        return ExpressionType.PARENTHESIS;
    }
    
    public Expression applyMappings(VariablesMapping mapping, Expression result) {
        return new ParenthesisExpression(expr.applyMappings(mapping, result));
    }
    
    public Expression applySummarisationMappings(VariablesMapping mapping, Map<String, Expression> parametersMapping, Expression resultExpr) {
        return new ParenthesisExpression(expr.applySummarisationMappings(mapping, parametersMapping, resultExpr));
    }
}
