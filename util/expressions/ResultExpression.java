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

public class ResultExpression extends Expression {

    public ExpressionType getType() {
        return ExpressionType.RESULT;
    }
    
    public Expression applyMappings(VariablesMapping mapping, Expression result) {
        return result.applyMappings(mapping, result);
    }
    
    public Expression applySummarisationMappings(VariablesMapping mapping, Map<String, Expression> parametersMapping, Expression resultExpr) {
        return resultExpr;
    }
}
