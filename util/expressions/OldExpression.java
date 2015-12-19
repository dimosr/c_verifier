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


public class OldExpression extends Expression {
    public String variableName;
    
    public OldExpression(String variableName) {
        this.variableName = variableName;
    }

    public ExpressionType getType() {
        return ExpressionType.OLD;
    }
    
    public Expression applyMappings(VariablesMapping mapping, Expression result) {
        VarRefExpression oldExpr = null;
        String ssaVariableName = "G__" + variableName + "0";
        oldExpr = new VarRefExpression(ssaVariableName);
        return oldExpr;
    }
    
    public Expression applySummarisationMappings(VariablesMapping mapping, Map<String, Expression> parametersMapping, Expression resultExpr) {
        VarRefExpression oldExpr = new VarRefExpression(variableName);
        return oldExpr;
    }
}
