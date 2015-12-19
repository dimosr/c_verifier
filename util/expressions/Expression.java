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

public abstract class Expression {
    public abstract ExpressionType getType();
    public abstract Expression applyMappings(VariablesMapping mapping, Expression result);
    public abstract Expression applySummarisationMappings(VariablesMapping mapping, Map<String, Expression> parametersMapping, Expression resultExpr);
}
