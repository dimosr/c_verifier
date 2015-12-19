/**
 *  Copyright 2016 by Dimos Raptis <raptis.dimos@yahoo.gr>
 *  Licensed under GNU General Public License 2.0 or later. 
 *  Some rights reserved. See LICENSE.
 *
 *  @license GPL-2.0 <http://spdx.org/licenses/GPL-2.0.html>
 */

package util.expressions;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import tool.verif.structs.VariablesMapping;
import util.operators.UnaryOperator;

public class UnaryExpression extends Expression {
    
    public List<UnaryOperator> operators;
    public Expression expr;
    
    public UnaryExpression(Expression expr) {
        this.operators = new ArrayList<UnaryOperator>();
        this.expr = expr;
    }
    
    public UnaryExpression(UnaryOperator op, Expression expr) {
        this(expr);
        operators.add(op);
    }
    
    public void addOperator(UnaryOperator op) {
        operators.add(op);
    }
    
    public ExpressionType getType() {
        return ExpressionType.UNARY;
    }
    
    public Expression applyMappings(VariablesMapping mapping, Expression result) {
        Expression exprEval = expr.applyMappings(mapping, result);
        UnaryExpression unaryEval = new UnaryExpression(exprEval);
        for(UnaryOperator op : operators)
            unaryEval.addOperator(op);
        return unaryEval;
    }
    
    public Expression applySummarisationMappings(VariablesMapping mapping, Map<String, Expression> parametersMapping, Expression resultExpr) {
        Expression exprEval = expr.applySummarisationMappings(mapping, parametersMapping, resultExpr);
        UnaryExpression unaryEval = new UnaryExpression(exprEval);
        for(UnaryOperator op : operators)
            unaryEval.addOperator(op);
        return unaryEval;
    };
}
