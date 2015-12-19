/**
 *  Copyright 2016 by Dimos Raptis <raptis.dimos@yahoo.gr>
 *  Licensed under GNU General Public License 2.0 or later. 
 *  Some rights reserved. See LICENSE.
 *
 *  @license GPL-2.0 <http://spdx.org/licenses/GPL-2.0.html>
 */

package util.statement;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import util.expressions.Expression;
import util.program.Program;

public class AssignStatement extends Statement {
    public String variable;
    public Expression rightHandSideExpr;
    
    public AssignStatement(String variable, Expression expression) {
        this.variable = variable;
        this.rightHandSideExpr = expression;
    }
    
    public StatementType getType() {
        return StatementType.ASSIGN;
    }
    
    public Set<String> getModifiedSet(Program program, List<String> localVariables) {
        Set<String> modSet = new HashSet();
        modSet.add(variable);
        return modSet;
    }
}
