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


public class AssertStatement extends Statement {
    public Expression expression;
    
    public AssertStatement(Expression expression) {
        this.expression = expression;
    }
    
    public StatementType getType() {
        return StatementType.ASSERT;
    }
    
    public Set<String> getModifiedSet(Program program, List<String> localVariables) {
        return new HashSet();
    }
}
