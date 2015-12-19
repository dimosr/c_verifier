/**
 *  Copyright 2016 by Dimos Raptis <raptis.dimos@yahoo.gr>
 *  Licensed under GNU General Public License 2.0 or later. 
 *  Some rights reserved. See LICENSE.
 *
 *  @license GPL-2.0 <http://spdx.org/licenses/GPL-2.0.html>
 */

package util.program;

import util.expressions.Expression;

public class Assertion {
    public Expression expression;
    
    public Assertion(Expression expression) {
        this.expression = expression;
    }
}
