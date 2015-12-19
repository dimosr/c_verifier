/**
 *  Copyright 2016 by Dimos Raptis <raptis.dimos@yahoo.gr>
 *  Licensed under GNU General Public License 2.0 or later. 
 *  Some rights reserved. See LICENSE.
 *
 *  @license GPL-2.0 <http://spdx.org/licenses/GPL-2.0.html>
 */

package util.misc;

public class Tuple<X, Y> {
    
    public final X first; 
    public final Y second;
    
    public Tuple(X x, Y y) { 
        this.first = x; 
        this.second = y; 
    } 
} 