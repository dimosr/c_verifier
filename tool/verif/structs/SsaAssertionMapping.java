/**
 *  Copyright 2016 by Dimos Raptis <raptis.dimos@yahoo.gr>
 *  Licensed under GNU General Public License 2.0 or later. 
 *  Some rights reserved. See LICENSE.
 *
 *  @license GPL-2.0 <http://spdx.org/licenses/GPL-2.0.html>
 */

package tool.verif.structs;

import java.util.List;


public class SsaAssertionMapping {
    public Object source;
    public List holder;
    public SourceType sourceType;
    
    public enum SourceType {
        ASSERT, INVARIANT, ENSURES, REQUIRES
    }
    
    public SsaAssertionMapping(Object source, List holder, SourceType sourceType) {
        this.source = source;
        this.holder = holder;
        this.sourceType = sourceType;
    }
}
