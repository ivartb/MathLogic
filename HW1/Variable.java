/**
 * Created by -- on 23.10.2016.
 */

import java.util.HashMap;

public class Variable extends Expression {
    final int VAR = 2;

    Variable(String cachedToString) {
        this.cached = cachedToString;
        type = VAR;
    }

    public boolean equivalent(Expression e, HashMap<String, String> d) {
        if (e == null) {
            return false;
        }
        if (d.containsKey(cached)) {
            return d.get(cached).equals(e.toString());
        } else {
            d.put(cached, e.toString());
            return true;
        }
    }
}

