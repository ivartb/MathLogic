/**
 * Created by -- on 23.10.2016.
 */

import java.util.HashMap;

public abstract class Expression {
    int type;
    String cached;

    abstract public boolean equivalent(Expression e, HashMap<String, String> d);

    public String toString() {
        return cached;
    }

    public int hashCode() {
        return cached.hashCode();
    }

    public boolean equals(Object o) {
        return !(o == null || !(o instanceof Expression)) && cached.equals(((Expression) o).cached);
    }

}

