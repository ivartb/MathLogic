/**
 * Created by -- on 23.10.2016.
 */

import java.util.HashMap;

public class Negation extends Expression {
    final int NEG = 1;
    Expression neg;

    Negation(Expression neg) {
        this.neg = neg;
        type = NEG;
        cached = "!" + neg.cached;
    }

    public boolean equivalent(Expression e, HashMap<String, String> d) {
        return !(e == null || e.type != type) && neg.equivalent(((Negation) e).neg, d);
    }
}
