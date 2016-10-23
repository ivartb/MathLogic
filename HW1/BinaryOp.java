/**
 * Created by -- on 23.10.2016.
 */

import java.util.HashMap;

public class BinaryOp extends Expression {
    static final int BINOP = 0;
    Expression left, right;
    Operation op;

    BinaryOp(Expression l, Expression r, Operation o) {
        left = l;
        right = r;
        op = o;
        type = BINOP;

        cached = left.cached + op + "(" + right.cached + ")";
    }

    public boolean equivalent(Expression e, HashMap<String, String> d) {
        if (e == null || e.type != type) {
            return false;
        }
        BinaryOp bo = (BinaryOp) e;
        return op == bo.op && left.equivalent(bo.left, d) && right.equivalent(bo.right, d);
    }


    enum Operation {
        AND, OR, IMPL;

        char toChar() {
            switch (this) {
                case AND:
                    return '&';
                case OR:
                    return '|';
                default:
                    return '>';
            }
        }
    }
}
