package expression;

public class Num extends Expression {
    public final int k;
    final Expression d;

    public Num(int k, Expression d) {
        this.k = k;
        this.d = d;
    }

    @Override
    public String toString() {
        StringBuilder t = new StringBuilder();
        for (int i = 0; i < k; i++) {
            t.append("'");
        }
        return d.toString() + t.toString();
    }

    @Override
    public Expression changeVarToExpr(String var, Expression other) {
        return new Num(k, d.changeVarToExpr(var, other));
    }
}
