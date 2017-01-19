package expression;

public class Negation extends Expression {
    final Expression d;

    public Negation(Expression d) {
        this.d = d;
    }

    @Override
    public Expression changeVarToExpr(String var, Expression other) {
        return new Negation(d.changeVarToExpr(var, other));
    }

    @Override
    public String toString() {
        return "!" + d.toString();
    }
}
