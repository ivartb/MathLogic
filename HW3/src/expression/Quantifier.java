package expression;

public class Quantifier extends Expression {
    final String quantifier;
    final Variable v;
    final Expression d;

    public Quantifier(String quantifier, Variable v, Expression d) {
        this.quantifier = quantifier;
        this.v = v;
        this.d = d;
    }

    @Override
    public Expression freeQuantifier(Expression other) {
        return d.changeVarToExpr(v.toString(), other);
    }

    @Override
    public Expression changeVarToExpr(String var, Expression other) {
        if (var.equals(v.toString()))
            return this;
        return new Quantifier(quantifier, v, d.changeVarToExpr(var, other));
    }

    @Override
    public String toString() {
        return quantifier + v.toString() + "(" + d.toString() + ")";
    }
}
