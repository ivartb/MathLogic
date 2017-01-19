package expression;

public class Variable extends Expression {
    final String var;

    public Variable(String s) {
        this.var = s;
    }

    @Override
    public String toString() {
        return var;
    }

    @Override
    public Expression changeVarToExpr(String var, Expression other) {
        if (this.var.equals(var))
            return other;
        return this;
    }
}
