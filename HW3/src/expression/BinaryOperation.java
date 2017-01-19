package expression;

public class BinaryOperation extends Expression {
    public final Expression a, b;
    final String op;

    public BinaryOperation(Expression a, Expression b, String op) {
        this.a = a;
        this.b = b;
        this.op = op;
    }

    @Override
    public String toString() {
        return "(" + a.toString() + op + b.toString() + ")";
    }

    @Override
    public Expression changeVarToExpr(String var, Expression other) {
        return new BinaryOperation(a.changeVarToExpr(var, other),
                b.changeVarToExpr(var, other), op);
    }
}
