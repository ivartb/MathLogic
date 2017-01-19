package expression;

public abstract class Expression {
    public Expression freeQuantifier(Expression other) {
        return this;
    }
    public abstract Expression changeVarToExpr(String var, Expression other);
}
