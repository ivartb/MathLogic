package expression;

import expression.*;

public class Operations {
    public static final Variable varA = new Variable("a");
    public static final Variable varB = new Variable("b");
    public static final Variable varC = new Variable("c");
    public static final Variable zero = new Variable("0");

    public static Expression helper = con(eqv(zero, zero), con(eqv(zero, zero), eqv(zero, zero)));

    static public Expression formalAxiom1 = con(eqv(varA, varB), eqv(plusNum(varA, 1), plusNum(varB, 1)));
    static public Expression formalAxiom2 = con(eqv(varA, varB), con(eqv(varA, varC), eqv(varB, varC)));
    static public Expression formalAxiom4 = negation(eqv(plusNum(varA, 1), zero));
    static public Expression formalAxiom5 = eqv(plus(varA, plusNum(varB, 1)), plusNum(plus(varA, varB), 1));
    static public Expression formalAxiom6 = eqv(plus(varA, zero), varA);

    public static Expression negation(Expression a) {
        return new Negation(a);
    }
    public static Expression and(Expression a, Expression b) {
        return new BinaryOperation(a, b, "&");
    }
    public static Expression con(Expression a, Expression b) {
        return new BinaryOperation(a, b, "->");
    }
    public static Expression eqv(Expression a, Expression b) {
        return new BinaryOperation(a, b, "=");
    }
    public static Expression plus(Expression a, Expression b) {
        return new BinaryOperation(a, b, "+");
    }
    public static Expression plusNum(Expression a, int k) {
        return new Num(k, a);
    }
    public static Expression num(int n) {
        return new Num(n, zero);
    }
    public static Expression quantifier(String q, Expression a, Variable var) {
        return new Quantifier(q, var, a);
    }
}
