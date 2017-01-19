import expression.BinaryOperation;
import expression.Expression;
import expression.Num;
import expression.Variable;

import java.io.*;

import static expression.Operations.*;

public class ProofGenerator {
    final static boolean LESS = false;
    final AxiomGenerator gen;
    final PrintWriter out;

    ProofGenerator(PrintWriter out) {
        this.out = out;
        gen = new AxiomGenerator(out);
    }


    void proveHelper(char[] c, Expression[] a, String filename) throws IOException {
        BufferedReader in = new BufferedReader(new FileReader(filename));
        String s = in.readLine();
        while (s != null) {
            for (int i = 0; i < s.length(); i++) {
                boolean flag = true;
                for (int j = 0; j < c.length; j++) {
                    if (s.charAt(i) == c[j]) {
                        out.print(a[j]);
                        flag = false;
                    }
                }
                if (flag) {
                    out.print(s.charAt(i));
                }
            }
            out.println();
            s = in.readLine();
        }

    }

    Expression genABBA(Expression a, Expression b) throws IOException {
        proveHelper(new char[]{'a', 'b'}, new Expression[]{a, b}, "abba.txt");
        return eqv(b, a);
    }

    private void induction(Expression phi, Expression a0, Expression ax, Variable var) {
        out.println(a0);
        ax = con(phi, ax);
        gen.prepareForQuantifiers(ax);
        Expression qax = gen.addQuantifiers(ax, new Variable[]{var});
        out.println(con(a0, con(qax, and(a0, qax))));
        out.println(con(qax, and(a0, qax)));
        out.println(and(a0, qax));
        out.println(con(and(a0, qax), phi));
    }

    // t = 0 + t
    static private Variable f1 = new Variable("f1");
    boolean isLemmaFProved= false;
    void lemmaF(Expression t) throws IOException {
        out.println(helper);
        Expression phi = eqv(f1, plus(zero, f1));
        if (!isLemmaFProved) {
            gen.genAxiom6(zero);
            Expression a0 = abba2(plus(zero, zero), zero);
            a0 = ((BinaryOperation) a0).b;
            out.println(phi + "|-(f1'=(0+f1'))");
            out.println(phi);
            gen.genAxiom5(zero, f1);
            gen.genAxiom1(f1, plus(zero, f1));
            out.println(eqv(plusNum(f1, 1), plusNum(plus(zero, f1), 1)));
            Expression ax = abcbac(plusNum(f1, 1), plusNum(plus(zero, f1), 1), plus(zero, plusNum(f1, 1)));
            out.println("deduction");
//
            out.println(a0);
            out.println(ax);
            induction(phi, a0, ax, f1);
            isLemmaFProved = true;
        }
        gen.generate(phi, new Expression[]{t}, new Variable[]{f1});
    }

    // x'+y=(x+y)'
    static private Variable g1 = new Variable("g1");
    static private Variable g2 = new Variable("g2");
    boolean lemmaGProved = false;
    void lemmaG(Expression t, Expression r) throws IOException {
        Expression hyp = eqv(plus(plusNum(g1, 1), g2), plusNum(plus(g1, g2), 1));
        if (!lemmaGProved) {
            gen.genAxiom6(plusNum(g1, 1));
            gen.genAxiom6(g1);
            gen.genAxiom1(plus(g1, zero), g1);
            out.println(eqv(plusNum(plus(g1, zero), 1), plusNum(g1, 1)));
            Expression a0 = abcbac(plus(plusNum(g1, 1), zero), plusNum(g1, 1), plusNum(plus(g1, zero), 1));

            Expression pro = eqv(plus(plusNum(g1, 1), plusNum(g2, 1)), plusNum(plus(g1, plusNum(g2, 1)), 1));
            out.println(hyp + "|-" + pro);
            out.println(eqv(plus(plusNum(g1, 1), g2), plusNum(plus(g1, g2), 1)));
            gen.genAxiom5(plusNum(g1, 1), g2);
            gen.genAxiom1(plus(plusNum(g1, 1), (g2)), plusNum(plus(g1, g2), 1));
            out.println(eqv(plusNum(plus(plusNum(g1, 1), (g2)), 1), plusNum(plus(g1, g2), 2)));
            abbcac(plus(plusNum(g1, 1), plusNum(g2, 1)), plusNum(plus(plusNum(g1, 1), (g2)), 1), plusNum(plus(g1, g2), 2));
            BinaryOperation res = (BinaryOperation) gen.genAxiom5(g1, g2);
            res = (BinaryOperation) gen.genAxiom1(res.a, res.b);
            out.println(res.b);
            Expression d = abcbac(plus(plusNum(g1, 1), plusNum(g2, 1)), plusNum(plus(g1, g2), 2), plusNum(plus(g1, plusNum(g2, 1)), 1));
            out.println("deduction");
            induction(hyp, a0, pro, g2);
            lemmaGProved = true;
        }
        gen.generate(hyp, new Expression[]{t, r}, new Variable[]{g1, g2});
    }

    void aLessOrEqualsB(int ka, int kb, boolean flag) throws IOException {
        Num a = new Num(ka, zero);
        Num b = new Num(kb, zero);

        gen.genAxiom6(a);
        for (int tt = 0; tt < b.k - a.k; ++tt) {
            Expression t = num(tt);
            gen.genAxiom1(plus(a, t), num(a.k + tt));

            Expression d2 = eqv(plusNum(plus(a, t), 1), plusNum(num(a.k + tt), 1));
            out.println(d2);
//
            axiom5(a, t);

            Expression d3 = eqv(plus(a, plusNum(t, 1)), plusNum(num(a.k + tt), 1));

            gen.genAxiom2(plusNum(plus(a, t), 1), plus(a, plusNum(t, 1)), plusNum(num(a.k + tt), 1));

            out.println(con(d2, d3));
            out.println(d3);
        }

        Expression s = eqv(plus(a, num(b.k - a.k)), b);
        Expression d;
        if (flag == LESS) {
            Expression ns = negation(eqv(num(b.k - a.k), zero));
            gen.genAxiom4(num(b.k - a.k - 1));
            out.println(con(ns, con(s, and(ns, s))));
            out.println(con(s, and(ns, s)));
            out.println(and(ns, s));
            s = and(ns, s);
            d = quantifier("?", and(negation(eqv(varA, zero)), eqv(plus(a, varA), b)), varA);
        } else {
            d = quantifier("?", eqv(plus(a, varA), b), varA);
        }
        out.println(con(s, d));
        out.println(d);
    }


    void axiom5(Expression a, Expression b) throws IOException {
        gen.genAxiom5(a, b);
        Expression aPlusBH = plus(a, plusNum(b, 1));
        Expression aPlusBPlusOne = plusNum(plus(a, b), 1);
        aa2(aPlusBH);
        gen.genAxiom2(aPlusBH, aPlusBPlusOne, aPlusBH);
        out.println(con(eqv(aPlusBH, aPlusBH), eqv(aPlusBPlusOne, aPlusBH)));
        out.println(eqv(aPlusBPlusOne, aPlusBH));
    }



    void greater(int aa, int bb) throws IOException {
        String b = num(bb).toString().substring(1);
        String c = num(aa - bb).toString().substring(2);

        BufferedReader in = new BufferedReader(
                new FileReader("src\\data\\a+0.in"));
        String s = in.readLine();
        while (s != null) {
            out.println(s);
            s = in.readLine();
        }
        in = new BufferedReader(
                new FileReader("src\\data\\a'+b.in"));
        s = in.readLine();
        while (s != null) {
            out.println(s);
            s = in.readLine();
        }

        in = new BufferedReader(
                new FileReader("src\\data\\proof.in"));
        printer(in, c, b);
        in = new BufferedReader(
                new FileReader("src\\data\\deMorgan.in"));
        printer(in, c, b);
    }

    void printer(BufferedReader in, String c, String b) throws IOException {
        String s = in.readLine();
        while (s != null) {
            for (int i = 0; i < s.length(); i++) {
                switch (s.charAt(i)) {
                    case 'C':
                        out.print(c);
                        break;
                    case 'B':
                        out.print(b);
                        break;
                    default:
                        out.print(s.charAt(i));
                }
            }
            out.println();
            s = in.readLine();
        }
    }

    void aa2(Expression a) {
        gen.generate(eqv(varA, varA), new Expression[]{a}, new Variable[]{varA});
    }
    Expression abba2(Expression a, Expression b) {
        return gen.generate(con(eqv(varA, varB), eqv(varB, varA)), new Expression[]{a, b}, new Variable[]{varA, varB});
    }

    Expression abbcac(Expression a, Expression b, Expression c) {
        abba2(a, b);
        out.println(eqv(b, a));
        BinaryOperation temp1 = (BinaryOperation) gen.genAxiom2(b, a, c);
        BinaryOperation temp2 = (BinaryOperation) temp1.b;
        out.println(temp1.b);
        out.println(temp2.b);
        return temp2.b;
    }
    Expression abcbac(Expression a, Expression b, Expression c) {

        abba2(c, b);
        out.println(eqv(b, c));
        return abbcac(a, b, c);
    }
}