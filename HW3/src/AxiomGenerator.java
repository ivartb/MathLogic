import expression.Expression;
import expression.Variable;
import static expression.Operations.*;

import java.io.PrintWriter;
import java.util.Arrays;
import java.util.HashMap;

public class AxiomGenerator {
    final PrintWriter out;
    Expression[] generatedAxioms = new Expression[10];
    HashMap<String, Expression> s;
    
    AxiomGenerator(PrintWriter out) {
        this.out = out;
        Arrays.fill(generatedAxioms, null);
        s = new HashMap<>();
    }

    Expression addQuantifiers(Expression d, Variable[] vars) {
        for (Variable var : vars) {
            d = quantifier("@", d, var);
            out.println(con(helper, d));
        }
        out.println(d);
        return d;
    }

    void prepareForQuantifiers(Expression canAxiom) {
        out.println(canAxiom);
        out.println(con(canAxiom, con(helper, canAxiom)));
        out.println(con(helper, canAxiom));
    }

    Expression generate(Expression canAxiom, Expression[] args, Variable quant[]) {
        assert args.length == quant.length;
        prepareForQuantifiers(canAxiom);
        Expression cur = addQuantifiers(canAxiom, quant);
        for (int i = args.length - 1; i >= 0; i--) {
            Expression nx = cur.freeQuantifier(args[i]);
            out.println(con(cur, nx));
            out.println(nx);
            cur = nx;
        }
        return cur;

    }
    Expression genAxiom1(Expression a, Expression b) {
        return generate(formalAxiom1, new Expression[]{a, b}, new Variable[]{varA, varB});
    }
    Expression genAxiom2(Expression a, Expression b, Expression c) {
        return generate(formalAxiom2, new Expression[]{a, b, c}, new Variable[]{varA, varB, varC});
    }
    Expression genAxiom4(Expression a) {
        return generate(formalAxiom4, new Expression[]{a}, new Variable[]{varA});
    }
    Expression genAxiom5(Expression a, Expression b) {
        return generate(formalAxiom5, new Expression[]{a, b}, new Variable[]{varA, varB});
    }
    Expression genAxiom6(Expression a) {
        return generate(formalAxiom6, new Expression[]{a}, new Variable[]{varA});
    }
}
