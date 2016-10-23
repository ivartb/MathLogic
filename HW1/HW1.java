/**
 * Created by -- on 23.10.2016.
 */

import java.io.*;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.StringTokenizer;

public class HW1 {
    static Parser p = new Parser();
    static Map<String, Integer> data;
    static Map<String, ArrayList<Pair>> rightImpl;
    static Map<String, Integer> assumptions;

    static PrintWriter out;
    static BufferedReader in;

    private static ArrayList<Expression> axioms = new ArrayList<Expression>() {{
        add(p.parse("A->B->A"));
        add(p.parse("(A->B)->(A->B->C)->(A->C)"));
        add(p.parse("A->B->A&B)"));
        add(p.parse("A&B->A"));
        add(p.parse("A&B->B"));
        add(p.parse("A->A|B"));
        add(p.parse("B->A|B"));
        add(p.parse("(A->C)->(B->C)->(A|B->C)"));
        add(p.parse("(A->B)->(A->!B)->!A"));
        add(p.parse("!!A->A"));
    }};

    static boolean isAxiom(Expression d) {
        for (int i = 0; i < axioms.size(); i++) {
            if (axioms.get(i).equivalent(d, new HashMap<>())) {
                out.println("Сх. акс. " + (i + 1) + ")");
                return true;
            }
        }
        return false;
    }

    public static boolean isAssumption(String d) {
        if (assumptions.containsKey(d)) {
            out.println("Предп. " + assumptions.get(d) + ")");
            return true;
        }
        return false;
    }

    static private boolean isModusPonens(String b) {
        if (rightImpl.containsKey(b)) {
            ArrayList<Pair> arr = rightImpl.get(b);
            for (int i = 0; i < arr.size(); i++) {
                Pair pair = arr.get(i);
                if (data.containsKey(pair.d)) {
                    if (i != 0) {
                        arr.set(0, pair);
                        arr.ensureCapacity(1);
                    }
                    out.println("M.P. " + data.get(pair.d) + ", " + pair.id + ")");
                    return true;
                }
            }
        }
        return false;
    }

    public static void main(String[] args) throws IOException {
        //long time = System.currentTimeMillis();

        in = new BufferedReader(new FileReader("input.txt"));
        out = new PrintWriter(new File("output.txt"));
        data = new HashMap<>();
        assumptions = new HashMap<>();
        rightImpl = new HashMap<>();

        int ind = 0;
        String header = in.readLine();
        StringTokenizer t = new StringTokenizer(header, ",| ");
        while (t.hasMoreTokens()) {
            header = t.nextToken();
            if (header.startsWith("-")) {
                break;
            }
            ind++;
            Expression d = p.parse(header);
            assumptions.put(d.toString(), ind);
        }

        ind = 0;
        for (String cur = in.readLine(); cur != null; cur = in.readLine()) {
            out.print("(" + (ind + 1) + ") " + cur + " (");
            Expression d = p.parse(cur);
            if (!(isAxiom(d) || isAssumption(d.toString()) || isModusPonens(d.toString()))) {
                out.println("Не доказано)");
            } else {
                ind++;
                data.put(d.toString(), ind);
                if (d.type == BinaryOp.BINOP) {
                    BinaryOp bo = (BinaryOp) d;
                    if (bo.op == BinaryOp.Operation.IMPL) {
                        if (!rightImpl.containsKey(bo.right.toString())) {
                            rightImpl.put(bo.right.toString(), new ArrayList<>());
                        }
                        rightImpl.get(bo.right.toString()).add(new Pair(bo.left.toString(), ind));
                    }
                }
            }
        }

        in.close();
        out.close();
        //System.out.println(System.currentTimeMillis() - time + " ms");
    }


    static class Pair {
        String d;
        int id;

        Pair(String d, int id) {
            this.d = d;
            this.id = id;
        }
    }
}
