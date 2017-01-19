import java.io.*;

import static expression.Operations.*;

public class HW3 {

    static PrintWriter out;
    static BufferedReader in;

    public static void main(String[] args) throws IOException {
        out = new PrintWriter(new File("output.txt"));
        ProofGenerator generator = new ProofGenerator(out);
        generator.genABBA(varA, varB);
        in = new BufferedReader(new FileReader("input.txt"));
        String[] s = in.readLine().split(" ");
        in.close();
        int a = Integer.parseInt(s[0]);
        int b = Integer.parseInt(s[1]);
        if (a <= b) {
            generator.aLessOrEqualsB(a, b, true);
        } else {
            generator.greater(a, b);
        }
        out.close();
    }

}
