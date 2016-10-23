/**
 * Created by -- on 23.10.2016.
 */

import java.util.ArrayList;
import java.util.Collections;


public class Parser {
    String expression;
    int pointer;
    BinaryOp.Operation OPERATIONS[] = new BinaryOp.Operation[]
            {BinaryOp.Operation.IMPL, BinaryOp.Operation.OR, BinaryOp.Operation.AND};

    Expression parse(String exp) {
        this.expression = exp;
        pointer = 0;
        return parseBinary(0);
    }

    void skipBlank() {
        while (pointer < expression.length() && Character.isWhitespace(expression.charAt(pointer))) {
            pointer++;
        }
    }

    boolean currentOperationIs(char c) {
        if (expression.charAt(pointer) == '-')
            pointer++;
        return expression.charAt(pointer) == c;
    }

    Expression parseBinary(int pos) {
        if (pos == OPERATIONS.length) {
            return parseUnary();
        }
        ArrayList<Expression> list = new ArrayList<Expression>() {{
            add(parseBinary(pos + 1));
        }};
        while (pointer < expression.length()) {
            skipBlank();
            if (pointer == expression.length() || !currentOperationIs(OPERATIONS[pos].toChar())) {
                break;
            }
            pointer++;
            list.add(parseBinary(pos + 1));
        }

        if (OPERATIONS[pos] == BinaryOp.Operation.IMPL) {
            Collections.reverse(list);
            return list.stream().skip(1).reduce(list.get(0), (a, b) -> new BinaryOp(b, a, OPERATIONS[pos]));
        } else {
            return list.stream().skip(1).reduce(list.get(0), (a, b) -> new BinaryOp(a, b, OPERATIONS[pos]));
        }
    }

    Expression parseUnary() {
        skipBlank();
        switch (expression.charAt(pointer)) {
            case '(':
                pointer++;
                Expression result = parseBinary(0);
                skipBlank();
                pointer++;
                return result;
            case '!':
                pointer++;
                return new Negation(parseUnary());
            default:
                int start = pointer;
                while (pointer < expression.length() && Character.isLetterOrDigit(expression.charAt(pointer))) {
                    pointer++;
                }
                return new Variable(expression.substring(start, pointer));
        }
    }

}
