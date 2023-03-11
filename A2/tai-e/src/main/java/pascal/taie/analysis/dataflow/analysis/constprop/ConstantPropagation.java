/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.BinaryExp;
import pascal.taie.ir.exp.BitwiseExp;
import pascal.taie.ir.exp.ConditionExp;
import pascal.taie.ir.exp.Exp;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.ShiftExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.List;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        CPFact fact = new CPFact();
        List<Var> params = cfg.getIR().getParams();
        for (Var param : params) {
            if (canHoldInt(param)) {
                fact.update(param, Value.getNAC());
            }
        }
        // TODO - finish me
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        for (Var key : fact.keySet()) {
            target.update(key, meetValue(fact.get(key), target.get(key)));
        }
        // TODO - finish me
    }

    /**
     * Meets two Values.
     */

    public Value meetValue(Value v1, Value v2) throws NullPointerException{
        // NAC ⊓ v = NAC
        // UNDEF ⊓ v = v
        if (v1.isConstant() && v2.isConstant()) {
            if (v1.equals(v2)) {
                return Value.makeConstant(v1.getConstant());
            } else {
                return Value.getNAC();
            }
        } else if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        } else if (v1.isConstant() && v2.isUndef()) {
            return Value.makeConstant(v1.getConstant());
        } else if (v2.isConstant() && v1.isUndef()) {
            return Value.makeConstant(v2.getConstant());
        }
        return Value.getUndef();
        // TODO - finish me
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        boolean isChanged = false;
       // out.copyFrom(in);
        for (Var key : in.keySet()) {
            if(out.update(key, in.get(key))){
                isChanged = true;
            };

        }
        if (stmt instanceof DefinitionStmt<?, ?> s) {
            if (s.getLValue() instanceof Var value && canHoldInt((Var) s.getLValue())) {
                Value removedVal = in.get(value);
                out.remove(value);
                Value updatedVal = evaluate(s.getRValue(), in);
                out.update(value, updatedVal);
                return !removedVal.equals(updatedVal) || isChanged;
            }
        }
        return isChanged;
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE, SHORT, INT, CHAR, BOOLEAN -> {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        if (exp instanceof Var var) {
            if(in.get(var).isConstant()){
                return Value.makeConstant(in.get(var).getConstant());
            }
            return in.get(var);
        }

        if (exp instanceof IntLiteral intLiteral) {
            return Value.makeConstant(intLiteral.getValue());
        }

        if (exp instanceof BinaryExp binaryExp) {
            Value value1 = evaluate(binaryExp.getOperand1(), in);
            Value value2 = evaluate(binaryExp.getOperand2(), in);
            BinaryExp.Op operator = binaryExp.getOperator();

            // 被除数为0
            if (value2.isConstant() && value2.getConstant()==0) {
                if (operator instanceof ArithmeticExp.Op arithmeticOp) {
                    if (arithmeticOp == ArithmeticExp.Op.DIV || arithmeticOp == ArithmeticExp.Op.REM) {
                        return Value.getUndef();
                    }
                }
            }

            if (value1.isNAC() || value2.isNAC()) {
                return Value.getNAC();
            }

            if (value1.isUndef() || value2.isUndef()) {
                return Value.getUndef();
            }

            if (value1.isConstant() && value2.isConstant()) {
                int int1 = value1.getConstant();
                int int2 = value2.getConstant();
                if (operator instanceof ArithmeticExp.Op arithmeticOp) {
                    return switch (arithmeticOp) {
                        case ADD -> Value.makeConstant(int1 + int2);
                        case SUB -> Value.makeConstant(int1 - int2);
                        case MUL -> Value.makeConstant(int1 * int2);
                        case DIV -> Value.makeConstant(int1 / int2);
                        case REM -> Value.makeConstant(int1 % int2);
                    };
                }
                if (operator instanceof ShiftExp.Op shiftOp) {
                    return switch (shiftOp) {
                        case SHL -> Value.makeConstant(int1 << int2);
                        case SHR -> Value.makeConstant(int1 >> int2);
                        case USHR -> Value.makeConstant(int1 >>> int2);
                    };
                }
                if (operator instanceof BitwiseExp.Op bitwiseOp) {
                    return switch (bitwiseOp) {
                        case OR -> Value.makeConstant(int1 | int2);
                        case AND -> Value.makeConstant(int1 & int2);
                        case XOR -> Value.makeConstant(int1 ^ int2);
                    };
                }
                if (operator instanceof ConditionExp.Op conditionOp) {
                    return switch (conditionOp) {
                        case EQ -> Value.makeConstant(int1 == int2 ? 1 : 0);
                        case NE -> Value.makeConstant(int1 != int2 ? 1 : 0);
                        case GE -> Value.makeConstant(int1 >= int2 ? 1 : 0);
                        case GT -> Value.makeConstant(int1 > int2 ? 1 : 0);
                        case LE -> Value.makeConstant(int1 <= int2 ? 1 : 0);
                        case LT -> Value.makeConstant(int1 < int2 ? 1 : 0);
                    };
                }
            }
        }

        return Value.getNAC();
    }
}
