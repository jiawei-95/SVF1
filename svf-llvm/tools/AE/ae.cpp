//
// Created by Jiawei Ren on 11/28/23.
//
#include "AbstractExecution/IntervalExeState.h"
#include "AbstractExecution/RelExeState.h"
#include "AbstractExecution/RelationSolver.h"
#include "SVF-LLVM/LLVMUtil.h"
#include "Util/Options.h"
#include "Util/Z3Expr.h"
#include <chrono>
#include <cmath>
#include <string>

using namespace SVF;
using namespace SVFUtil;

static Option<bool> SYMABS(
    "symabs",
    "symbolic abstraction test",
    false
);

class SymblicAbstractionTest
{
public:
    SymblicAbstractionTest() = default;

    ~SymblicAbstractionTest() = default;

    static z3::context& getContext()
    {
        return Z3Expr::getContext();
    }

    void test_print()
    {
        SVFUtil::outs() << "hello print\n";
    }

    IntervalESBase RSY_time(IntervalESBase& inv, const Z3Expr& phi,
                            RelationSolver& rs)
    {
        auto start_time = std::chrono::high_resolution_clock::now();
        IntervalESBase resRSY = rs.RSY(inv, phi);
        auto end_time = std::chrono::high_resolution_clock::now();
        auto duration = std::chrono::duration_cast<std::chrono::microseconds>(
                            end_time - start_time);
        outs() << "running time of RSY      : " << duration.count()
               << " microseconds\n";
        return resRSY;
    }
    IntervalESBase Bilateral_time(IntervalESBase& inv, const Z3Expr& phi,
                                  RelationSolver& rs)
    {
        auto start_time = std::chrono::high_resolution_clock::now();
        IntervalESBase resBilateral = rs.bilateral(inv, phi);
        auto end_time = std::chrono::high_resolution_clock::now();
        auto duration = std::chrono::duration_cast<std::chrono::microseconds>(
                            end_time - start_time);
        outs() << "running time of Bilateral: " << duration.count()
               << " microseconds\n";
        return resBilateral;
    }
    IntervalESBase BS_time(IntervalESBase& inv, const Z3Expr& phi,
                           RelationSolver& rs)
    {
        auto start_time = std::chrono::high_resolution_clock::now();
        IntervalESBase resBS = rs.BS(inv, phi);
        auto end_time = std::chrono::high_resolution_clock::now();
        auto duration = std::chrono::duration_cast<std::chrono::microseconds>(
                            end_time - start_time);
        outs() << "running time of BS       : " << duration.count()
               << " microseconds\n";
        return resBS;
    }

    void testRelExeState1_1()
    {
        SVFUtil::outs() << sucMsg("\t SUCCESS :") << "test1_1 start\n";
        IntervalESBase itv;
        RelExeState relation;
        // var0 := [0, 1];
        itv[0] = IntervalValue(0, 1);
        relation[0] = getContext().int_const("0");
        // var1 := var0 + 1;
        relation[1] =
            getContext().int_const("1") == getContext().int_const("0") + 1;
        itv[1] = itv[0] + IntervalValue(1);
        // Test extract sub vars
        Set<u32_t> res;
        relation.extractSubVars(relation[1], res);
        assert(res == Set<u32_t>({0, 1}) && "inconsistency occurs");
        IntervalESBase inv = itv.sliceState(res);
        RelationSolver rs;
        const Z3Expr& relExpr = relation[1];
        const Z3Expr& initExpr = rs.gamma_hat(inv);
        const Z3Expr& phi = (relExpr && initExpr).simplify();
        IntervalESBase resRSY = rs.RSY(inv, phi);
        IntervalESBase resBilateral = rs.bilateral(inv, phi);
        IntervalESBase resBS = rs.BS(inv, phi);
        // 0:[0,1] 1:[1,2]
        assert(resRSY == resBS && resBS == resBilateral && "inconsistency occurs");
        for (auto r : resRSY.getVarToVal())
        {
            outs() << r.first << " " << r.second << "\n";
        }
        IntervalESBase::VarToValMap intendedRes = {{0, IntervalValue(0, 1)}, {1, IntervalValue(1, 2)}};
        assert(IntervalESBase::eqVarToValMap(resBS.getVarToVal(), intendedRes) && "inconsistency occurs");
    }

    void testRelExeState1_2()
    {
        SVFUtil::outs() << "test1_2 start\n";
        IntervalESBase itv;
        RelExeState relation;
        // var0 := [0, 1];
        relation[0] = getContext().int_const("0");
        itv[0] = IntervalValue(0, 1);
        // var1 := var0 + 1;
        relation[1] =
            getContext().int_const("1") == getContext().int_const("0") * 2;
        itv[1] = itv[0] * IntervalValue(2);

        // Test extract sub vars
        Set<u32_t> res;
        relation.extractSubVars(relation[1], res);
        assert(res == Set<u32_t>({0, 1}) && "inconsistency occurs");
        IntervalESBase inv = itv.sliceState(res);
        RelationSolver rs;
        const Z3Expr& relExpr = relation[1];
        const Z3Expr& initExpr = rs.gamma_hat(inv);
        const Z3Expr& phi = (relExpr && initExpr).simplify();
        IntervalESBase resRSY = rs.RSY(inv, phi);
        IntervalESBase resBilateral = rs.bilateral(inv, phi);
        IntervalESBase resBS = rs.BS(inv, phi);
        // 0:[0,1] 1:[0,2]
        assert(resRSY == resBS && resBS == resBilateral && "inconsistency occurs");
        for (auto r : resRSY.getVarToVal())
        {
            outs() << r.first << " " << r.second << "\n";
        }
        IntervalESBase::VarToValMap intendedRes = {{0, IntervalValue(0, 1)}, {1, IntervalValue(0, 2)}};
        assert(IntervalESBase::eqVarToValMap(resBS.getVarToVal(), intendedRes) && "inconsistency occurs");
    }

    void testRelExeState2_1()
    {
        SVFUtil::outs() << "test2_1 start\n";
        IntervalESBase itv;
        RelExeState relation;
        // var0 := [0, 10];
        relation[0] = getContext().int_const("0");
        itv[0] = IntervalValue(0, 10);
        // var1 := var0;
        relation[1] =
            getContext().int_const("1") == getContext().int_const("0");
        itv[1] = itv[0];
        // var2 := var1 - var0;
        relation[2] = getContext().int_const("2") ==
                      getContext().int_const("1") - getContext().int_const("0");
        itv[2] = itv[1] - itv[0];
        // Test extract sub vars
        Set<u32_t> res;
        relation.extractSubVars(relation[2], res);
        assert(res == Set<u32_t>({0, 1, 2}) && "inconsistency occurs");
        IntervalESBase inv = itv.sliceState(res);
        RelationSolver rs;
        const Z3Expr& relExpr = relation[2] && relation[1];
        const Z3Expr& initExpr = rs.gamma_hat(inv);
        const Z3Expr& phi = (relExpr && initExpr).simplify();
        IntervalESBase resRSY = rs.RSY(inv, phi);
        IntervalESBase resBilateral = rs.bilateral(inv, phi);
        IntervalESBase resBS = rs.BS(inv, phi);
        // 0:[0,10] 1:[0,10] 2:[0,0]
        assert(resRSY == resBS && resBS == resBilateral && "inconsistency occurs");
        for (auto r : resRSY.getVarToVal())
        {
            outs() << r.first << " " << r.second << "\n";
        }
        // ground truth
        IntervalESBase::VarToValMap intendedRes = {{0, IntervalValue(0, 10)},
            {1, IntervalValue(0, 10)},
            {2, IntervalValue(0, 0)}
        };
        assert(IntervalESBase::eqVarToValMap(resBS.getVarToVal(), intendedRes) && "inconsistency occurs");
    }

    void testRelExeState2_2()
    {
        SVFUtil::outs() << "test2_2 start\n";
        IntervalESBase itv;
        RelExeState relation;
        // var0 := [0, 100];
        relation[0] = getContext().int_const("0");
        itv[0] = IntervalValue(0, 100);
        // var1 := var0;
        relation[1] =
            getContext().int_const("1") == getContext().int_const("0");
        itv[1] = itv[0];
        // var2 := var1 - var0;
        relation[2] = getContext().int_const("2") ==
                      getContext().int_const("1") - getContext().int_const("0");
        itv[2] = itv[1] - itv[0];

        // Test extract sub vars
        Set<u32_t> res;
        relation.extractSubVars(relation[2], res);
        assert(res == Set<u32_t>({0, 1, 2}) && "inconsistency occurs");
        IntervalESBase inv = itv.sliceState(res);
        RelationSolver rs;
        const Z3Expr& relExpr = relation[2] && relation[1];
        const Z3Expr& initExpr = rs.gamma_hat(inv);
        const Z3Expr& phi = (relExpr && initExpr).simplify();
        IntervalESBase resRSY = rs.RSY(inv, phi);
        IntervalESBase resBilateral = rs.bilateral(inv, phi);
        IntervalESBase resBS = rs.BS(inv, phi);
        // 0:[0,100] 1:[0,100] 2:[0,0]
        assert(resRSY == resBS && resBS == resBilateral && "inconsistency occurs");
        for (auto r : resRSY.getVarToVal())
        {
            outs() << r.first << " " << r.second << "\n";
        }
        // ground truth
        IntervalESBase::VarToValMap intendedRes = {{0, IntervalValue(0, 100)},
            {1, IntervalValue(0, 100)},
            {2, IntervalValue(0, 0)}
        };
        assert(IntervalESBase::eqVarToValMap(resBS.getVarToVal(), intendedRes) && "inconsistency occurs");
    }

    void testRelExeState2_3()
    {
        SVFUtil::outs() << "test2_3 start\n";
        IntervalESBase itv;
        RelExeState relation;
        // var0 := [0, 1000];
        relation[0] = getContext().int_const("0");
        itv[0] = IntervalValue(0, 1000);
        // var1 := var0;
        relation[1] =
            getContext().int_const("1") == getContext().int_const("0");
        itv[1] = itv[0];
        // var2 := var1 - var0;
        relation[2] = getContext().int_const("2") ==
                      getContext().int_const("1") - getContext().int_const("0");
        itv[2] = itv[1] - itv[0];

        // Test extract sub vars
        Set<u32_t> res;
        relation.extractSubVars(relation[2], res);
        assert(res == Set<u32_t>({0, 1, 2}) && "inconsistency occurs");
        IntervalESBase inv = itv.sliceState(res);
        RelationSolver rs;
        const Z3Expr& relExpr = relation[2] && relation[1];
        const Z3Expr& initExpr = rs.gamma_hat(inv);
        const Z3Expr& phi = (relExpr && initExpr).simplify();
        IntervalESBase resRSY = rs.RSY(inv, phi);
        IntervalESBase resBilateral = rs.bilateral(inv, phi);
        IntervalESBase resBS = rs.BS(inv, phi);
        // 0:[0,1000] 1:[0,1000] 2:[0,0]
        assert(resRSY == resBS && resBS == resBilateral && "inconsistency occurs");
        for (auto r : resRSY.getVarToVal())
        {
            outs() << r.first << " " << r.second << "\n";
        }
        // ground truth
        // ground truth
        IntervalESBase::VarToValMap intendedRes = {{0, IntervalValue(0, 1000)},
            {1, IntervalValue(0, 1000)},
            {2, IntervalValue(0, 0)}
        };
        assert(IntervalESBase::eqVarToValMap(resBS.getVarToVal(), intendedRes) && "inconsistency occurs");
    }

    void testRelExeState2_4()
    {
        SVFUtil::outs() << "test2_4 start\n";
        IntervalESBase itv;
        RelExeState relation;
        // var0 := [0, 10000];
        relation[0] = getContext().int_const("0");
        itv[0] = IntervalValue(0, 10000);
        // var1 := var0;
        relation[1] =
            getContext().int_const("1") == getContext().int_const("0");
        itv[1] = itv[0];
        // var2 := var1 - var0;
        relation[2] = getContext().int_const("2") ==
                      getContext().int_const("1") - getContext().int_const("0");
        itv[2] = itv[1] - itv[0];

        // Test extract sub vars
        Set<u32_t> res;
        relation.extractSubVars(relation[2], res);
        assert(res == Set<u32_t>({0, 1, 2}) && "inconsistency occurs");
        IntervalESBase inv = itv.sliceState(res);
        RelationSolver rs;
        const Z3Expr& relExpr = relation[2] && relation[1];
        const Z3Expr& initExpr = rs.gamma_hat(inv);
        const Z3Expr& phi = (relExpr && initExpr).simplify();
        IntervalESBase resRSY = RSY_time(inv, phi, rs);
        IntervalESBase resBilateral = Bilateral_time(inv, phi, rs);
        IntervalESBase resBS = BS_time(inv, phi, rs);
        // 0:[0,10000] 1:[0,10000] 2:[0,0]
        assert(resRSY == resBS && resBS == resBilateral && "inconsistency occurs");
        for (auto r : resRSY.getVarToVal())
        {
            outs() << r.first << " " << r.second << "\n";
        }
        // ground truth
        // ground truth
        IntervalESBase::VarToValMap intendedRes = {{0, IntervalValue(0, 10000)},
            {1, IntervalValue(0, 10000)},
            {2, IntervalValue(0, 0)}
        };
        assert(IntervalESBase::eqVarToValMap(resBS.getVarToVal(), intendedRes) && "inconsistency occurs");
    }

    void testRelExeState2_5()
    {
        SVFUtil::outs() << "test2_5 start\n";
        IntervalESBase itv;
        RelExeState relation;
        // var0 := [0, 100000];
        relation[0] = getContext().int_const("0");
        itv[0] = IntervalValue(0, 100000);
        // var1 := var0;
        relation[1] =
            getContext().int_const("1") == getContext().int_const("0");
        itv[1] = itv[0];
        // var2 := var1 - var0;
        relation[2] = getContext().int_const("2") ==
                      getContext().int_const("1") - getContext().int_const("0");
        itv[2] = itv[1] - itv[0];

        // Test extract sub vars
        Set<u32_t> res;
        relation.extractSubVars(relation[2], res);
        assert(res == Set<u32_t>({0, 1, 2}) && "inconsistency occurs");
        IntervalESBase inv = itv.sliceState(res);
        RelationSolver rs;
        const Z3Expr& relExpr = relation[2] && relation[1];
        const Z3Expr& initExpr = rs.gamma_hat(inv);
        const Z3Expr& phi = (relExpr && initExpr).simplify();
        IntervalESBase resRSY = RSY_time(inv, phi, rs);
        IntervalESBase resBilateral = Bilateral_time(inv, phi, rs);
        IntervalESBase resBS = BS_time(inv, phi, rs);
        // 0:[0,100000] 1:[0,100000] 2:[0,0]
        assert(resRSY == resBS && resBS == resBilateral && "inconsistency occurs");
        for (auto r : resRSY.getVarToVal())
        {
            outs() << r.first << " " << r.second << "\n";
        }
        // ground truth
        // ground truth
        IntervalESBase::VarToValMap intendedRes = {{0, IntervalValue(0, 100000)},
            {1, IntervalValue(0, 100000)},
            {2, IntervalValue(0, 0)}
        };
        assert(IntervalESBase::eqVarToValMap(resBS.getVarToVal(), intendedRes) && "inconsistency occurs");
    }

    void testRelExeState3_1()
    {
        SVFUtil::outs() << "test3_1 start\n";
        IntervalESBase itv;
        RelExeState relation;
        // var0 := [1, 10];
        relation[0] = getContext().int_const("0");
        itv[0] = IntervalValue(1, 10);
        // var1 := var0;
        relation[1] =
            getContext().int_const("1") == getContext().int_const("0");
        itv[1] = itv[0];
        // var2 := var1 / var0;
        relation[2] = getContext().int_const("2") ==
                      getContext().int_const("1") / getContext().int_const("0");
        itv[2] = itv[1] / itv[0];
        // Test extract sub vars
        Set<u32_t> res;
        relation.extractSubVars(relation[2], res);
        assert(res == Set<u32_t>({0, 1, 2}) && "inconsistency occurs");
        IntervalESBase inv = itv.sliceState(res);
        RelationSolver rs;
        const Z3Expr& relExpr = relation[2] && relation[1];
        const Z3Expr& initExpr = rs.gamma_hat(inv);
        const Z3Expr& phi = (relExpr && initExpr).simplify();
        IntervalESBase resRSY = rs.RSY(inv, phi);
        IntervalESBase resBilateral = rs.bilateral(inv, phi);
        IntervalESBase resBS = rs.BS(inv, phi);
        // 0:[1,10] 1:[1,10] 2:[1,1]
        assert(resRSY == resBS && resBS == resBilateral && "inconsistency occurs");
        for (auto r : resRSY.getVarToVal())
        {
            outs() << r.first << " " << r.second << "\n";
        }
        // ground truth
        IntervalESBase::VarToValMap intendedRes = {{0, IntervalValue(1, 10)},
            {1, IntervalValue(1, 10)},
            {2, IntervalValue(1, 1)}
        };
        assert(IntervalESBase::eqVarToValMap(resBS.getVarToVal(), intendedRes) && "inconsistency occurs");
    }

    void testRelExeState3_2()
    {
        SVFUtil::outs() << "test3_2 start\n";
        IntervalESBase itv;
        RelExeState relation;
        // var0 := [1, 1000];
        relation[0] = getContext().int_const("0");
        itv[0] = IntervalValue(1, 1000);
        // var1 := var0;
        relation[1] =
            getContext().int_const("1") == getContext().int_const("0");
        itv[1] = itv[0];
        // var2 := var1 / var0;
        relation[2] = getContext().int_const("2") ==
                      getContext().int_const("1") / getContext().int_const("0");
        itv[2] = itv[1] / itv[0];
        // Test extract sub vars
        Set<u32_t> res;
        relation.extractSubVars(relation[2], res);
        assert(res == Set<u32_t>({0, 1, 2}) && "inconsistency occurs");
        IntervalESBase inv = itv.sliceState(res);
        RelationSolver rs;
        const Z3Expr& relExpr = relation[2] && relation[1];
        const Z3Expr& initExpr = rs.gamma_hat(inv);
        const Z3Expr& phi = (relExpr && initExpr).simplify();
        IntervalESBase resRSY = rs.RSY(inv, phi);
        IntervalESBase resBilateral = rs.bilateral(inv, phi);
        IntervalESBase resBS = rs.BS(inv, phi);
        // 0:[1,1000] 1:[1,1000] 2:[1,1]
        assert(resRSY == resBS && resBS == resBilateral && "inconsistency occurs");
        for (auto r : resRSY.getVarToVal())
        {
            outs() << r.first << " " << r.second << "\n";
        }
        // ground truth
        IntervalESBase::VarToValMap intendedRes = {{0, IntervalValue(1, 1000)},
            {1, IntervalValue(1, 1000)},
            {2, IntervalValue(1, 1)}
        };
        assert(IntervalESBase::eqVarToValMap(resBS.getVarToVal(), intendedRes) && "inconsistency occurs");
    }

    void testRelExeState3_3()
    {
        SVFUtil::outs() << "test3_3 start\n";
        IntervalESBase itv;
        RelExeState relation;
        // var0 := [1, 10000];
        relation[0] = getContext().int_const("0");
        itv[0] = IntervalValue(1, 10000);
        // var1 := var0;
        relation[1] =
            getContext().int_const("1") == getContext().int_const("0");
        itv[1] = itv[0];
        // var2 := var1 / var0;
        relation[2] = getContext().int_const("2") ==
                      getContext().int_const("1") / getContext().int_const("0");
        itv[2] = itv[1] / itv[0];
        // Test extract sub vars
        Set<u32_t> res;
        relation.extractSubVars(relation[2], res);
        assert(res == Set<u32_t>({0, 1, 2}) && "inconsistency occurs");
        IntervalESBase inv = itv.sliceState(res);
        RelationSolver rs;
        const Z3Expr& relExpr = relation[2] && relation[1];
        const Z3Expr& initExpr = rs.gamma_hat(inv);
        const Z3Expr& phi = (relExpr && initExpr).simplify();
        IntervalESBase resRSY = RSY_time(inv, phi, rs);
        IntervalESBase resBilateral = Bilateral_time(inv, phi, rs);
        IntervalESBase resBS = BS_time(inv, phi, rs);
        // 0:[1,10000] 1:[1,10000] 2:[1,1]
        assert(resRSY == resBS && resBS == resBilateral && "inconsistency occurs");
        for (auto r : resRSY.getVarToVal())
        {
            outs() << r.first << " " << r.second << "\n";
        }
        // ground truth
        IntervalESBase::VarToValMap intendedRes =
        Map<u32_t, IntervalValue>({{0, IntervalValue(1, 10000)},
            {1, IntervalValue(1, 10000)},
            {2, IntervalValue(1, 1)}});
    }

    void testRelExeState3_4()
    {
        SVFUtil::outs() << "test3_4 start\n";
        IntervalESBase itv;
        RelExeState relation;
        // var0 := [1, 100000];
        relation[0] = getContext().int_const("0");
        itv[0] = IntervalValue(1, 100000);
        // var1 := var0;
        relation[1] =
            getContext().int_const("1") == getContext().int_const("0");
        itv[1] = itv[0];
        // var2 := var1 / var0;
        relation[2] = getContext().int_const("2") ==
                      getContext().int_const("1") / getContext().int_const("0");
        itv[2] = itv[1] / itv[0];
        // Test extract sub vars
        Set<u32_t> res;
        relation.extractSubVars(relation[2], res);
        assert(res == Set<u32_t>({0, 1, 2}) && "inconsistency occurs");
        IntervalESBase inv = itv.sliceState(res);
        RelationSolver rs;
        const Z3Expr& relExpr = relation[2] && relation[1];
        const Z3Expr& initExpr = rs.gamma_hat(inv);
        const Z3Expr& phi = (relExpr && initExpr).simplify();
        IntervalESBase resRSY = RSY_time(inv, phi, rs);
        IntervalESBase resBilateral = Bilateral_time(inv, phi, rs);
        IntervalESBase resBS = BS_time(inv, phi, rs);
        // 0:[1,100000] 1:[1,100000] 2:[1,1]
        assert(resRSY == resBS && resBS == resBilateral && "inconsistency occurs");
        for (auto r : resRSY.getVarToVal())
        {
            outs() << r.first << " " << r.second << "\n";
        }
        // ground truth
        IntervalESBase::VarToValMap intendedRes = {{0, IntervalValue(1, 100000)},
            {1, IntervalValue(1, 100000)},
            {2, IntervalValue(1, 1)}
        };
        assert(IntervalESBase::eqVarToValMap(resBS.getVarToVal(), intendedRes) && "inconsistency occurs");
    }

    void testRelExeState4_1()
    {
        SVFUtil::outs() << "test4_1 start\n";
        IntervalESBase itv;
        RelExeState relation;
        // var0 := [0, 10];
        relation[0] = getContext().int_const("0");
        itv[0] = IntervalValue(0, 10);
        // var1 := var0;
        relation[1] =
            getContext().int_const("1") == getContext().int_const("0");
        itv[1] = itv[0];
        // var2 := var1 / var0;
        relation[2] = getContext().int_const("2") ==
                      getContext().int_const("1") / getContext().int_const("0");
        itv[2] = itv[1] / itv[0];
        // Test extract sub vars
        Set<u32_t> res;
        relation.extractSubVars(relation[2], res);
        assert(res == Set<u32_t>({0, 1, 2}) && "inconsistency occurs");
        IntervalESBase inv = itv.sliceState(res);
        RelationSolver rs;
        const Z3Expr& relExpr = relation[2] && relation[1];
        const Z3Expr& initExpr = rs.gamma_hat(inv);
        const Z3Expr& phi = (relExpr && initExpr).simplify();
        // IntervalExeState resRSY = rs.RSY(inv, phi);
        outs() << "rsy done\n";
        // IntervalExeState resBilateral = rs.bilateral(inv, phi);
        outs() << "bilateral done\n";
        IntervalESBase resBS = rs.BS(inv, phi);
        outs() << "bs done\n";
        // 0:[0,10] 1:[0,10] 2:[-00,+00]
        // assert(resRSY == resBS && resBS == resBilateral);
        for (auto r : resBS.getVarToVal())
        {
            outs() << r.first << " " << r.second << "\n";
        }
        // ground truth
        IntervalESBase::VarToValMap intendedRes = {{0, IntervalValue(0, 10)},
            {1, IntervalValue(0, 10)},
            {2, IntervalValue(IntervalValue::minus_infinity(), IntervalValue::plus_infinity())}
        };
        assert(IntervalESBase::eqVarToValMap(resBS.getVarToVal(), intendedRes) && "inconsistency occurs");
    }

    void testsValidation()
    {
        SymblicAbstractionTest saTest;
        saTest.testRelExeState1_1();
        saTest.testRelExeState1_2();

        saTest.testRelExeState2_1();
        saTest.testRelExeState2_2();
        saTest.testRelExeState2_3();
//        saTest.testRelExeState2_4(); /// 10000
//        saTest.testRelExeState2_5(); /// 100000

        saTest.testRelExeState3_1();
        saTest.testRelExeState3_2();
//        saTest.testRelExeState3_3(); /// 10000
//        saTest.testRelExeState3_4(); /// 100000

        outs() << "start top\n";
        saTest.testRelExeState4_1(); /// top
    }
};

int main(int argc, char** argv)
{
    std::vector<std::string> moduleNameVec;
    moduleNameVec = OptionBase::parseOptions(
                        argc, argv, "Source-Sink Bug Detector", "[options] <input-bitcode...>"
                    );
    // if (SYMABS())
    // {
    //     SymblicAbstractionTest saTest;
    //     saTest.testsValidation();
    // }


    z3::context& c = Z3Expr::getContext();
    z3::set_param("pp.decimal", true); // set decimal notation
    z3::set_param("pp.decimal-precision", 2); // increase number of decimal places to 50.
    // z3::set_param("pp.fp_real_literals", true);
    typedef  z3::expr expr;
    expr x = c.real_const("x");
    // expr x = c.fpa_const<32>("x");
    // expr x = c.fpa_const("x", 8, 24);
    // expr constraint = x <= c.fpa_val((float)0.5);

    // expr y = c.real_const("y");
    expr constraint = x >= c.real_val("0.511");

    // expr z = c.real_const("z");
    float lbx = 0, upx = 1, ret = 1;
    z3::solver s = Z3Expr::getSolver();
    s.add(constraint);
    // double lby = 0, upy = 1;
    while (lbx <= upx)
    {

        float mid = (upx - lbx) / 2;
        std::cout << "mid: " << mid << "\n";
        s.push();
        s.add(c.real_val(std::to_string(mid).c_str()) <= x);
        s.add(x <= c.real_val(std::to_string(upx).c_str()));
        // s.add(x*x + y*y == 1);                     // x^2 + y^2 == 1
        // s.add(x*x*x + z*z*z < c.real_val("1/2"));  // x^3 + z^3 < 1/2
        // s.add(y == x / 2);
        // s.add(z == 0.1);
        // s.add(z != 0);
        // s.add(x > 0 && x < 1);
        // std::cout << s << "\n\n";
        float fmax = std::numeric_limits<float>::max(), fmin = std::numeric_limits<float>::min();
        outs() << -(fmax+1) << " " << -fmin << "\n";
        if (s.check() == z3::sat)
        {
            z3::model m = s.get_model();
            z3::expr mm = m.eval(x);
            // z3::set_param("pp.decimal-precision", 50); // increase number of decimal places to 50.

            std::cout << "SAT " << mm << "\n";
            std::cout << "SAT " << mm.get_decimal_string(32) << "\n";
            float res = std::stof(mm.to_string());
            res += 1.0;
            std::cout << "SAT " << res << "\n";
            // Z3_string mmm= Z3_get_numeral_string(c, mm);
            // Z3_string mmm= Z3_get_numeral_string(c, mm);

            // if (mm.is_real())
            // {
            //
            //     // Z3_get_numeral_string
            //     std::cout << "T " << mmm << "\n";
            // }
            ret = mm;
            std::cout << "ret " << ret << "\n";
            lbx = ret + 0.1;
            break;
        } else
        {
            std::cout << s << "\n\n";
            upx = mid - 0.1;
        }
        s.pop();
    }


    std::cout << "res: "<< ret << "\n";


    // std::cout << s.check() << "\n";
    // z3::model m = s.get_model();
    // // std::cout << m << "\n";
    // z3::set_param("pp.decimal", true); // set decimal notation
    // // std::cout << "model in decimal notation\n";
    // // std::cout << m << "\n";
    // z3::set_param("pp.decimal-precision", 50); // increase number of decimal places to 50.
    // // std::cout << "model using 50 decimal places\n";
    // std::cout << m << "\n";
    z3::set_param("pp.decimal", false); // disable decimal notation
    return 0;
}
