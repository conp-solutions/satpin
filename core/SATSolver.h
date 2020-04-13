/****************************************************************************************[Dimacs.h]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson
Copyright (c) 2017       Norbert Manthey

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#ifndef Minisat_SATSolver_h
#define Minisat_SATSolver_h

#ifdef HAVE_IPASIR // only if we compile for the ipasir solver
extern "C" {
#include "ipasir.h"

#define IPASIR(x) x
}
#else
#define IPASIR(x)
#endif

#include <cassert>
#include <cstdlib>
#include <iostream>
#include <vector>

#include <core/SolverTypes.h>

namespace SATPin
{

class SATSolver
{

    void *ipasirSolver;
    int maxVar = 0;

    public:
    SATSolver() : ipasirSolver(0)
    {
        IPASIR(ipasirSolver = ipasir_init(););
        IPASIR(std::cerr << "initialized IPASIR solver: " << std::string(ipasir_signature()) << std::endl;);
#ifndef HAVE_IPASIR
        std::cerr << "error: trying to use IPASIR solver without being compiled for ipasir, abort" << std::endl;
        exit(1);
#endif
    }

    ~SATSolver() { IPASIR(if (ipasirSolver) ipasir_release(ipasirSolver);); }

    /** add clause to formula */
    void addClause(std::vector<int> &lits)
    {
        for (int i = 0; i < lits.size(); ++i) {
            IPASIR(ipasir_add(ipasirSolver, lits[i]););
            maxVar = lits[i] > maxVar ? lits[i] : maxVar;
            maxVar = -lits[i] > maxVar ? -lits[i] : maxVar;
        }
        IPASIR(ipasir_add(ipasirSolver, 0););
    }
    /** convert from Minisat to ipasir */
    void addClause(vec<Lit> &lits)
    {
        for (int i = 0; i < lits.size(); ++i) {
            int l = sign(lits[i]) ? -var(lits[i]) - 1 : var(lits[i]) + 1;
            IPASIR(ipasir_add(ipasirSolver, l););
            maxVar = var(lits[i]) + 1 > maxVar ? var(lits[i]) + 1 : maxVar;
        }
        IPASIR(ipasir_add(ipasirSolver, 0););
    }

    /** solve the current formula with the given set of assumptions
     @param assumptions list of variable assignments (+v or -v) that should be assumed during solving
     @param model will contain the model of the formula, +v or -v for each variable v, with model[v] = v or model[v] = -v
     @param conflict set of assumptions that do falsify the formula F, i.e. UNSAT = F \land conflict
     @return 10, if SAT, 20, if 20
     */
    int solve(const std::vector<int> &assumptions, std::vector<int> &model, std::vector<int> &conflict)
    {
        for (int i = 0; i < assumptions.size(); ++i) {
            IPASIR(ipasir_assume(ipasirSolver, assumptions[i]););
            maxVar = assumptions[i] > maxVar ? assumptions[i] : maxVar;
            maxVar = -assumptions[i] > maxVar ? -assumptions[i] : maxVar;
        }
        std::cerr << "solve ipasir with maxvar: " << maxVar << std::endl;
        int SATret = 0;
        IPASIR(SATret = ipasir_solve(ipasirSolver););

        if (SATret == 10) {
            model.clear();
            model.resize(maxVar + 1);
            for (int v = 1; v <= maxVar; ++v) {
                IPASIR(model[v] = ipasir_val(ipasirSolver, v););
            }
        } else if (SATret == 20) {
            conflict.clear();
            for (int i = 0; i < assumptions.size(); ++i) {
                int v = assumptions[i] > 0 ? assumptions[i] : -assumptions[i];
                IPASIR(/*std::cerr << "c failed " << v << std::endl; */ if (ipasir_failed(ipasirSolver, v))
                       conflict.push_back(assumptions[i]););
                IPASIR(/*std::cerr << "c failed " << -v << std::endl;*/ if (ipasir_failed(ipasirSolver, -v))
                       conflict.push_back(-assumptions[i]););
            }
        } else {
            std::cerr << "ipasir SAT solver terminated with unexpected exit code: " << SATret << ". Abort." << std::endl;
            exit(1);
        }

        return SATret;
    }

    int solve(const vec<Lit> &assumptions, vec<lbool> &model, vec<Lit> &conflict)
    {
        for (int i = 0; i < assumptions.size(); ++i) {
            int l = sign(assumptions[i]) ? -var(assumptions[i]) - 1 : var(assumptions[i]) + 1;
            maxVar = var(assumptions[i]) + 1 > maxVar ? var(assumptions[i]) + 1 : maxVar;
            IPASIR(ipasir_assume(ipasirSolver, l););
            // std::cerr << "ipasir assumed " << l << std::endl;
        }
        int SATret = 0;
        IPASIR(SATret = ipasir_solve(ipasirSolver););
        // std::cerr << "ipasir finished with return code " << SATret << std::endl;

        if (SATret == 10) {
            model.clear();
            model.growTo(maxVar);
            for (int v = 1; v <= maxVar; ++v) {
                IPASIR(model[v - 1] = ipasir_val(ipasirSolver, v) > 0 ? l_True : l_False;);
            }
        } else if (SATret == 20) {
            conflict.clear();
            for (int i = 0; i < assumptions.size(); ++i) {
                int v = var(assumptions[i]) + 1;
                // std::cerr << "test variable " << v << " (lit " << assumptions[i] << ") being failed" << std::endl;
                IPASIR(if (ipasir_failed(ipasirSolver, -v)) { /* std::cerr << "c failed " << v << std::endl; */
                                                              conflict.push(~assumptions[i]);
                });
                // IPASIR( if(ipasir_failed(ipasirSolver, v)) { std::cerr << "c failed " << -v << std::endl; std::cerr << "        do not add to conflict??" << std::endl;} );
            }
        } else {
            std::cerr << "ipasir SAT solver terminated with unexpected exit code: " << SATret << ". Abort." << std::endl;
            exit(1);
        }

        return SATret;
    }
};

} // namespace SATPin

#endif
