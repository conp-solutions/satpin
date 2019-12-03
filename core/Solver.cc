/***************************************************************************************[Solver.cc]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

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

#include <math.h>
#include <string>

#include "core/Solver.h"
#include "mtl/Sort.h"

#include "core/SATSolver.h"

using namespace Minisat;

#include "utils/System.h" // for the cputime
#include <sstream>
using namespace std; // debug output

//=================================================================================================
// Options:


static const char *_cat = "CORE";

static DoubleOption opt_var_decay(_cat, "var-decay", "The variable activity decay factor", 0.95, DoubleRange(0, false, 1, false));
static DoubleOption opt_clause_decay(_cat, "cla-decay", "The clause activity decay factor", 0.999, DoubleRange(0, false, 1, false));
static DoubleOption
opt_random_var_freq(_cat,
                    "rnd-freq",
                    "The frequency with which the decision heuristic tries to choose a random variable",
                    0,
                    DoubleRange(0, true, 1, true));
static DoubleOption
opt_random_seed(_cat, "rnd-seed", "Used by the random variable selection", 91648253, DoubleRange(0, false, HUGE_VAL, false));
static IntOption
opt_ccmin_mode(_cat, "ccmin-mode", "Controls conflict clause minimization (0=none, 1=basic, 2=deep)", 2, IntRange(0, 2));
static IntOption
opt_phase_saving(_cat, "phase-saving", "Controls the level of phase saving (0=none, 1=limited, 2=full)", 2, IntRange(0, 2));
static BoolOption opt_rnd_init_act(_cat, "rnd-init", "Randomize the initial activity", false);
static BoolOption opt_luby_restart(_cat, "luby", "Use the Luby restart sequence", true);
static IntOption opt_restart_first(_cat, "rfirst", "The base restart interval", 100, IntRange(1, INT32_MAX));
static DoubleOption opt_restart_inc(_cat, "rinc", "Restart interval increase factor", 2, DoubleRange(1, false, HUGE_VAL, false));
static DoubleOption opt_garbage_frac(_cat,
                                     "gc-frac",
                                     "The fraction of wasted memory allowed before a garbage collection is triggered",
                                     0.20,
                                     DoubleRange(0, false, HUGE_VAL, false));

/* Norbert
 * Add option to modify the default assumption behavior of the solver
 */
static BoolOption opt_imply_check("EL", "implyCheck", "Question last assumption only", true);
static IntOption opt_max_calls("EL", "maxCalls", "maximum calls to outer solver", INT32_MAX, IntRange(1, INT32_MAX));
static BoolOption opt_eldbg("EL", "eldbg", "Enable all the EL debug output", false);

static IntOption opt_reduce("EL", "reduce", "delete irrelevant clauses/assumptions (2=re-add)", 0, IntRange(0, 2));
static BoolOption opt_reduceLits("EL", "reduceLits", "Calculate Cone Of Influcenece based on literals", false);

#ifdef HAVE_IPASIR
static BoolOption opt_optext("EL", "ipasir", "Enable ipasir solver instead of local one", false);
static BoolOption opt_sort("EL", "elsort", "Sort MinAs and assumptions before giving to solver (for IPASIR only)", false);
#endif

static BoolOption opt_modelClause("EL", "modelClauses", "generate models based on seen conflict clauses", true);
static BoolOption opt_keepSearch("EL", "keepSearch", "jump back only as far as necessary in outer call", false);
static BoolOption opt_avoidSubModel("EL", "noSubModel", "enforce that from a model a sub model is never tested", true);
static BoolOption opt_subsumeBlocks("EL", "irredModCls", "ensure that model clauses do not subsume each other", false);
static BoolOption opt_minimalOnly("EL", "minimal", "minimize conflicting sets eagerly", false);

//=================================================================================================
// Constructor/Destructor:


Solver::Solver()
  :

  // Parameters (user settable):
  //
  verbosity(0)
  , var_decay(opt_var_decay)
  , clause_decay(opt_clause_decay)
  , random_var_freq(opt_random_var_freq)
  , random_seed(opt_random_seed)
  , luby_restart(opt_luby_restart)
  , ccmin_mode(opt_ccmin_mode)
  , phase_saving(opt_phase_saving)
  , rnd_pol(false)
  , rnd_init_act(opt_rnd_init_act)
  , garbage_frac(opt_garbage_frac)
  , restart_first(opt_restart_first)
  , restart_inc(opt_restart_inc)

  // Parameters (the rest):
  //
  , learntsize_factor((double)1 / (double)3)
  , learntsize_inc(1.1)

  // Parameters (experimental):
  //
  , learntsize_adjust_start_confl(100)
  , learntsize_adjust_inc(1.5)

  // Statistics: (formerly in 'SolverStats')
  //
  , solves(0)
  , starts(0)
  , decisions(0)
  , rnd_decisions(0)
  , propagations(0)
  , conflicts(0)
  , dec_vars(0)
  , clauses_literals(0)
  , learnts_literals(0)
  , max_literals(0)
  , tot_literals(0)

  , ok(true)
  , cla_inc(1)
  , var_inc(1)
  , watches(WatcherDeleted(ca))
  , qhead(0)
  , simpDB_assigns(-1)
  , simpDB_props(0)
  , order_heap(VarOrderLt(activity))
  , progress_estimate(0)
  , remove_satisfied(true)

  // Resource constraints:
  //
  , conflict_budget(-1)
  , propagation_budget(-1)
  , asynch_interrupt(false)

  /* Norbert
   * Have the option as solver attribute
   */
  , imply_check(opt_imply_check)
  , generateClauseModels(false) // usually, use the simple search of the tool
  , localDebug(false)
  , satTreeFastForward(0)
  , unsatTreeFastForward(0)
  , artificialSatLevel(-1)

  , minimalChecks(0)
  , minimizations(0)
  , minimizationBackjump(0)

{
}


Solver::~Solver() {}


//=================================================================================================
// Minor methods:


// Creates a new SAT variable in the solver. If 'decision' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
//
Var Solver::newVar(bool sign, bool dvar)
{
    int v = nVars();
    watches.init(mkLit(v, false));
    watches.init(mkLit(v, true));
    assigns.push(l_Undef);
    vardata.push(mkVarData(CRef_Undef, 0));
    // activity .push(0);
    activity.push(rnd_init_act ? drand(random_seed) * 0.00001 : 0);
    seen.push(0);
    polarity.push(sign);
    decision.push();
    trail.capacity(v + 1);
    setDecisionVar(v, dvar);
    return v;
}


bool Solver::addClause_(vec<Lit> &ps)
{
    assert(decisionLevel() == 0);
    if (!ok) return false;

    // Check if clause is satisfied and remove false/duplicate literals:
    sort(ps);
    Lit p;
    int i, j;
    for (i = j = 0, p = lit_Undef; i < ps.size(); i++)
        if (value(ps[i]) == l_True || ps[i] == ~p)
            return true;
        else if (value(ps[i]) != l_False && ps[i] != p)
            ps[j++] = p = ps[i];
    ps.shrink(i - j);

    if (ps.size() == 0)
        return ok = false;
    else if (ps.size() == 1) {
        uncheckedEnqueue(ps[0]);
        return ok = (propagate() == CRef_Undef);
    } else {
        CRef cr = ca.alloc(ps, false);
        clauses.push(cr);
        attachClause(cr);
    }

    return true;
}


void Solver::attachClause(CRef cr)
{
    const Clause &c = ca[cr];
    assert(c.size() > 1);
    watches[~c[0]].push(Watcher(cr, c[1]));
    watches[~c[1]].push(Watcher(cr, c[0]));
    if (c.learnt())
        learnts_literals += c.size();
    else
        clauses_literals += c.size();
}


void Solver::detachClause(CRef cr, bool strict)
{
    const Clause &c = ca[cr];
    assert(c.size() > 1);

    if (strict) {
        remove(watches[~c[0]], Watcher(cr, c[1]));
        remove(watches[~c[1]], Watcher(cr, c[0]));
    } else {
        // Lazy detaching: (NOTE! Must clean all watcher lists before garbage collecting this clause)
        watches.smudge(~c[0]);
        watches.smudge(~c[1]);
    }

    if (c.learnt())
        learnts_literals -= c.size();
    else
        clauses_literals -= c.size();
}


void Solver::removeClause(CRef cr)
{
    Clause &c = ca[cr];
    detachClause(cr);
    // Don't leave pointers to free'd memory!
    if (locked(c)) vardata[var(c[0])].reason = CRef_Undef;
    c.mark(1);
    ca.free(cr);
}


bool Solver::satisfied(const Clause &c) const
{
    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) == l_True) return true;
    return false;
}


// Revert to the state at given level (keeping all assignment at 'level' but not beyond).
//
void Solver::cancelUntil(int level)
{
    if (decisionLevel() > level) {
        for (int c = trail.size() - 1; c >= trail_lim[level]; c--) {
            Var x = var(trail[c]);
            assigns[x] = l_Undef;
            if (phase_saving > 1 || (phase_saving == 1) && c > trail_lim.last()) polarity[x] = sign(trail[c]);
            insertVarOrder(x);
        }
        qhead = trail_lim[level];
        trail.shrink(trail.size() - trail_lim[level]);
        trail_lim.shrink(trail_lim.size() - level);
    }
}


//=================================================================================================
// Major methods:


Lit Solver::pickBranchLit()
{
    Var next = var_Undef;

    // Random decision:
    if (drand(random_seed) < random_var_freq && !order_heap.empty()) {
        next = order_heap[irand(random_seed, order_heap.size())];
        if (value(next) == l_Undef && decision[next]) rnd_decisions++;
    }

    // Activity based decision:
    while (next == var_Undef || value(next) != l_Undef || !decision[next])
        if (order_heap.empty()) {
            next = var_Undef;
            break;
        } else
            next = order_heap.removeMin();

    return next == var_Undef ? lit_Undef : mkLit(next, rnd_pol ? drand(random_seed) < 0.5 : polarity[next]);
}


/*_________________________________________________________________________________________________
|
|  analyze : (confl : Clause*) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
|
|  Description:
|    Analyze conflict and produce a reason clause.
|
|    Pre-conditions:
|      * 'out_learnt' is assumed to be cleared.
|      * Current decision level must be greater than root level.
|
|    Post-conditions:
|      * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
|      * If out_learnt.size() > 1 then 'out_learnt[1]' has the greatest decision level of the
|        rest of literals. There may be others from the same level though.
|
|________________________________________________________________________________________________@*/
void Solver::analyze(CRef confl, vec<Lit> &out_learnt, int &out_btlevel)
{
    int pathC = 0;
    Lit p = lit_Undef;

    // Generate conflict clause:
    //
    out_learnt.push(); // (leave room for the asserting literal)
    int index = trail.size() - 1;

    do {
        assert(confl != CRef_Undef); // (otherwise should be UIP)
        Clause &c = ca[confl];

        if (c.learnt()) claBumpActivity(c);

        for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++) {
            Lit q = c[j];

            if (!seen[var(q)] && level(var(q)) > 0) {
                varBumpActivity(var(q));
                seen[var(q)] = 1;
                if (level(var(q)) >= decisionLevel())
                    pathC++;
                else
                    out_learnt.push(q);
            }
        }

        // Select next clause to look at:
        while (!seen[var(trail[index--])])
            ;
        p = trail[index + 1];
        confl = reason(var(p));
        seen[var(p)] = 0;
        pathC--;

    } while (pathC > 0);
    out_learnt[0] = ~p;

    // Simplify conflict clause:
    //
    int i, j;
    out_learnt.copyTo(analyze_toclear);
    if (ccmin_mode == 2) {
        uint32_t abstract_level = 0;
        for (i = 1; i < out_learnt.size(); i++)
            abstract_level |= abstractLevel(var(out_learnt[i])); // (maintain an abstraction of levels involved in conflict)

        for (i = j = 1; i < out_learnt.size(); i++)
            if (reason(var(out_learnt[i])) == CRef_Undef || !litRedundant(out_learnt[i], abstract_level))
                out_learnt[j++] = out_learnt[i];

    } else if (ccmin_mode == 1) {
        for (i = j = 1; i < out_learnt.size(); i++) {
            Var x = var(out_learnt[i]);

            if (reason(x) == CRef_Undef)
                out_learnt[j++] = out_learnt[i];
            else {
                Clause &c = ca[reason(var(out_learnt[i]))];
                for (int k = 1; k < c.size(); k++)
                    if (!seen[var(c[k])] && level(var(c[k])) > 0) {
                        out_learnt[j++] = out_learnt[i];
                        break;
                    }
            }
        }
    } else
        i = j = out_learnt.size();

    max_literals += out_learnt.size();
    out_learnt.shrink(i - j);
    tot_literals += out_learnt.size();

    // Find correct backtrack level:
    //
    if (out_learnt.size() == 1)
        out_btlevel = 0;
    else {
        int max_i = 1;
        // Find the first literal assigned at the next-highest level:
        for (int i = 2; i < out_learnt.size(); i++)
            if (level(var(out_learnt[i])) > level(var(out_learnt[max_i]))) max_i = i;
        // Swap-in this literal at index 1:
        Lit p = out_learnt[max_i];
        out_learnt[max_i] = out_learnt[1];
        out_learnt[1] = p;
        out_btlevel = level(var(p));
    }

    for (int j = 0; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0; // ('seen[]' is now cleared)
}


// Check if 'p' can be removed. 'abstract_levels' is used to abort early if the algorithm is
// visiting literals at levels that cannot be removed later.
bool Solver::litRedundant(Lit p, uint32_t abstract_levels)
{
    analyze_stack.clear();
    analyze_stack.push(p);
    int top = analyze_toclear.size();
    while (analyze_stack.size() > 0) {
        assert(reason(var(analyze_stack.last())) != CRef_Undef);
        Clause &c = ca[reason(var(analyze_stack.last()))];
        analyze_stack.pop();

        for (int i = 1; i < c.size(); i++) {
            Lit p = c[i];
            if (!seen[var(p)] && level(var(p)) > 0) {
                if (reason(var(p)) != CRef_Undef && (abstractLevel(var(p)) & abstract_levels) != 0) {
                    seen[var(p)] = 1;
                    analyze_stack.push(p);
                    analyze_toclear.push(p);
                } else {
                    for (int j = top; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0;
                    analyze_toclear.shrink(analyze_toclear.size() - top);
                    return false;
                }
            }
        }
    }

    return true;
}


/*_________________________________________________________________________________________________
|
|  analyzeFinal : (p : Lit)  ->  [void]
|
|  Description:
|    Specialized analysis procedure to express the final conflict in terms of assumptions.
|    Calculates the (possibly empty) set of assumptions that led to the assignment of 'p', and
|    stores the result in 'out_conflict'.
|________________________________________________________________________________________________@*/
void Solver::analyzeFinal(Lit p, vec<Lit> &out_conflict)
{
    out_conflict.clear();
    out_conflict.push(p);

    if (decisionLevel() == 0) return;

    seen[var(p)] = 1;

    for (int i = trail.size() - 1; i >= trail_lim[0]; i--) {
        Var x = var(trail[i]);
        if (seen[x]) {
            if (reason(x) == CRef_Undef) {
                assert(level(x) > 0);
                out_conflict.push(~trail[i]);
            } else {
                Clause &c = ca[reason(x)];
                for (int j = 1; j < c.size(); j++)
                    if (level(var(c[j])) > 0) seen[var(c[j])] = 1;
            }
            seen[x] = 0;
        }
    }

    seen[var(p)] = 0;
}


void Solver::uncheckedEnqueue(Lit p, CRef from)
{
    assert(value(p) == l_Undef);
    assigns[var(p)] = lbool(!sign(p));
    vardata[var(p)] = mkVarData(from, decisionLevel());
    // prefetch watch lists
    __builtin_prefetch(&watches[p], 1, 0); // prefetch the watch, prepare for a write (1), the data is highly temoral (0) // FIXME: after ternary clause modificatoin, write is no longer necessary
    trail.push_(p);
    assert((from == CRef_Undef || ca[from].size() == 1 || level(var(ca[from][0])) == level(var(ca[from][1]))) &&
           "ensure reason properties");
}


/*_________________________________________________________________________________________________
|
|  propagate : [void]  ->  [Clause*]
|
|  Description:
|    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
|    otherwise CRef_Undef.
|
|    Post-conditions:
|      * the propagation queue is empty, even if there was a conflict.
|________________________________________________________________________________________________@*/
CRef Solver::propagate()
{
    CRef confl = CRef_Undef;
    int num_props = 0;
    watches.cleanAll();

    while (qhead < trail.size()) {
        Lit p = trail[qhead++]; // 'p' is enqueued fact to propagate.
        vec<Watcher> &ws = watches[p];
        Watcher *i, *j, *end;
        num_props++;

        if (localDebug) {
            cerr << "c [localDebug] propagate " << p << " with reason [" << reason(var(p)) << "]" << endl;
            if (reason(var(p)) != CRef_Undef) cerr << "c [localDebug] reason clause " << ca[reason(var(p))] << endl;
        }

        for (i = j = (Watcher *)ws, end = i + ws.size(); i != end;) {
            // Try to avoid inspecting the clause:
            Lit blocker = i->blocker;
            if (value(blocker) == l_True) {
                *j++ = *i++;
                continue;
            }

            // Make sure the false literal is data[1]:
            CRef cr = i->cref;
            Clause &c = ca[cr];
            Lit false_lit = ~p;
            if (c[0] == false_lit) c[0] = c[1], c[1] = false_lit;
            assert(c[1] == false_lit);
            i++;

            // If 0th watch is true, then clause is already satisfied.
            Lit first = c[0];
            Watcher w = Watcher(cr, first);
            if (first != blocker && value(first) == l_True) {
                *j++ = w;
                continue;
            }

            // Look for new watch:
            for (int k = 2; k < c.size(); k++)
                if (value(c[k]) != l_False) {
                    c[1] = c[k];
                    c[k] = false_lit;
                    watches[~c[1]].push(w);
                    goto NextClause;
                }

            // Did not find watch -- clause is unit under assignment:
            *j++ = w;
            if (value(first) == l_False) {
                confl = cr;
                qhead = trail.size();
                // Copy the remaining watches:
                while (i < end) *j++ = *i++;
            } else
                uncheckedEnqueue(first, cr);

        NextClause:;
        }
        ws.shrink(i - j);
    }
    propagations += num_props;
    simpDB_props -= num_props;

    return confl;
}


/*_________________________________________________________________________________________________
|
|  reduceDB : ()  ->  [void]
|
|  Description:
|    Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
|    clauses are clauses that are reason to some assignment. Binary clauses are never removed.
|________________________________________________________________________________________________@*/
struct reduceDB_lt {
    ClauseAllocator &ca;
    reduceDB_lt(ClauseAllocator &ca_) : ca(ca_) {}
    bool operator()(CRef x, CRef y)
    {
        return ca[x].size() > 2 && (ca[y].size() == 2 || ca[x].activity() < ca[y].activity());
    }
};
void Solver::reduceDB()
{
    int i, j;
    double extra_lim = cla_inc / learnts.size(); // Remove any clause below this activity

    sort(learnts, reduceDB_lt(ca));
    // Don't delete binary or locked clauses. From the rest, delete clauses from the first half
    // and clauses with activity smaller than 'extra_lim':
    for (i = j = 0; i < learnts.size(); i++) {
        Clause &c = ca[learnts[i]];
        if (c.size() > 2 && !locked(c) && (i < learnts.size() / 2 || c.activity() < extra_lim))
            removeClause(learnts[i]);
        else
            learnts[j++] = learnts[i];
    }
    learnts.shrink(i - j);
    checkGarbage();
}


void Solver::removeSatisfied(vec<CRef> &cs)
{
    int i, j;
    for (i = j = 0; i < cs.size(); i++) {
        Clause &c = ca[cs[i]];
        if (satisfied(c))
            removeClause(cs[i]);
        else
            cs[j++] = cs[i];
    }
    cs.shrink(i - j);
}


void Solver::rebuildOrderHeap()
{
    vec<Var> vs;
    for (Var v = 0; v < nVars(); v++)
        if (decision[v] && value(v) == l_Undef) vs.push(v);
    order_heap.build(vs);
}


/*_________________________________________________________________________________________________
|
|  simplify : [void]  ->  [bool]
|
|  Description:
|    Simplify the clause database according to the current top-level assigment. Currently, the only
|    thing done here is the removal of satisfied clauses, but more things can be put here.
|________________________________________________________________________________________________@*/
bool Solver::simplify()
{
    assert(decisionLevel() == 0);

    if (!ok || propagate() != CRef_Undef) return ok = false;

    if (nAssigns() == simpDB_assigns || (simpDB_props > 0)) return true;

    // Remove satisfied clauses:
    removeSatisfied(learnts);
    if (remove_satisfied) // Can be turned off.
        removeSatisfied(clauses);
    checkGarbage();
    rebuildOrderHeap();

    simpDB_assigns = nAssigns();
    simpDB_props = clauses_literals + learnts_literals; // (shouldn't depend on stats really, but it will do for now)

    return true;
}


/*_________________________________________________________________________________________________
|
|  search : (nof_conflicts : int) (params : const SearchParams&)  ->  [lbool]
|
|  Description:
|    Search for a model the specified number of conflicts.
|    NOTE! Use negative value for 'nof_conflicts' indicate infinity.
|
|  Output:
|    'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
|    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
|    if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
|________________________________________________________________________________________________@*/
lbool Solver::search(int nof_conflicts)
{
    assert(ok);
    int backtrack_level;
    int conflictC = 0;
    vec<Lit> learnt_clause;
    starts++;

    artificialSatLevel = -1; // reset the level before another search!

    for (;;) {
        CRef confl = propagate();
        if (confl != CRef_Undef) {
            // CONFLICT
            conflicts++;
            conflictC++;
            if (decisionLevel() == 0) return l_False;

            learnt_clause.clear();
            analyze(confl, learnt_clause, backtrack_level);
            cancelUntil(backtrack_level);

            if (learnt_clause.size() == 1) {
                uncheckedEnqueue(learnt_clause[0]);
            } else {
                CRef cr = ca.alloc(learnt_clause, true);
                learnts.push(cr);
                attachClause(cr);
                claBumpActivity(ca[cr]);
                uncheckedEnqueue(learnt_clause[0], cr);
            }

            varDecayActivity();
            claDecayActivity();

            if (--learntsize_adjust_cnt == 0) {
                learntsize_adjust_confl *= learntsize_adjust_inc;
                learntsize_adjust_cnt = (int)learntsize_adjust_confl;
                max_learnts *= learntsize_inc;

                if (verbosity >= 1)
                    printf("| %9d | %7d %8d %8d | %8d %8d %6.0f | %6.3f %% |\n", (int)conflicts,
                           (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]), nClauses(), (int)clauses_literals,
                           (int)max_learnts, nLearnts(), (double)learnts_literals / nLearnts(), progressEstimate() * 100);
            }

        } else {
            // NO CONFLICT
            if (nof_conflicts >= 0 && conflictC >= nof_conflicts || !withinBudget()) {
                // Reached bound on number of conflicts:
                progress_estimate = progressEstimate();
                if (!opt_keepSearch) // do not jump over the assumptions
                    cancelUntil(0);
                else {
                    cancelUntil(assumptions.size()); // if current level is lower, than the routine takes care!
                }
                return l_Undef;
            }

            // Simplify the set of problem clauses:
            if (decisionLevel() == 0 && !simplify()) return l_False;

            if (learnts.size() - nAssigns() >= max_learnts)
                // Reduce the set of learnt clauses:
                reduceDB();

            Lit next = lit_Undef;

            /* Norbert
             * for the imply check, always test the question literal, before using the next assumption! (not necessary, but should improve the average run time)
             */
            if (opt_imply_check && decisionLevel() < assumptions.size()) {
                assert(assumptions.size() > 0 && "this assertion must hold, because we entered the then-path");
                const Lit p = assumptions[assumptions.size() - 1]; // consider the questionable literal
                if (value(p) == l_False) {
                    // 		printf("assuming question %s%d failed at level %d\n", sign(p) ? "-" : "", var(p)+1, assumptions.size() - 1, decisionLevel() );
                    analyzeFinal(~p, conflict);
                    return l_False;
                }
            }


            while (decisionLevel() < assumptions.size()) {

                // Perform user provided assumption:
                Lit p = assumptions[decisionLevel()];

                /* Norbert
                 * ignore if an assumption is violated already, if it is not the very last assumption literal
                 * if the value of the assumption is false, but its not the very last assumption, act as the assumption is not in the list
                 */
                if ((value(p) == l_True)
#if 0
                  || (    opt_imply_check                            // but we have the option enabled to ignore the literal,
                       && decisionLevel() != assumptions.size() - 1  // if this literal is not the last assumption literal in the list
                       && value(p) == l_False                        // just check whether we have false here
		     )
#endif
                ) {
                    // Dummy decision level:
                    //                     printf("ignore assumption %s%d (assumption %d)\n", sign(p) ? "-" : "", var(p)+1, decisionLevel());
                    newDecisionLevel();
                } else if (value(p) == l_False) {
                    // 		    printf("assuming %s%d failed (assumption %d)\n", sign(p) ? "-" : "", var(p)+1, decisionLevel());
                    analyzeFinal(~p, conflict);
                    return l_False;
                } else {
                    next = p;
                    // 		    printf("assuming %s%d (at level %d)\n", sign(p) ? "-" : "", var(p)+1, decisionLevel());
                    break;
                }
            }

            if (next == lit_Undef) {
                // New variable decision:
                decisions++;

                if (generateClauseModels) {
                    next = pickClauseBranchLit(); // use a specialized decision heuristic, to be able to stop model enumeration much faster
                    if (next == lit_Undef) {
                        if (opt_eldbg) {
                            cerr << "c create an artificial model based on the generate clause models method -- set "
                                    "all variables positive, and not as decision"
                                 << endl;
                        }
                        if (opt_eldbg) cerr << "c found formula to be satisfied at level " << decisionLevel() << endl;
                        artificialSatLevel = decisionLevel();
                        for (Var v = 0; v < nVars(); ++v) { // create artificial model with extra decision levels
                            if (value(v) == l_Undef) {
                                newDecisionLevel();
                                uncheckedEnqueue(mkLit(v, false), CRef_Undef); // satisfy all variables
                            }
                        }
                        order_heap.clear(); // and remove all variables from the decision heap

                        if (generateClauseModels && opt_eldbg) {
                            cerr << "c [modelclause] return model " << trail << endl;
                        }
                        return l_True; // return to the calling method that we found a model
                    }
                } else
                    next = pickBranchLit();
                //
                //		if( next != lit_Undef ) cerr << "c decide " << next << "@" << decisionLevel() + 1 << endl;

                if (next == lit_Error) // enumerated all possible models based on the pickBlocks
                    return l_False;

                if (next == lit_Undef) {
                    // Model found:
                    if (generateClauseModels && opt_eldbg) {
                        cerr << "c [modelclause] return model " << trail << endl;
                    }
                    return l_True;
                }
            }

            // Increase decision level and enqueue 'next'
            newDecisionLevel();
            uncheckedEnqueue(next);
        }
    }
}


double Solver::progressEstimate() const
{
    double progress = 0;
    double F = 1.0 / nVars();

    for (int i = 0; i <= decisionLevel(); i++) {
        int beg = i == 0 ? 0 : trail_lim[i - 1];
        int end = i == decisionLevel() ? trail.size() : trail_lim[i];
        progress += pow(F, i) * (end - beg);
    }

    return progress / nVars();
}

/*
  Finite subsequences of the Luby-sequence:

  0: 1
  1: 1 1 2
  2: 1 1 2 1 1 2 4
  3: 1 1 2 1 1 2 4 1 1 2 1 1 2 4 8
  ...


 */

static double luby(double y, int x)
{

    // Find the finite subsequence that contains index 'x', and the
    // size of that subsequence:
    int size, seq;
    for (size = 1, seq = 0; size < x + 1; seq++, size = 2 * size + 1)
        ;

    while (size - 1 != x) {
        size = (size - 1) >> 1;
        seq--;
        x = x % size;
    }

    return pow(y, seq);
}


/* Norbert
 * modifications for model enumeration and implication checks
 */
Lit Solver::pickClauseBranchLit()
{
    int pickLevel = 0; // level of the block that is satisfied with the next decision

    if (opt_eldbg) cerr << "c PICK TRAIL: " << trail << endl;

    int satisfiedByOwnDecision = 0; // determine the actual comparison level, starts with 1

    while (pickLevel < pickedAlready.size()) {
        const vector<Lit> &block = pickBlocks[pickLevel]; // work with current block
        satisfiedByOwnDecision++;                         // next block satisfies itself at the next higher level

        if (opt_eldbg)
            cerr << "c check block " << block << " at level " << pickLevel << " with pick " << pickedAlready[pickLevel] << endl;
        // check whether this clause is already satisfied due to checks that have been performed before
        bool blockIsSat = false;
        for (int j = 0; j < block.size(); ++j) {
            if (value(block[j]) == l_True) {
                blockIsSat = true;
                break;
            }
        }
        if (blockIsSat) { // found satisfied block
            if (opt_eldbg) cerr << "c satisfied block at level " << pickLevel << " : " << block << endl;

            bool satisfiedBefore =
            false; // check whether this constraint is irrelevant in the current sub-tree, hence, ignore this constraint
            for (int i = 0; i < block.size(); ++i) {
                if (value(block[i]) == l_True && satisfiedByOwnDecision > level(var(block[i]))) {
                    satisfiedByOwnDecision--;
                    satisfiedBefore = true;
                    break;
                }
            }
            if (satisfiedBefore) { //
                int updateLevel = pickLevel + 1;
                if (pickedAlready[pickLevel] < block.size()) {
                    pickedAlready[pickLevel] =
                    block.size(); // indicate that this constraint wrt the current sub tree has been handled completely
                    for (; updateLevel < pickBlocks.size(); ++updateLevel) // for all blocks deeper in the tree, after backtracking
                        pickedAlready[updateLevel] = 0; // the first literal has to be considered again
                    satTreeFastForward++;               // count number of occurrences for this situation
                }
            } else {
                bool foundImpliedFalse = false; // check whether we can go fast forward in the tree
                for (; pickedAlready[pickLevel] < block.size();
                     pickedAlready[pickLevel]++) { // otherwise increase the counter of the current level
                    if (value(block[pickedAlready[pickLevel]]) != l_False // if the literal is not false
                        || level(var(block[pickedAlready[pickLevel]])) >
                           pickLevel // or is assigned at a higher level then the corresponding decision level
                    )
                        break; // found a literal that is still free
                    else {
                        foundImpliedFalse = true;
                        unsatTreeFastForward++; // count number of occurrences for this situation
                    }
                }
                if (foundImpliedFalse) {
                    int updateLevel = pickLevel + 1; // set all other literals back to 0 based on the above condition
                    for (; updateLevel < pickBlocks.size(); ++updateLevel) // for all blocks deeper in the tree, after backtracking
                        pickedAlready[updateLevel] = 0; // the first literal has to be considered again
                }
            }

            //#error check this here! moving forward should be ok ...
            //       pickedAlready[pickLevel] = block.size();   // memorize that this block is satisfied with the previous decisions
            ++pickLevel;
            continue; // consider next block
        }

        if (opt_eldbg)
            cerr << "c INITIAL to satisfy block: " << block << " with pick= " << pickedAlready[pickLevel] << endl;
        // look for a literal of the current block that can be satisfied
        for (; pickedAlready[pickLevel] < block.size(); pickedAlready[pickLevel]++) { // otherwise increase the counter of the current level
            if (value(block[pickedAlready[pickLevel]]) != l_False) break; // found a literal that is still free
        }
        if (opt_eldbg)
            cerr << "c AFTER SCAN to satisfy block: " << block << " with pick= " << pickedAlready[pickLevel] << endl;

        // reached a level where we can pick a literal to satisfy the clause
        if (pickedAlready[pickLevel] >= pickBlocks[pickLevel].size()) { // we already picked all literals of this clause, apply backtracking and set the picks for previous clauses
            // found all combinations of the current stack?
            if (pickLevel == 0) {
                if (opt_eldbg) cerr << "c exceeded all combinations" << endl;
                return lit_Error; // exceeded all combinations for the very first block, hence we are done!
            }

            // otherwise backtrack!
            int updateLevel = pickLevel - 1;
            while (updateLevel >= 0) { // modify pick for previous level (all necessary levels recursively)
                pickedAlready[updateLevel]++;
                if (pickedAlready[updateLevel] < pickBlocks[updateLevel].size())
                    break; // do not backtrack beyond, because there is another combination that has to be considered
                updateLevel--; // continue on previous level
            }
            for (; updateLevel < pickBlocks.size(); ++updateLevel) // for all blocks deeper in the tree, after backtracking
                pickedAlready[updateLevel] = 0;                    // the first literal has to be considered again
        }

        if (opt_eldbg)
            cerr << "c AFTER BACKTRACK to satisfy block: " << block << " with pick= " << pickedAlready[pickLevel] << endl;
        // after backtracking, perform the same check once more
        // look for a literal of the current block that can be satisfied
        for (; pickedAlready[pickLevel] < block.size(); pickedAlready[pickLevel]++) { // otherwise increase the counter of the current level
            if (value(block[pickedAlready[pickLevel]]) != l_False) break; // found a literal that is still free
        }
        if (opt_eldbg)
            cerr << "c AFTER SCAN2 to satisfy block: " << block << " with pick= " << pickedAlready[pickLevel] << endl;

        assert(pickedAlready[pickLevel] < block.size() && "the block can be satisfied");
        assert(value(block[pickedAlready[pickLevel]]) == l_Undef && "there has to be a free literal in this clause");

        if (opt_eldbg) { // print the path to the current model
            cerr << "c select " << block[pickedAlready[pickLevel]] << " : picked branch in decision tree: ";
            for (int i = 0; i <= pickLevel; ++i)
                cerr << " " << pickBlocks[i][pickedAlready[i]] << " ( " << pickedAlready[i] << "/" << pickBlocks[i].size() << " ) ";
            cerr << endl;
        }
        return block[pickedAlready[pickLevel]];
    }

    // satisfied all clauses in the stack
    if (pickLevel >= pickedAlready.size()) {
        if (opt_eldbg) { // print the path to the current model
            cerr << "c created another model" << endl;
            cerr << "c picked branch in decision tree: ";
            for (int i = 0; i < pickLevel; ++i)
                cerr << " " << pickBlocks[i][pickedAlready[i]] << " ( " << pickedAlready[i] << "/" << pickBlocks[i].size() << " ) ";
            cerr << endl;
        }
        return lit_Undef;
    }

    assert(false && "should never reach this part of the code");
    exit(3);
}

lbool Solver::integrateNewClause(vec<Lit> &clause, bool modelClause)
{
    if (opt_eldbg) cerr << "c [local] add clause " << clause << " at level " << decisionLevel() << endl;
    if (opt_eldbg) cerr << "c [local] ok: " << ok << " trail: " << trail << endl;

    if (clause.size() == 0) {
        ok = false;     // solver state is false
        return l_False; // adding the empty clause results in an unsatisfiable formula
    }

    // make sure we have enough variables
    Lit maxLit = clause[0];
    for (int i = 0; i < clause.size(); ++i) {
        maxLit = clause[i] < maxLit ? maxLit : clause[i];
    }
    while (nVars() < var(maxLit)) {
        const Var nv = newVar();
        //    cerr << "c [local] add " << nv + 1 << " to heap" << endl;
    }

    // analyze the current clause
    int satLits = 0, unsatLits = 0, undefLits = 0;

    for (int i = 0; i < clause.size(); ++i) {
        lbool truthvalue = value(clause[i]);
        if (truthvalue != l_False) {
            Lit tmp = clause[undefLits + satLits];
            clause[undefLits + satLits] = clause[i];
            clause[i] = tmp;
            undefLits = (truthvalue == l_Undef) ? undefLits + 1 : undefLits;
            satLits = (truthvalue == l_True) ? satLits + 1 : satLits;
        } else
            unsatLits++;
    }

    if (opt_eldbg)
        cerr << "c [local] sat: " << satLits << " unsat: " << unsatLits << " undefLits: " << undefLits << endl;

    // clause is not satisfied, and not "free" enough
    int backtrack_level = decisionLevel();
    int highestLevelVars = 0;
    if (undefLits + satLits < 2) {
        if (undefLits + satLits < 1) { // apply backtracking

            if (opt_eldbg) {
                cerr << "c [local] detailed2: ";
                for (int i = 0; i < clause.size(); ++i)
                    cerr << " " << clause[i] << "@" << level(var(clause[i])) << "t" << (value(clause[i]) == l_True)
                         << "f" << (value(clause[i]) == l_False);
                cerr << " " << endl;
            }
            int higehest_level = 0;
            backtrack_level = -1;
            for (int i = 0; i < clause.size(); ++i) {
                assert(value(clause[i]) == l_False && "all literals in the clause have to be unsatisfiable");
                assert(higehest_level > backtrack_level && "some literals have to be undefined after backtracking");
                if (level(var(clause[i])) > higehest_level) { // found new highest level in the clause
                    if (opt_eldbg)
                        cerr << "c " << clause[i] << " sets bt to " << backtrack_level << " and highest to "
                             << level(var(clause[i])) << endl;
                    backtrack_level = higehest_level;       // the other level is the new backtrack level
                    higehest_level = level(var(clause[i])); // store new highest level
                    Lit tmp = clause[0];
                    clause[0] = clause[i];
                    clause[i] = tmp;      // move highest level variable to front!
                    highestLevelVars = 1; // count variables for this level
                } else if (level(var(clause[i])) > backtrack_level) {
                    if (level(var(clause[i])) == higehest_level) { // found another variable of the highest level
                        if (opt_eldbg)
                            cerr << "c move literal " << clause[i] << "@" << level(var(clause[i])) << " to position "
                                 << highestLevelVars << endl;
                        Lit tmp = clause[highestLevelVars];
                        clause[highestLevelVars] = clause[i];
                        clause[i] = tmp;    // move highest level variable to front!
                        highestLevelVars++; // and count
                    } else {
                        if (opt_eldbg)
                            cerr << "c " << clause[i] << " updates bt from " << backtrack_level << " to "
                                 << level(var(clause[i])) << " highest: " << higehest_level << endl;
                        backtrack_level = level(var(clause[i]));
                    }
                }
            }
            for (int i = 1; i < clause.size(); ++i) { // move literal of backtrack level forward
                if (level(var(clause[i])) == backtrack_level) {
                    const Lit tmp = clause[i];
                    clause[i] = clause[1];
                    clause[1] = tmp; // move the literal forward
                    break;           // stop looking for more variables
                }
            }
        } else {
            assert(value(clause[0]) != l_False && "shuffling above moved only free literal to front");
            backtrack_level = 0;
            for (int i = 1; i < clause.size(); ++i) { // find actual backtrack level
                if (level(var(clause[i])) > backtrack_level) {
                    backtrack_level = level(var(clause[i])); // store level
                    Lit tmp = clause[1];
                    clause[1] = clause[i];
                    clause[i] = tmp; // move literal to front
                }
                assert(level(var(clause[1])) >= level(var(clause[i])) && "highest level on second position in clause");
            }
        }
    }

    // jump back (if necessary)
    if (backtrack_level == -1) { // cannot backtrack beyond level 0 -> clause cannot be added to the formula
        assert(value(clause[0]) == l_False && "clause is falsified");
        ok = false;
        return l_False;
    }

    if (opt_eldbg)
        cerr << "c [local] decisionLevel: " << decisionLevel() << " backtracklevel: " << backtrack_level << endl;

    cancelUntil(backtrack_level); // backtrack

    if (opt_eldbg) {
        cerr << "c [local] detailed2: ";
        for (int i = 0; i < clause.size(); ++i)
            cerr << " " << clause[i] << "@" << level(var(clause[i])) << "t" << (value(clause[i]) == l_True) << "f"
                 << (value(clause[i]) == l_False);
        cerr << " " << endl;
    }

    assert(value(clause[0]) != l_False && "first literal has to be free now");

    // add the clause to the local data structures
    CRef cr = CRef_Undef;    // for unit clauses
    if (clause.size() > 1) { // if clause is larger, add nicely to two-watched-literal structures
        cr = ca.alloc(clause, false);
        clauses.push(cr);
        attachClause(cr);

        if (opt_eldbg) cerr << "c new reason clause[ " << cr << " ]: " << ca[cr] << endl;

        if (modelClause) { // use this clause for model enumeration
            if (opt_eldbg) cerr << "c add a new model clause to the solver" << endl;
            pickedAlready.push(0); // did not see any of the literals of the current clause yet
            pickBlocks.push_back(vector<Lit>());
            pickBlocks[pickBlocks.size() - 1].resize(clause.size());
            for (int i = 0; i < clause.size(); ++i)
                pickBlocks[pickBlocks.size() - 1][i] =
                clause[i]; // satisfy one literal of the clause during specialized decision heuristic
            if (opt_subsumeBlocks)
                sort(pickBlocks[pickBlocks.size() - 1]); // sort the block, so that it becomes easier later to replace a block with a smaller one
            if (opt_eldbg)
                cerr << "c new decision block: (" << pickBlocks[pickBlocks.size() - 1].size() << ") "
                     << pickBlocks[pickBlocks.size() - 1] << endl;

            // check whether duplicate solutions have been found already
            if (opt_subsumeBlocks) {
                sort(pickBlocks[pickBlocks.size() - 1]); // sort the block, so that it becomes easier later to replace a block with a smaller one
                // check all blocks for being subsumed, replace the first subsumed block with the current block, delete all other subsumed blocks from the list
                int keptBlocks = 0;
                vector<Lit> &block = pickBlocks[pickBlocks.size() - 1]; // reference to current block
                bool isFirstSubsumed = true;                            // it did not yet subsume any block
                for (int i = 0; i < pickedAlready.size(); ++i) {        // check all other blocks
                    bool isSubsumed = false;
                    if (pickBlocks[i].size() > block.size()) { // is subsumed only, if its size is larger (never find the same block with the same size)

// TODO: check whether the small block subsumes the large block -- with merge routine
#warning TO BE IMPLEMENTED
                    }
                    if (isSubsumed) { // if the new block subsumes another block, hande the other block
                        if (isFirstSubsumed) {
                            // TODO replace the current block,
                            // update the picked-already structure
                            isFirstSubsumed = false;
                        }
                        // otherwise, simply drop this block ...
                    } else { // keep this block!
                        pickedAlready[keptBlocks] = pickedAlready[i];
                        pickBlocks[keptBlocks] = pickBlocks[i];
                        keptBlocks++;
                    }
                }
                pickedAlready.shrink(pickedAlready.size() - keptBlocks);
                pickBlocks.resize(keptBlocks);
            }
        }

    } else {
        assert(decisionLevel() == 0 && "unit can only be added at decision level 0");
    }

    if ((undefLits == 1 && satLits == 0)                             // clause was unit before backjumping already
        || (undefLits == 0 && satLits == 0 && highestLevelVars == 1) // or clause became unit after backjumping
    ) {
        if (opt_eldbg) cerr << "c [local] enqueue unit " << clause[0] << endl;
        assert((clause.size() == 1 || cr != CRef_Undef) && "always enqueue with a reason");
        uncheckedEnqueue(clause[0], cr); // then continue with unit propagation
        assert((clause.size() <= 1 || level(var(clause[0])) == level(var(clause[1]))) &&
               "always watch two literals of the same level (conflicting)");
    } else {
        if (clause.size() == 1)
            cerr << "c did not enqueue unit clause " << clause << " at level " << decisionLevel()
                 << " satisfied: " << (value(clause[0]) == l_True) << " falsified: " << (value(clause[0]) == l_False) << endl;
    }

    if (opt_eldbg) cerr << "c [local] succeeded at level " << decisionLevel() << endl;
    if (opt_eldbg) cerr << "c [local] trail " << trail << endl;

    return l_True;
}

lbool Solver::generateNextModel()
{
    // assert( false && "only accept models that falsify a literal of at least one clause? or that falsify a literal of each clause?" );

    if (opt_eldbg)
        cerr << "c [local] generate next model (empty: " << order_heap.empty() << ") vars: " << nVars() << endl;
    // current state is satisfiable
    vec<Lit> clause;
    vec<Lit> subModelClause;  // collect all literals that are currently negated
    if (order_heap.empty()) { // formula is currently satisfied. disallow current model, and generate next model
        if (opt_eldbg)
            cerr << "c use first "
                 << (generateClauseModels && artificialSatLevel != -1 ? artificialSatLevel : trail_lim.size())
                 << " decision levels for disallow-clause" << endl;
        for (int i = 0; i < (generateClauseModels && artificialSatLevel != -1 // if we create clause-models (tree based), then use the artificial level(if there was one)
                             ?
                             artificialSatLevel // use the artificial level
                             :
                             trail_lim.size()) // otherwise build a usual decision clause
             ;
             ++i) { // consider only the decision levels that are required for enumerating the tree
            clause.push(~trail[trail_lim[i]]);
        }

        if (opt_avoidSubModel) {
            for (Var v = 0; v < nVars(); ++v) {
                // #error check whether decision literals are enough
                if (value(v) == l_False)
                    subModelClause.push(mkLit(v)); // collect all literals that are currently mapped to false. one of them has to be satisfied in the next round!
            }
        }

        // if the solver generates models based on the specialized procedure, tell it to generate the next model
        if (generateClauseModels) {
            int updateLevel = pickedAlready.size() - 1;
            if (updateLevel >= 0) { // if there are already levels, backtrack to the next interpretation for the tree
                while (updateLevel >= 0) { // modify pick for previous level (all necessary levels recursively)
                    pickedAlready[updateLevel]++;
                    if (pickedAlready[updateLevel] < pickBlocks[updateLevel].size())
                        break; // do not backtrack beyond, because there is another combination that has to be considered
                    updateLevel--; // continue on previous level
                }
                for (updateLevel++; updateLevel < pickBlocks.size(); ++updateLevel) // for all blocks deeper in the tree, after backtracking
                    pickedAlready[updateLevel] = 0; // the first literal has to be considered again
            }
        }

        if (opt_eldbg) cerr << "c [local] generate model disallow clause " << clause << endl;
        if (l_False == integrateNewClause(clause)) { // add the new decision clause (should backtrack)
            return l_False;                          // tell that adding the next clause failed
        }

        if (opt_avoidSubModel) {
            if (opt_eldbg) cerr << "c [local] generate sub model disallow clause " << subModelClause << endl;
            if (l_False == integrateNewClause(subModelClause)) { // add the new decision clause (should backtrack)
                return l_False;                                  // tell that adding the next clause failed
            }
            cancelUntil(0);
        }
    }

    if (opt_eldbg) cerr << "c [local] ok: " << ok << " trail: " << trail << endl;
    if (opt_eldbg)
        cerr << "c [local] qhead: " << qhead << " |trail|: " << trail.size() << " nVars: " << nVars()
             << " level: " << decisionLevel() << endl;

    if (opt_eldbg) {
        cerr << "c [local] formula" << endl;
        for (int i = 0; i < clauses.size(); ++i) {
            cerr << "c [local clause] " << ca[clauses[i]] << endl;
        }
        for (int i = 0; i < learnts.size(); ++i) {
            cerr << "c [local learnt] " << ca[learnts[i]] << endl;
        }
    }

    // search for the next model with an infinite budget
    lbool ret = search(INT32_MAX);
    assert(ret != l_Undef && "search without budget");
    if (opt_eldbg) cerr << "c [local] ret == l_True: " << (ret == l_True) << " |trail|: " << trail.size() << endl;
    // cerr << "c return answer after " << conflicts << " conflicts and " << decisions << " decisions" << endl;
    return ret;
}


void Solver::removeIrrelevantClauses(vec<Lit> &assumps, const Lit questionLit, vec<Lit> *removedClauses)
{
    assert(decisionLevel() == 0 && "perform only before search");

    if (opt_reduceLits) {
        cerr << "c cannot reduce based on literals yet ... use fallback with variables" << endl;
    }

    // clear all watch lists
    watches.cleanAll();
    for (int v = 0; v < nVars(); v++)
        for (int s = 0; s < 2; s++) watches[mkLit(v, s)].clear();

    // add all clauses to all watch lists (as all watch scheme)
    int keptClauses = 0;
    for (int i = 0; i < clauses.size(); ++i) { // add a clause C = [a,b,c] to the watch lists a, b and c (not the complement!)
        const Clause &c = ca[clauses[i]];
        if (c.mark()) { // delete the ignored clause

        } else {
            for (int j = 0; j < c.size(); ++j) watches[c[j]].push(Watcher(clauses[i], c[j]));
            clauses[keptClauses++] = clauses[i]; // keep the clause
        }
    }
    clauses.shrink(clauses.size() - keptClauses); // remove ignored clauses

    // use a queue that consists of a seen-vector, and a vector with a head-index
    int seenOldSize = seen.size();
    seen.growTo(2 * nVars(), 0); // storage for each literal
    vec<Lit> queue;
    int head = queue.size();
    queue.push(questionLit);
    seen[toInt(opt_reduceLits ? ~questionLit : mkLit(var(questionLit), false))] = 1; // do not add this literal again

    // perform depth first search from clauses starting with variable questionLit, additionally mark clauses if already
    // seen or use literals and then do not mark clauses, but take polarity into account

    while (head < queue.size()) {                 // there are still elements to be processed
        const Lit currentLiteral = queue[head++]; // dequeue next element

        // analyze all clauses that contain this literal
        for (int iteration = 0; iteration < (opt_reduceLits ? 1 : 2); iteration++) { // process both watch lists, if only variables are handled
            const Lit next = iteration == 0 ? currentLiteral : ~currentLiteral; // if variables are processed, process both polarities!
            for (int i = 0; i < watches[next].size(); ++i) {
                Clause &c = ca[watches[next][i].cref];
                if (!opt_reduceLits) { // if we consider only variables, its sufficient to check each clause once
                    if (c.mark() != 0)
                        continue; // skip clauses that have been seen already
                    else
                        c.mark(1); // otherwise, we can mark the clause for being skipped next time
                }

                for (int j = 0; j < c.size(); ++j) { // analyze all variables of the clause
                    if (var(c[j]) == var(next))
                        continue; // do not add the comlement literal of a given variable with the same clause
                    const Lit cl = opt_reduceLits ? ~c[j] : mkLit(var(c[i]), false); // use the literal that has to be considered next
                    if (!seen[toInt(cl)]) {                                          // have not seen this literal yet
                        seen[toInt(cl)] = 1;                                         // do not add this literal again
                        queue.push(cl);                                              // add the literal to the queue
                    }
                }
            }
        }
    }

    cerr << "c found " << queue.size() << " relevant literals in the formula out of " << nVars() << endl;

    // remove all assumption literals that are not marked
    int keptAssumptions = 0;
    for (int i = 0; i < assumps.size(); ++i) {
        const Lit al = opt_reduceLits ? al : mkLit(var(al), false); // the asssumption is not negated for the implication (as literals in clauses are)
        if (seen[toInt(al)]) assumps[keptAssumptions++] = assumps[i];
    }
    cerr << "c removed " << assumps.size() - keptAssumptions << " assumptions out of " << assumps.size() << endl;
    assumps.shrink(assumps.size() - keptAssumptions);

    // clean watch lists after "misusing" them, and before using them properly again
    for (int v = 0; v < nVars(); v++)
        for (int s = 0; s < 2; s++) watches[mkLit(v, s)].clear();
    // remove all clauses that do not contain marked variables or marked complements
    // if necessary, add them to the vector in the parameter
    keptClauses = 0;
    for (int i = 0; i < clauses.size(); ++i) {
        Clause &c = ca[clauses[i]];
        c.mark(1); // mark the clause as redundant, and check whether it's not
        for (int j = 0; j < c.size(); ++j) {
            const Lit &l = c[j];
            if (seen[toInt(l)] || seen[toInt(~l)]) { // some literal is marked (or its complement)
                c.mark(0);
                break;
            }
        }

        if (c.mark() == 0) {
            attachClause(clauses[i]);
            clauses[keptClauses++] = clauses[i];
        } else if (removedClauses != 0) {
            for (int j = 0; j < c.size(); ++j) // add the clause to the list of removed clauses
                removedClauses->push(c[j]);
            removedClauses->push(lit_Undef); // separate the literals of clauses by a "lit_Undef" literal
            ca.free(clauses[i]);             // tell the garbage collector that we removed the clause
        }
    }
    cerr << "c removed " << clauses.size() - keptClauses << " irrelevant clauses" << endl;
    clauses.shrink(clauses.size() - keptClauses); // remove the clauses that are not useful

    // clean seen vector, independently of used option clean both
    for (int i = 0; i < queue.size(); ++i) {
        seen[toInt(queue[i])] = 0;
        seen[toInt(~queue[i])] = 0;
    }
    seen.shrink(nVars()); // reduce half of the variables again
    assert(seen.size() == nVars() && "have the same space as before");
}


bool Solver::minimizeCurrentConflict(const Lit questionLit)
{
    const int oldConflictSize = conflict.size();
    necessary.clear();                    // remove previously stored data
    necessary.growTo(nVars(), 0);         // initialize for all variables with 0
    assumptions.moveTo(assumptionBackup); // backup current set of assumptions

    conflict.moveTo(assumptions);
    for (int i = 0; i < assumptions.size(); ++i) { // automatically reversed :)
        if (assumptions[i] != ~questionLit) {
            assumptions[i] = ~assumptions[i]; // negate all literals
        } else {                              // remove the questionlit literal from the initial assumption vector again
            assumptions[i] = ~assumptions.last(); // move last literal forward, and negate it
            assumptions.shrink(1);                // remove the duplicate
        }
    }

    int keepLits = 0;
    cancelUntil(0); // have to start from scratch
    while (keepLits < assumptions.size()) {
        if (necessary[var(assumptions[keepLits])]) {
            keepLits++;
            continue;
        } // jump over literals that are necessary

        Lit toCheck = assumptions[keepLits];        // literal to be checked
        assumptions[keepLits] = assumptions.last(); // move last literal forward
        assumptions.last() = questionLit;           // add question lit as last literal
        assert(decisionLevel() == 0 && "can do intermediate calls only at level 0");
        lbool ret = solveLimited_(); // check whether this subset results in an error
        cancelUntil(0);              // have to start from scratch
        minimalChecks++;             // stats

        if (ret == l_True) { // literal is necessary (could do model rotation here, but since we have group MUS, its assumed to be inefficient
            necessary[var(toCheck)] = 1;                // memorize
            assumptions.last() = assumptions[keepLits]; // restore assumptions vector
            assumptions[keepLits] = toCheck;            // and add necessary literal back
        } else {                                        // literal is not necessary
            minimizations++;

            conflict.moveTo(assumptions); // move new conflict vector to assumptions vector
            for (int i = 0; i < assumptions.size(); ++i) {
                if (assumptions[i] != ~questionLit) {
                    assumptions[i] = ~assumptions[i]; // negate all literals
                } else { // remove the questionlit literal from the initial assumption vector again
                    assumptions[i] = ~assumptions.last(); // move last literal forward, and negate it
                    assumptions.shrink(1);                // remove the duplicate
                }
            }
            keepLits = 0; // start scan from the beginning, but necessary literals are restored
        }
    }

    assumptions.moveTo(conflict);                                         // move final assumptions back
    for (int i = 0; i < conflict.size(); ++i) conflict[i] = ~conflict[i]; // negate all literals
    assumptionBackup.moveTo(assumptions);                                 // restore previous assumptions vector

    return conflict.size() < oldConflictSize; // return whether the conflict has been minimized
}

lbool Solver::findImplications(vec<Lit> &assumps, Lit questionLit, int rotate)
{
    // TODO: use global variables and timers for statistics
    int checks = 0, localchecks = 0, unsatchecks = 0;
    uint64_t savedLevels = 0;

    double findTime = cpuTime();

    assumps.copyTo(assumptions);

    // reduce the formual and set of assumptions
    vec<Lit> removdClauses; // storage for all clauses that have been removed due to being irrelevant
    if (opt_reduce > 0) {   // reduce the formula (delete clauses that are irrelevant)
        removeIrrelevantClauses(assumptions, questionLit, (opt_reduce > 1 ? &removdClauses : 0));
    }

    // have a first call with the full set (check for any subset)
    assumptions.push(questionLit);
    // if( opt_eldbg ) cerr << "c solve with assumptions " << assumptions << endl;

    SATSolver *externalSolver = 0;
#ifdef HAVE_IPASIR
    if (opt_optext) {
        externalSolver = new SATSolver(); // use this, if IPASIR should be used
        assert(decisionLevel() == 0 && "no search should have happened so far");
        vec<Lit> c;
        for (int i = 0; i < trail.size(); ++i) {
            c.clear();
            c.push(trail[i]);
            externalSolver->addClause(c);
        }
        for (int i = 0; i < clauses.size(); ++i) {
            c.clear();
            const Clause &cl = ca[clauses[i]];
            c.growTo(cl.size());
            for (int j = 0; j < cl.size(); ++j) {
                c[j] = cl[j];
            }
            if (opt_sort) sort(c); // try to make run repeatable
            externalSolver->addClause(c);
        }
    }
#endif

    lbool ret;

    if (opt_eldbg) cerr << "test assumptions: " << assumptions << std::endl;
    if (externalSolver) {
#ifdef HAVE_IPASIR
        if (opt_sort) {
            assumptions.copyTo(sortedAssumptions);
            sort(assumptions);
        }
#endif
        int ipasirRet = externalSolver->solve(assumptions, model, conflict);
        ret = ipasirRet == 10 ? l_True : l_False;
        if (opt_eldbg) std::cerr << "ipasirRet: " << ipasirRet << std::endl;
#ifdef HAVE_IPASIR
        if (opt_sort) {
            //       std::cerr << "sort conflict, unsort assumptions" << std::endl;
            sortedAssumptions.copyTo(assumptions);
            sort(conflict);
        }
#endif
    } else
        ret = solveLimited_();

    assumptions.shrink_(1);
    checks++;

    // there is no conflicting subset of assumptions that violates the questionLit
    if (ret == l_True) {
        std::cerr << "no conflicting subset" << std::endl;
        return l_True;
    }
    assert(ret != l_Undef && "the solution should not be aborted due to some other reason");

    int oldVerbosity = verbosity;
    verbosity = 0; // disable statistics output

    Solver *localSolver = new Solver();            // generate solver that maintains the formula G
    if (opt_eldbg) localSolver->localDebug = true; // enable debug for local solver

    if (opt_modelClause) // tell the local solver to enumerate models according to a specialized scheme
        localSolver->generateClauseModels = true;

    vec<int> assumpsPositions;
    assumpsPositions.growTo(nVars(), 0); // have a mapping for each variable (even though not all variables might be present
    int originalAssumptions = assumptions.size(); // store number of initial assumption literals
    vec<Lit> violatingAssumptions;                // set of literals that already appeared in conflicts
    vec<Var> varToLocalVar; // map from outer variables to inner variables (so that the inner solver has only as many variables as required)
    varToLocalVar.growTo(nVars(), var_Undef); // indicate the variable in the inner solver, have a mapping for each variable of the formula

    // have a vector with the positions of the literals in assumptions, store the positions
    for (int i = 0; i < assumptions.size(); ++i) {
        assumpsPositions[var(assumptions[i])] = i; // variable assumptions[i] is at position i
    }

    int foundAnswers = 0;
    vec<char> assumptionInViolatingSet;
    assumptionInViolatingSet.growTo(nVars(), 0);
    int usedAssumptions = 0;

    // enumerate all interesting solutions
    do {

        if (ret == l_False) { // display violating set, remove quesiton literal from conflict, rewrite conflict clause, add conflict to localsolver
            unsatchecks++;

            if (!externalSolver) {
                if (opt_minimalOnly) {
                    if (opt_eldbg) cerr << "c minimize conflicting clause: " << conflict << endl;
                    minimizeCurrentConflict(questionLit);
                }
            }

            // check number of
            for (int i = 0; i < conflict.size(); ++i) {
                if (conflict[i] != ~questionLit) { // remove the question literal from the conflict, do not display the literal
                    if (assumptionInViolatingSet[var(conflict[i])] == 0) {
                        ++usedAssumptions;
                        assumptionInViolatingSet[var(conflict[i])] = 1;
                    }
                }
            }

            if (opt_eldbg) cerr << "c actual conflicting clause: " << conflict << endl;
            foundAnswers++;
            if (foundAnswers == 1)
                printf("              [#,CPUsec,MB,totallyUsedAssumptions,totalCalls]: variables in the sat\n");
            printf("violating set [%d,%.3lf,%.2f,%lf,%d]: ", foundAnswers, cpuTime() - findTime, memUsedPeak(),
                   (double)usedAssumptions / (double)assumptions.size(), localchecks);
            for (int i = 0; i < conflict.size(); ++i) {
                if (conflict[i] == ~questionLit) { // remove the question literal from the conflict, do not display the literal
                    conflict[i] = conflict[conflict.size() - 1]; // move last literal forward
                    conflict.shrink(1);
                    --i;
                    continue;
                }
                printf("%s%d ", sign(conflict[i]) ? "" : "-", var(conflict[i]) + 1); // print complement of the next literal
            }
            printf("0\n");

            // remove conflicting variables from assumption vector
            for (int i = 0; i < conflict.size(); ++i) {
                if (opt_eldbg) cerr << "c process " << i << "/" << conflict.size() << endl;
                const Var v = var(conflict[i]);
                int minLevel = decisionLevel();          // get minimal literal to calculate the backtracking point
                if (assumpsPositions[v] != -1) {         // variable has not been moved to conflicting sets before
                    const int pos = assumpsPositions[v]; // use temporary position variable
                    minLevel = minLevel <= level(v) ? minLevel : level(v);  // store minimum level
                    assumptions[pos] = assumptions[assumptions.size() - 1]; // move other variable forward
                    assumpsPositions[var(assumptions[pos])] = pos;          // update position of the moved literal
                    assumpsPositions[v] = -1; // invalidate variable v, actually removing it from the structure
                    violatingAssumptions.push(~conflict[i]); // add literal to the other set
                    assumptions.shrink(1);                   // remove the last literal, which has been moved forwards
                }

                if (!externalSolver) {
                    if (opt_keepSearch && minLevel > 0) {
                        cancelUntil(minLevel - 1); // remove the level of the smallest assumption
                    }
                }

                // rewrite the conflict clause with respect to the variable map
                if (varToLocalVar[v] == var_Undef) {
                    if (opt_eldbg) cerr << "c variable without mapping " << v + 1 << endl;
                    varToLocalVar[v] = localSolver->newVar(); // assign the new variable
                    if (opt_eldbg)
                        cerr << "c variable without mapping " << v + 1 << " maps to " << varToLocalVar[v] + 1 << endl;
                    // 	  cerr << "c add " << varToLocalVar[v] + 1 << " to the heap" << endl;
                    //  localSolver->order_heap.insert( varToLocalVar[v] );  // and tell the local solver that there is another new variable for being decided
                }
                if (opt_eldbg)
                    cerr << "c rewrite " << conflict[i] << " into " << mkLit(varToLocalVar[v], sign(conflict[i])) << endl;
                conflict[i] = mkLit(varToLocalVar[v], sign(conflict[i])); // store the according variable
            }
            if (opt_eldbg)
                cerr << "c original: " << originalAssumptions << " current: " << assumptions.size()
                     << " localVars: " << localSolver->nVars() << endl;
            if (opt_eldbg) cerr << "c rewritten conflict clause: " << conflict << endl;
            assert(originalAssumptions == assumptions.size() + localSolver->nVars() &&
                   "variables should not disappear or be created");

            // add the rewriten clause
            if (l_False == localSolver->integrateNewClause(conflict, opt_modelClause)) // tell the local solver to forget about the current violating set -- use this set of literals for model enumeration
                break; // in case of failure, there are no more models to be generated by that solver
        }

        // get next local model
        ret = localSolver->generateNextModel();
        localchecks++;
        if (ret == l_False)
            break; // there is no more model in the local solver, so we generated all possible models for the variables that are known to the local solver

        // add extra assumptions to solver // TODO can be done faster if the solver does not backtrack to level 0 in the solve_ method!
        const int preCallAssumptoinSize = assumptions.size();
        if (!externalSolver) {
            if (opt_keepSearch && assumptions.size() > 0) { // jump back as far as necessary
                cancelUntil(level(var(assumptions[assumptions.size() - 1])));
            }
        }


        // add the assumptions that vary (due to model generation) // TODO: improvement would be to order the actual assumption vector to maximize the backjump level (to not backjump too far)
        int minAssumptionLevel = decisionLevel();
        for (int i = 0; i < violatingAssumptions.size(); ++i) {
            const Lit outerLit = violatingAssumptions[i];
            const Lit localLit = mkLit(varToLocalVar[var(outerLit)], sign(outerLit)); // translate to local variable names
            assumptions.push((localSolver->value(localLit) == l_True) ? outerLit : ~outerLit); // add literal according to sign in local solver
            if (value(outerLit) != l_Undef)
                minAssumptionLevel = minAssumptionLevel < level(var(outerLit)) ? minAssumptionLevel : level(var(outerLit)); // select level to backjump to
        }

        if (!externalSolver) {
            if (opt_keepSearch)
                cancelUntil(minAssumptionLevel > 1 ? minAssumptionLevel - 1 : 0);
            else
                assert(decisionLevel() == 0 && "if no time-saving is used, decision level has to be 0");
            savedLevels += (uint64_t)decisionLevel();
        }

        assumptions.push(questionLit); // add questionlit again
        assert(value(questionLit) == l_Undef && "question literal should not have a truth value already");
        /*
        cerr << "c solve with assumptions " << assumptions << endl;
        cerr << "c solve with trail       " << assumptions << endl;*/

        // cerr << "test assumptions: " << assumptions << std::endl;
        // use the assumptions implicitely
        if (!externalSolver)
            ret = solveLimited_(); // analyze the current set of assumptions // TODO: can be done faster if backtracking for restarts takes the assumptions into account
        else {
#ifdef HAVE_IPASIR
            if (opt_sort) {
                assumptions.copyTo(sortedAssumptions);
                sort(assumptions);
            }
#endif
            ret = externalSolver->solve(assumptions, model, conflict) == 10 ? l_True : l_False;
#ifdef HAVE_IPASIR
            if (opt_sort) {
                //         std::cerr << "sort conflict, unsort assumptions" << std::endl;
                sortedAssumptions.copyTo(assumptions);
                sort(conflict);
            }
#endif
        }
        // cerr << "search returned conflict: " << conflict << endl;

        //     checks ++;                                                // stats
        assumptions.shrink(assumptions.size() - preCallAssumptoinSize); // remove the extra variables again
        if (checks > opt_max_calls) {
            cerr << "Warning: interupt due to too many calls" << endl;
            break;
        }

    } while (true && !asynch_interrupt);

    printf("local fast forward: sat: %d unsat: %d \n", localSolver->satTreeFastForward, localSolver->unsatTreeFastForward);
    delete localSolver;

    printf("found violating sets: %d\n", foundAnswers);
    printf("outer calls: %d (unsat: %d), inner calls: %d\n", checks, unsatchecks, localchecks);
    printf("saved levels: %lld\n", savedLevels);
    printf("minimization calls: %d, successful: %d, backjumps: %d\n", minimalChecks, minimizations, minimizationBackjump);

    verbosity = oldVerbosity;

    cancelUntil(0); // make sure we clean up the solver!
    assert(decisionLevel() == 0 &&
           "after processing all literals, decision level should be set to 0 before returning to caller");
    // add the missing clauses back
    if (removdClauses.size() != 0) {
        vec<Lit> clause;
        int readdedClauses = 0;
        for (int i = 0; i < removdClauses.size(); ++i) {
            if (removdClauses[i] != lit_Undef)
                clause.push(removdClauses[i]);
            else {
                addClause_(clause);
                clause.clear();
                readdedClauses++;
            }
        }
        cerr << "c added " << readdedClauses << " back" << endl;
    }

    return l_False;
}

void Solver::toGroupMUS(const char *file, const vec<Lit> &assumps, const Lit questionLit)
{
    int gcnfvariables = nVars();
    int gcnfclauses = 0;
    assert(decisionLevel() == 0 && "print formula only on level 0");
    gcnfclauses += trail.size() + 1;         // all unit clauses, and the unit clause for the question literal
    for (int i = 0; i < clauses.size(); ++i) // count all active clauses
        gcnfclauses = ca[clauses[i]].mark() == 0 ? gcnfclauses + 1 : gcnfclauses;

    gcnfclauses += assumps.size(); // add all the unit clauses for all the groups

    // print the actual file
    FILE *fd = fopen(file, "wr");
    if (fd == NULL) fprintf(stderr, "could not open file %s\n", file), exit(1);

    if (!ok) { // unsat
        fprintf(fd, "p gcnf 0 1 0\n0\n");
        fprintf(fd, "0\n"); // print the empty clause!
        return;
    }

    // print header
    fprintf(fd, "p gcnf %i %i %i\n", gcnfvariables, gcnfclauses, assumps.size());

    // print question lit
    {
        stringstream s;
        s << "{0} " << questionLit << " 0" << endl;
        fprintf(fd, "%s", s.str().c_str());
    }

    // print trail
    for (int i = 0; i < trail.size(); ++i) {
        stringstream s;
        s << "{0} " << trail[i] << " 0" << endl;
        fprintf(fd, "%s", s.str().c_str());
    }
    // print clauses for group 0
    for (int i = 0; i < clauses.size(); ++i) {
        Clause &c = ca[clauses[i]];
        if (c.mark()) continue;
        stringstream s;
        s << "{0} ";
        for (int i = 0; i < c.size(); ++i) s << c[i] << " ";
        s << "0" << endl;
        fprintf(fd, "%s", s.str().c_str());
    }

    // print all the other groups
    for (int i = 0; i < assumps.size(); ++i) {
        stringstream s;
        s << "{" << 1 + i << "} " << assumps[i] << " 0" << endl;
        fprintf(fd, "%s", s.str().c_str());
    }

    fclose(fd);
}

// NOTE: assumptions passed in member-variable 'assumptions'.
lbool Solver::solve_()
{
    model.clear();
    conflict.clear();
    if (!ok) return l_False;

    solves++;

    max_learnts = nClauses() * learntsize_factor;
    learntsize_adjust_confl = learntsize_adjust_start_confl;
    learntsize_adjust_cnt = (int)learntsize_adjust_confl;
    lbool status = l_Undef;

    if (verbosity >= 1) {
        printf("============================[ Search Statistics ]==============================\n");
        printf("| Conflicts |          ORIGINAL         |          LEARNT          | Progress |\n");
        printf("|           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |\n");
        printf("===============================================================================\n");
    }

    // Search:
    int curr_restarts = 0;
    while (status == l_Undef) {
        double rest_base = luby_restart ? luby(restart_inc, curr_restarts) : pow(restart_inc, curr_restarts);
        status = search(rest_base * restart_first);
        if (!withinBudget()) break;
        curr_restarts++;
    }

    if (verbosity >= 1) printf("===============================================================================\n");


    if (status == l_True) {
        // Extend & copy model:
        model.growTo(nVars());
        for (int i = 0; i < nVars(); i++) model[i] = value(i);
    } else if (status == l_False && conflict.size() == 0)
        ok = false;

    if (!opt_keepSearch) // jump only back, if we do not use the imply check
        cancelUntil(0);

    return status;
}

//=================================================================================================
// Writing CNF to DIMACS:
//
// FIXME: this needs to be rewritten completely.

static Var mapVar(Var x, vec<Var> &map, Var &max)
{
    if (map.size() <= x || map[x] == -1) {
        map.growTo(x + 1, -1);
        map[x] = max++;
    }
    return map[x];
}


void Solver::toDimacs(FILE *f, Clause &c, vec<Var> &map, Var &max)
{
    if (satisfied(c)) return;

    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) != l_False) fprintf(f, "%s%d ", sign(c[i]) ? "-" : "", mapVar(var(c[i]), map, max) + 1);
    fprintf(f, "0\n");
}


void Solver::toDimacs(const char *file, const vec<Lit> &assumps)
{
    FILE *f = fopen(file, "wr");
    if (f == NULL) fprintf(stderr, "could not open file %s\n", file), exit(1);
    toDimacs(f, assumps);
    fclose(f);
}


void Solver::toDimacs(FILE *f, const vec<Lit> &assumps)
{
    // Handle case when solver is in contradictory state:
    if (!ok) {
        fprintf(f, "p cnf 1 2\n1 0\n-1 0\n");
        return;
    }

    vec<Var> map;
    Var max = 0;

    // Cannot use removeClauses here because it is not safe
    // to deallocate them at this point. Could be improved.
    int cnt = 0;
    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]])) cnt++;

    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]])) {
            Clause &c = ca[clauses[i]];
            for (int j = 0; j < c.size(); j++)
                if (value(c[j]) != l_False) mapVar(var(c[j]), map, max);
        }

    // Assumptions are added as unit clauses:
    cnt += assumptions.size();

    fprintf(f, "p cnf %d %d\n", max, cnt);

    for (int i = 0; i < assumptions.size(); i++) {
        assert(value(assumptions[i]) != l_False);
        fprintf(f, "%s%d 0\n", sign(assumptions[i]) ? "-" : "", mapVar(var(assumptions[i]), map, max) + 1);
    }

    for (int i = 0; i < clauses.size(); i++) toDimacs(f, ca[clauses[i]], map, max);

    if (verbosity > 0) printf("Wrote %d clauses with %d variables.\n", cnt, max);
}


//=================================================================================================
// Garbage Collection methods:

void Solver::relocAll(ClauseAllocator &to)
{
    // All watchers:
    //
    // for (int i = 0; i < watches.size(); i++)
    watches.cleanAll();
    for (int v = 0; v < nVars(); v++)
        for (int s = 0; s < 2; s++) {
            Lit p = mkLit(v, s);
            // printf(" >>> RELOCING: %s%d\n", sign(p)?"-":"", var(p)+1);
            vec<Watcher> &ws = watches[p];
            for (int j = 0; j < ws.size(); j++) ca.reloc(ws[j].cref, to);
        }

    // All reasons:
    //
    for (int i = 0; i < trail.size(); i++) {
        Var v = var(trail[i]);

        if (reason(v) != CRef_Undef && (ca[reason(v)].reloced() || locked(ca[reason(v)])))
            ca.reloc(vardata[v].reason, to);
    }

    // All learnt:
    //
    for (int i = 0; i < learnts.size(); i++) ca.reloc(learnts[i], to);

    // All original:
    //
    for (int i = 0; i < clauses.size(); i++) ca.reloc(clauses[i], to);
}


void Solver::garbageCollect()
{
    // Initialize the next region to a size corresponding to the estimated utilization degree. This
    // is not precise but should avoid some unnecessary reallocations for the new region:
    ClauseAllocator to(ca.size() - ca.wasted());

    relocAll(to);
    if (verbosity >= 2)
        printf("|  Garbage collection:   %12d bytes => %12d bytes             |\n",
               ca.size() * ClauseAllocator::Unit_Size, to.size() * ClauseAllocator::Unit_Size);
    to.moveTo(ca);
}
