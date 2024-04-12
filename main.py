import itertools as it
import hwtypes as ht
from hwtypes import smt_utils as fc
import pysmt.shortcuts as smt
import pysmt.logics as logics
import typing as tp

_cache = {}
#bvlen = 0 means that the variable is a Bit, otherwise it is a BitVector
def new_var(s, bvlen):
    if (s, bvlen) in _cache:
        if _cache[s][1] != bvlen:
            raise ValueError(f"Variable {s} has conflicting lengths")
        return _cache[s][0]
    if bvlen==0:
        v = ht.SMTBit(name=s)
    else:
        v = ht.SMTBitVector[bvlen](name=s)
    _cache[s] = (v, bvlen)
    return v

def get_model(query, solver_name='z3', logic=None):
    vars = query.get_free_variables()
    model = smt.get_model(smt.And(query), solver_name=solver_name, logic=logic)
    if model:
        return {v: int(model.get_value(v).constant_value()) for v in vars}
    return False

def is_constant(var: ht.SMTBit):
    return var.value.is_constant()

def to_constant(var):
    if is_constant(var):
        return int(var.value.constant_value())

def all_smt(formula, keys=None, solver_name='z3'):
    vars = formula.get_free_variables()
    if keys is None:
        keys = vars
    with smt.Solver(solver_name, logic=logics.QF_BV) as solver:
        solver.add_assertion(formula)
        while solver.solve():
            yield {k: int(solver.get_value(k).constant_value()) for k in vars}
            partial_model = [smt.EqualsOrIff(k, solver.get_value(k)) for k in keys]
            solver.add_assertion(smt.Not(smt.And(partial_model)))


#This finds solution to the following puzzle: Given a list of integers, the goal is to reverse the list.
# The only allowed operations are:
#   (0) Take one integer and split it into two strictly smaller integers summing to the original integer.
#   (1) Take two integers and combine them into one integer by adding them.
#  The list is reversed when the first element is the largest and the last element is the smallest.
#  You can never make a move resulting in the same integer appearing in the list more than once
#  You can never make an integer greater than the largest integer in the init_list

def find_sol(init : tp.List[int], num_steps: int, max_list_len: int, is_nat: bool = True):

    assert num_steps > 0
    assert max_list_len > len(init)

    max_int = max(init)

    bvlen_val = (2*max_int+1).bit_length()
    BV_val = ht.SMTBitVector[bvlen_val]

    bvlen_list = max_list_len.bit_length()
    BV_list = ht.SMTBitVector[bvlen_list]


    #--------------------
    #Delcare Variables
    #--------------------

    #Represents the puzzle state: states[num_steps][list_index]
    states = [
        [new_var(f"s_{i}_{s}", bvlen_val) for i in range(max_list_len)] for s in range(num_steps + 1)
    ]
    #Represents the length of the list at each step
    lens = [new_var(f"l_{s}", bvlen_list) for s in range(num_steps + 1)]

    # Operation decisions
    ops = [new_var(f"a_{s}", 1) for s in range(num_steps)]

    # Operation index
    # if (0) then the list is split at op_idxs[s]
    # if (1) then the list is combined at op_idxs[s] and op_idxs[s] + 1
    op_idxs = [new_var(f"op_{s}", bvlen_list) for s in range(num_steps)]

    #Use ops and op idxs for keys
    keys = ops + op_idxs
    keys = [k.value for k in keys]

    def pretty_print(model):
        for s in range(num_steps + 1):
            len_s = model[lens[s].value]
            #prints the state of the list  up to len
            print([model[states[s][i].value] for i in range(len_s)])
            #print(f"op and index: {model[ops[s].value]} {model[op_idxs[s].value]}")
        print()


    #--------------------
    #Constraints
    #--------------------

    # All values are less than max_int
    cons_max_int = [states[s][i] <= max_int for s in range(num_steps + 1) for i in range(max_list_len)]

    # Initial state
    cons_init = []
    for i, v in enumerate(init):
        cons_init.append(states[0][i] == v)

    # Length of the list at the start
    cons_init.append(lens[0] == len(init))

    # Final State
    cons_final = []
    for i, v in enumerate(init[::-1]):
        cons_final.append(states[num_steps][i] == v)

    # Length of the list at the end
    cons_final.append(lens[num_steps] == len(init))

    # Each length is at most max_list_len
    cons_len = [lens[s] <= max_list_len for s in range(num_steps + 1)]

    # Each value is unique in the list
    cons_unique = []
    for s in range(num_steps + 1):
        cur_len = lens[s]
        for i, j in it.combinations(range(max_list_len), 2):
            vi = states[s][i]
            vj = states[s][j]
            valid = (i < cur_len) & (j < cur_len)
            cons_unique.append(fc.Implies(valid, vi != vj))

    cons_nat = []
    if is_nat:
        for s in range(num_steps + 1):
            for i in range(max_list_len):
                cons_nat.append(states[s][i] >= 0)

    # Operation index is less than the length of the list
    cons_op_idx = [op_idxs[s] < lens[s] for s in range(num_steps)]

    # Split (0) forces length to increase by 1
    cons_split_len = []
    for s in range(num_steps):
        cons_split_len.append(fc.Implies(ops[s] == 0, lens[s + 1] == lens[s] + 1))

    # Combine (1) forces length to decrease by 1
    cons_combine_len = []
    for s in range(num_steps):
        cons_combine_len.append(fc.Implies(ops[s] == 1, lens[s + 1] == lens[s] - 1))

    # Combine (1) forces op index to be less than length - 1
    cons_combine_idx = []
    for s in range(num_steps):
        cons_combine_idx.append(fc.Implies(ops[s] == 1, op_idxs[s] < lens[s] - 1))

    #Consructing the next state transition function

    #Constraint assuming operation is split and the list is split at op_idxs[s]
    #  Example: [3, 5, 7] -> [3, 1, 4, 7]
    #   This means that before the split cur state and next state vals are the same
    #   In split, the value at states[s] is split into two values
    #   And after split, the values are the same
    cons_split = []
    for s in range(num_steps):
        cons_split_s = []
        for i in range(max_list_len-1):
            before_split = BV_list(i) < op_idxs[s]
            is_split = op_idxs[s] == i
            after_split = (BV_list(i) > op_idxs[s]) & (BV_list(i) < lens[s])
            cons_split_s.append(fc.Implies(before_split, states[s][i] == states[s + 1][i]))
            cons_split_s.append(fc.Implies(is_split, states[s][i] == states[s + 1][i] + states[s + 1][i + 1]))
            cons_split_s.append(fc.Implies(after_split, states[s][i] == states[s + 1][i + 1]))
        cons_split.append(fc.Implies(ops[s] == 0, fc.And(cons_split_s)))

    #Constraint assuming operation is combine and the list is combined at op_idxs[s] and op_idxs[s] + 1
    # Example: [3, 1, 4, 7] -> [3, 5, 7]
    #   This means that before the combine cur state vals are the same
    #   In combine, the values at states[s] and states[s] + 1 are combined
    #   After combine, the values are the same
    cons_combine = []
    for s in range(num_steps):
        cons_combine_s = []
        for i in range(max_list_len-1):
            before_combine = BV_list(i) < op_idxs[s]
            is_combine = op_idxs[s] == i
            after_combine = (BV_list(i) > op_idxs[s]) & (BV_list(i) < lens[s])
            cons_combine_s.append(fc.Implies(before_combine, states[s][i] == states[s + 1][i]))
            cons_combine_s.append(fc.Implies(is_combine, states[s][i] + states[s][i + 1] == states[s + 1][i]))
            cons_combine_s.append(fc.Implies(after_combine, states[s+1][i] == states[s][i + 1]))
        cons_combine.append(fc.Implies(ops[s] == 1, fc.And(cons_combine_s)))

    query = fc.And([
        fc.And(cons_max_int),
        fc.And(cons_init),
        fc.And(cons_final),
        fc.And(cons_len),
        fc.And(cons_unique),
        fc.And(cons_nat),
        fc.And(cons_op_idx),
        fc.And(cons_split_len),
        fc.And(cons_combine_len),
        fc.And(cons_combine_idx),
        fc.And(cons_split),
        fc.And(cons_combine),
    ]).to_hwtypes()

    for model in all_smt(query.value, keys):
        pretty_print(model)
        print()

find_sol([7, 5, 3], num_steps=6, max_list_len=6, is_nat=True)