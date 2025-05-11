import time
import threading

def parse_dimacs_cnf(file_path):
    clauses = []
    with open(file_path, 'r') as f:
        for line in f:
            line = line.strip()
            if line == '' or line.startswith('c') or line.startswith('p'):
                continue
            literals = [int(x) for x in line.split() if x != '0']
            if literals:
                clauses.append(frozenset(literals))  # Changed to frozenset
    return clauses

# ---------------- DPLL ----------------
def dpll(clauses, assignment=frozenset()):
    clauses = set(clauses)
    clauses, assignment = unit_propagate_dpll(clauses, assignment)
    if clauses is None:
        return False, None
    if not clauses:
        return True, assignment
    clauses, assignment = eliminate_pure_literals_dpll(clauses, assignment)
    if not clauses:
        return True, assignment
    literal = choose_literal(clauses)

    for val in [literal, -literal]:
        new_clauses = simplify_dpll(clauses, val)
        if new_clauses is not None:
            sat, new_assignment = dpll(new_clauses, assignment | {val})
            if sat:
                return True, new_assignment
    return False, None

def choose_literal(clauses):
    smallest_clause = min(clauses, key=len)
    return next(iter(smallest_clause))

def simplify_dpll(clauses, literal):
    new_clauses = set()
    for clause in clauses:
        if literal in clause:
            continue
        if -literal in clause:
            new_clause = frozenset(clause - {-literal})  # Changed to frozenset
            if not new_clause:
                return None
            new_clauses.add(new_clause)
        else:
            new_clauses.add(clause)
    return new_clauses

def unit_propagate_dpll(clauses, assignment):
    clauses = set(clauses)
    unit_clauses = {next(iter(c)) for c in clauses if len(c) == 1}
    while unit_clauses:
        literal = unit_clauses.pop()
        assignment |= {literal}
        new_clauses = set()
        for clause in clauses:
            if literal in clause:
                continue
            if -literal in clause:
                new_clause = frozenset(clause - {-literal})  # Changed to frozenset
                if not new_clause:
                    return None, None
                new_clauses.add(new_clause)
            else:
                new_clauses.add(clause)
        clauses = new_clauses
        unit_clauses |= {next(iter(c)) for c in clauses if len(c) == 1}
    return clauses, assignment

def eliminate_pure_literals_dpll(clauses, assignment):
    literal_counts = {}
    for clause in clauses:
        for literal in clause:
            literal_counts[literal] = literal_counts.get(literal, 0) + 1
    pure_literals = {lit for lit in literal_counts if -lit not in literal_counts}
    assignment |= pure_literals
    new_clauses = {clause for clause in clauses if not any(lit in pure_literals for lit in clause)}
    return new_clauses, assignment

# ---------------- DP ----------------
def dp_algorithm(clauses):
    clauses = set(frozenset(c) for c in clauses)
    resolved_pairs = set()

    while True:
        clauses = unit_propagate_dp(clauses)
        if clauses is None:
            return False
        if not clauses:
            return True

        clauses = eliminate_pure_literals_dp(clauses)
        if not clauses:
            return True

        some_clause = min(clauses, key=len)
        literal = next(iter(some_clause))

        pos_clauses = {c for c in clauses if literal in c}
        neg_clauses = {c for c in clauses if -literal in c}
        others = {c for c in clauses if literal not in c and -literal not in c}

        resolvents = set()
        for ci in pos_clauses:
            for cj in neg_clauses:
                pair_id = tuple(sorted([id(ci), id(cj)]))
                if pair_id in resolved_pairs:
                    continue
                resolved_pairs.add(pair_id)
                resolvent = resolve_dp(ci, cj, literal)
                if resolvent is None:
                    continue
                if not resolvent:
                    return False
                resolvents.add(resolvent)

        if not resolvents:
            return True
        clauses = others.union(resolvents)

def unit_propagate_dp(clauses):
    unit_clauses = {next(iter(c)) for c in clauses if len(c) == 1}
    while unit_clauses:
        literal = unit_clauses.pop()
        new_clauses = set()
        for clause in clauses:
            if literal in clause:
                continue
            if -literal in clause:
                new_clause = frozenset(clause - {-literal})  # Changed to frozenset
                if not new_clause:
                    return None
                new_clauses.add(new_clause)
            else:
                new_clauses.add(clause)
        clauses = new_clauses
        unit_clauses |= {next(iter(c)) for c in clauses if len(c) == 1}
    return clauses

def eliminate_pure_literals_dp(clauses):
    counter = {}
    for clause in clauses:
        for literal in clause:
            counter[literal] = counter.get(literal, 0) + 1
    pure = {lit for lit in counter if -lit not in counter}
    return {clause for clause in clauses if not any(lit in pure for lit in clause)}

def resolve_dp(ci, cj, literal):
    resolvent = (ci - {literal}) | (cj - {-literal})
    if any(lit in resolvent and -lit in resolvent for lit in resolvent):
        return None
    return frozenset(resolvent)

# ---------------- Resolution ----------------
def resolution_algorithm(clauses):
    clauses = set(frozenset(clause) for clause in clauses)
    new = set()
    processed_pairs = set()

    while True:
        for ci in clauses:
            for cj in clauses:
                if ci == cj:
                    continue
                pair = tuple(sorted([ci, cj], key=id))
                if pair in processed_pairs:
                    continue
                processed_pairs.add(pair)

                resolvents = resolve_resolution(ci, cj)
                if frozenset() in resolvents:
                    return False
                new |= resolvents

        if new.issubset(clauses):
            return True

        clauses |= new

def resolve_resolution(ci, cj):
    resolvents = set()
    for literal in ci:
        if -literal in cj:
            resolvent = (ci - {literal}) | (cj - {-literal})
            resolvents.add(frozenset(resolvent))
    return resolvents

# ---------------- Framework ----------------
def run_with_timeout(func, args=(), timeout_duration=10):
    result = [None]
    completed = [False]

    def target():
        result[0] = func(*args)
        completed[0] = True

    thread = threading.Thread(target=target)
    thread.daemon = True
    thread.start()
    thread.join(timeout_duration)

    if not completed[0]:
        return "TIMED OUT", None
    return "COMPLETED", result[0]

def solve_with_timeout(algo_name, formula, timeout=60):
    if algo_name == "dpll":
        status, result = run_with_timeout(lambda: dpll(formula), timeout_duration=timeout)
        if status == "COMPLETED":
            return "SATISFIABLE" if result[0] else "UNSATISFIABLE", result[1]
        return status, None
    elif algo_name == "dp":
        status, result = run_with_timeout(lambda: dp_algorithm(formula), timeout_duration=timeout)
        return ("SATISFIABLE" if result else "UNSATISFIABLE") if status == "COMPLETED" else status, None
    elif algo_name == "resolution":
        status, result = run_with_timeout(lambda: resolution_algorithm(formula), timeout_duration=timeout)
        return ("SATISFIABLE" if result else "UNSATISFIABLE") if status == "COMPLETED" else status, None
    else:
        return "Unknown algorithm", None

def main():
    print("SAT Solver Console")
    print("Choose algorithm: dpll / dp / resolution")
    algo = input("Algorithm: ").strip().lower()

    if algo not in {"dpll", "dp", "resolution"}:
        print("Invalid algorithm choice.")
        return

    file_number = input("Enter test case number (1-5): ").strip()
    try:
        num = int(file_number)
        file_path = f"example{num}.cnf"
        formula = parse_dimacs_cnf(file_path)
    except Exception as e:
        print(f"Failed to load file: {e}")
        return

    start_time = time.time()
    result_status, assignment = solve_with_timeout(algo, formula)
    end_time = time.time()

    print("Result:", result_status)
    print(f"Execution Time: {end_time - start_time:.4f} seconds")


if __name__ == "__main__":
    main()
