import re

# This files is mostly boring string parsing stuff, except that parse_term handles implicit rules
# and splits conditional mutual informations into basic entropies.

def parse_variable_set(var_set):
    return frozenset(x.strip() for x in var_set.split(","))

# Returns a list of implicit functional dependencies, represented as pairs (world, X, Y) for rules
# world: X <- Y.
def parse_implicit_rules(input_file):
    implicit_rules = []
    with open(input_file, 'r') as f:
        for line in f.readlines():
            line = line.strip()
            if line[-9:] == " implicit":
                worlds, line = line[:-9].split(":")
                func_outputs, func_inputs = line.split("<-")
                func_inputs = parse_variable_set(func_inputs)
                func_outputs = parse_variable_set(func_outputs)
                for world in worlds.split(","):
                    implicit_rules.append((world.strip(), func_outputs, func_inputs))
    return implicit_rules

# Apply implicit functional dependencies to add to a set of random variables all variables that are
# completely determined by them, according to the implicit rules.
def apply_implicit_rules(implicit_rules, world, random_vars):
    random_vars = set(random_vars)

    changed = True
    while changed:
        changed = False
        for (rule_world, func_outputs, func_inputs) in implicit_rules:
            if world == rule_world and func_inputs <= random_vars and not func_outputs <= random_vars:
                random_vars |= func_outputs
                changed = True

    return frozenset(random_vars)

# Possibly outputs multiple terms, as it breaks down conditional mutual informations into their
# component entropies.
def parse_term(term, coeff, implicit_rules):
    term = term.strip()
    terms = []

    if term[0] in "HI": # An entropy or conditional mutual information
        world, args = term[1:-1].split("(")
        world = world.strip()
        if term[0] == "I":
            # CMI terms in the proof should only appear in the form CMI >= 0, as Citip as converted
            # all user provided bounds to basic entropies anyway.
            assert coeff >= 0.0

        # A conditional entropy, mutual information, or conditional mutual information.
        if "|" in args:
            args, conditions = args.split("|")
            conditions = parse_variable_set(conditions)
        else:
            conditions = frozenset()

        if ";" in args:
            left, right = args.split(";")
            left = parse_variable_set(left)
            right = parse_variable_set(right)
        else:
            left = parse_variable_set(args)
            right = None

        # Write the conditional mutual information as a linear combination of up to 4 entropies.
        if len(conditions) > 0:
            terms.append((-coeff, world, conditions))
        terms.append((coeff, world, apply_implicit_rules(implicit_rules, world, left | conditions)))
        if right != None:
            terms.append((coeff, world, apply_implicit_rules(implicit_rules, world, right | conditions)))
            terms.append((-coeff, world, apply_implicit_rules(implicit_rules, world, left | right | conditions)))

    else: # A formal eps variable
        terms.append((coeff, None, term))

    return terms

def parse_lhs(lhs, implicit_rules):
    lhs = lhs.strip()
    terms = []
    while lhs != "":
        # Get the leading coefficient's sign.
        if lhs[0] in "-+":
            leading_sign = 1 if lhs[0] == "+" else -1
            lhs = lhs[1:].strip()
        else:
            leading_sign = 1

        # Get the leading coefficient.
        if lhs[0].isdigit():
            coeff, lhs = lhs.split(" ", maxsplit=1)
            coeff = leading_sign * float(coeff)
        else:
            coeff = leading_sign

        # The term ends at the next + or -, or at the end of the string.
        term_end_search = re.search(r'[+-]', lhs)
        if term_end_search != None:
            term_end = term_end_search.start()
        else:
            term_end = len(lhs)
        term = lhs[:term_end]
        lhs = lhs[term_end:].strip()

        terms += parse_term(term, coeff, implicit_rules)

    return terms

# Parses the proof, returning (target, steps). Steps is a list, with each of the form (is_equality,
# terms, rhs). terms is a list of pairs (coeff, world, term), where term is either a set of random
# variables or a string naming a formal variable. rhs is just a constant number Target has the form
# (terms, rhs), and is the bound that is supposed to be proven.
def parse_proof(input_file, proof_file):
    implicit_rules = parse_implicit_rules(input_file)
    #print(implicit_rules)

    steps = []
    with open(proof_file, 'r') as f:
        for line in f.readlines():
            line = line.strip()
            if line == "":
                continue

            if line[:3] == "=> ":
                # Target bound
                line = line[3:]
                lhs, rhs = line.split(">=")
                rhs = float(rhs)
                target = (parse_lhs(lhs, implicit_rules), rhs)
                return target, steps

            is_equality = ("==" in line)
            if is_equality:
                lhs, rhs = line.split("==")
            else:
                lhs, rhs = line.split(">=")
            rhs = float(rhs)

            steps.append((is_equality, parse_lhs(lhs, implicit_rules), rhs))
