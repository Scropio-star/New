MAX_CONSTANTS = 10

# Helper sets
PROP_VARS = {'p', 'q', 'r', 's'}
FOL_VARS = {'x', 'y', 'z', 'w'}
PREDICATES = {'P', 'Q', 'R', 'S'}
CONNECTIVES = {'&', '\/', '->'}


def _reset_universal_flags(branch):
    to_remove = []
    for formula in branch['expanded']:
        if parse(formula) == 3 or (formula.startswith('~E') and parse(formula[2:])):
            to_remove.append(formula)
    for formula in to_remove:
        branch['expanded'].discard(formula)

# Internal helper to find the main connective position in a binary formula
# Assumes the formula starts with '(' and ends with ')'
def _find_main_connective(fmla):
    depth = 0
    i = 0
    while i < len(fmla):
        ch = fmla[i]
        if ch == '(':
            depth += 1
            i += 1
            continue
        if ch == ')':
            depth -= 1
            i += 1
            continue
        if depth == 1:
            if ch == '&':
                return i
            if ch == '\\':
                if i + 1 < len(fmla) and fmla[i + 1] == '/':
                    return i
            if ch == '-' and i + 1 < len(fmla) and fmla[i + 1] == '>':
                return i
        i += 1
    return -1


def _is_prop_atom(fmla):
    return fmla in PROP_VARS


def _is_fol_atom(fmla):
    if len(fmla) < 5:
        return False
    if fmla[0] not in PREDICATES or fmla[1] != '(' or fmla[-1] != ')':
        return False
    comma_pos = fmla.find(',', 2)
    if comma_pos == -1 or comma_pos == len(fmla) - 2:
        return False
    left = fmla[2:comma_pos]
    right = fmla[comma_pos + 1:-1]
    if not left or not right:
        return False
    if not left.isalnum() or not right.isalnum():
        return False
    if len(left) == 1 and left not in FOL_VARS and not left.startswith('c'):
        return False
    if len(right) == 1 and right not in FOL_VARS and not right.startswith('c'):
        return False
    return True


def _parse_prop(fmla):
    if _is_prop_atom(fmla):
        return 6
    if fmla.startswith('~'):
        inner = _parse_prop(fmla[1:])
        if inner:
            return 7
        return 0
    if fmla.startswith('(') and fmla.endswith(')'):
        pos = _find_main_connective(fmla)
        if pos == -1:
            return 0
        left = fmla[1:pos]
        conn = con(fmla)
        right = fmla[pos + len(conn): -1]
        left_t = _parse_prop(left)
        right_t = _parse_prop(right)
        if left_t and right_t:
            return 8
    return 0


def _parse_fol(fmla):
    if _is_fol_atom(fmla):
        return 1
    if fmla.startswith('~'):
        inner = _parse_fol(fmla[1:])
        if inner:
            return 2
        return 0
    if fmla.startswith('A') or fmla.startswith('E'):
        if len(fmla) < 2:
            return 0
        var = fmla[1]
        if var not in FOL_VARS:
            return 0
        sub = _parse_fol(fmla[2:])
        if sub:
            if fmla[0] == 'A':
                return 3
            return 4
        return 0
    if fmla.startswith('(') and fmla.endswith(')'):
        pos = _find_main_connective(fmla)
        if pos == -1:
            return 0
        left = fmla[1:pos]
        conn = con(fmla)
        right = fmla[pos + len(conn): -1]
        left_t = _parse_fol(left)
        right_t = _parse_fol(right)
        if left_t and right_t:
            return 5
    return 0


# Parse a formula, consult parseOutputs for return values.
def parse(fmla):
    prop_result = _parse_prop(fmla)
    if prop_result:
        return prop_result
    fol_result = _parse_fol(fmla)
    if fol_result:
        return fol_result
    return 0


# Return the LHS of a binary connective formula
def lhs(fmla):
    if not (fmla.startswith('(') and fmla.endswith(')')):
        return ''
    pos = _find_main_connective(fmla)
    if pos == -1:
        return ''
    return fmla[1:pos]


# Return the connective symbol of a binary connective formula
def con(fmla):
    pos = _find_main_connective(fmla)
    if pos == -1:
        return ''
    if fmla[pos] == '&':
        return '&'
    if fmla[pos] == '\\' and pos + 1 < len(fmla) and fmla[pos + 1] == '/':
        return '\/'
    if fmla[pos] == '-' and pos + 1 < len(fmla) and fmla[pos + 1] == '>':
        return '->'
    return ''


# Return the RHS symbol of a binary connective formula
def rhs(fmla):
    connection = con(fmla)
    if not connection:
        return ''
    pos = _find_main_connective(fmla)
    return fmla[pos + len(connection):-1]


def theory(fmla):  # initialise a theory with a single formula in it
    return {
        'formulas': [fmla],
        'constants': [],
        'new_constants': 0,
        'expanded': set(),
        'universal_history': {}
    }


def _is_literal(fmla):
    if parse(fmla) in (1, 6):
        return True
    if fmla.startswith('~'):
        inner = fmla[1:]
        if parse(inner) in (1, 6):
            return True
    return False


def _closed(branch):
    seen = set(branch['formulas'])
    for f in branch['formulas']:
        if f.startswith('~'):
            if f[1:] in seen:
                return True
        else:
            if '~' + f in seen:
                return True
    return False


def _fresh_constant(branch):
    idx = branch['new_constants'] + 1
    name = 'c' + str(idx)
    while name in branch['constants']:
        idx += 1
        name = 'c' + str(idx)
    return name


def _substitute(fmla, var, const):
    kind = parse(fmla)
    if kind in (6,):
        return fmla
    if kind == 1:
        comma_pos = fmla.find(',', 2)
        left_arg = fmla[2:comma_pos]
        right_arg = fmla[comma_pos + 1:-1]
        if left_arg == var:
            left_arg = const
        if right_arg == var:
            right_arg = const
        return fmla[0] + '(' + left_arg + ',' + right_arg + ')'
    if fmla.startswith('~'):
        return '~' + _substitute(fmla[1:], var, const)
    if fmla.startswith('A') or fmla.startswith('E'):
        bound = fmla[1]
        body = fmla[2:]
        if bound == var:
            return fmla[0] + bound + body
        return fmla[0] + bound + _substitute(body, var, const)
    if fmla.startswith('(') and fmla.endswith(')'):
        left = lhs(fmla)
        right = rhs(fmla)
        connector = con(fmla)
        return '(' + _substitute(left, var, const) + connector + _substitute(right, var, const) + ')'
    return fmla


def _expand_universal(fmla, branch, queue):
    var = fmla[1]
    body = fmla[2:]
    used = branch['universal_history'].setdefault(fmla, set())
    added = False
    if not branch['constants']:
        if branch['new_constants'] >= MAX_CONSTANTS:
            return False, True
        const = _fresh_constant(branch)
        branch['constants'].append(const)
        branch['new_constants'] += 1
        _reset_universal_flags(branch)
    for const in branch['constants']:
        if const in used:
            continue
        inst = _substitute(body, var, const)
        queue.append(inst)
        used.add(const)
        added = True
    return added, False


def _expand_existential(fmla, branch, queue):
    var = fmla[1]
    body = fmla[2:]
    if branch['new_constants'] >= MAX_CONSTANTS:
        return False, True
    const = _fresh_constant(branch)
    branch['constants'].append(const)
    branch['new_constants'] += 1
    _reset_universal_flags(branch)
    inst = _substitute(body, var, const)
    queue.append(inst)
    return True, False


def sat(tableau):
    branch_clear = False
    undetermined = False
    while tableau:
        branch = tableau.pop()
        if _closed(branch):
            continue
        progressed = True
        while progressed:
            progressed = False
            if _closed(branch):
                break
            new_formulas = []
            for f in branch['formulas']:
                if f in branch['expanded']:
                    continue
                if _is_literal(f):
                    branch['expanded'].add(f)
                    continue
                kind = parse(f)
                if f.startswith('~~'):
                    branch['expanded'].add(f)
                    branch['formulas'].append(f[2:])
                    progressed = True
                    break
                if f.startswith('~'):
                    inner = f[1:]
                    inner_kind = parse(inner)
                    if inner_kind in (5, 8):
                        l = lhs(inner)
                        c = con(inner)
                        r = rhs(inner)
                        branch['expanded'].add(f)
                        if c == '&':
                            left_branch = {
                                'formulas': list(branch['formulas']),
                                'constants': list(branch['constants']),
                                'new_constants': branch['new_constants'],
                                'expanded': set(branch['expanded']),
                                'universal_history': {k: set(v) for k, v in branch['universal_history'].items()}
                            }
                            right_branch = {
                                'formulas': list(branch['formulas']),
                                'constants': list(branch['constants']),
                                'new_constants': branch['new_constants'],
                                'expanded': set(branch['expanded']),
                                'universal_history': {k: set(v) for k, v in branch['universal_history'].items()}
                            }
                            left_branch['formulas'].append('~' + l)
                            right_branch['formulas'].append('~' + r)
                            tableau.append(left_branch)
                            tableau.append(right_branch)
                            progressed = True
                            break
                        if c == '\/' or c == '->':
                            new_formulas.extend(['~' + l, '~' + r] if c == '\/' else [l, '~' + r])
                            progressed = True
                            break
                    if f.startswith('~A') and parse(f[1:]) == 3:
                        transformed = 'E' + f[2] + '~' + f[3:]
                        branch['expanded'].add(f)
                        branch['formulas'].append(transformed)
                        progressed = True
                        break
                    if f.startswith('~E') and parse(f[1:]) == 4:
                        transformed = 'A' + f[2] + '~' + f[3:]
                        branch['expanded'].add(f)
                        branch['formulas'].append(transformed)
                        progressed = True
                        break
                if kind == 3:  # universal
                    added, limited = _expand_universal(f, branch, new_formulas)
                    if limited:
                        undetermined = True
                        branch['expanded'].add(f)
                        continue
                    if added:
                        progressed = True
                        break
                    branch['expanded'].add(f)
                    continue
                if kind == 4:  # existential
                    added, limited = _expand_existential(f, branch, new_formulas)
                    branch['expanded'].add(f)
                    if limited:
                        undetermined = True
                        continue
                    progressed = True
                    break
                if kind in (5, 8):
                    left = lhs(f)
                    connector = con(f)
                    right = rhs(f)
                    branch['expanded'].add(f)
                    if connector == '&':
                        new_formulas.extend([left, right])
                        progressed = True
                        break
                    if connector == '\/' or connector == '->':
                        left_branch = {
                            'formulas': list(branch['formulas']),
                            'constants': list(branch['constants']),
                            'new_constants': branch['new_constants'],
                            'expanded': set(branch['expanded']),
                            'universal_history': {k: set(v) for k, v in branch['universal_history'].items()}
                        }
                        right_branch = {
                            'formulas': list(branch['formulas']),
                            'constants': list(branch['constants']),
                            'new_constants': branch['new_constants'],
                            'expanded': set(branch['expanded']),
                            'universal_history': {k: set(v) for k, v in branch['universal_history'].items()}
                        }
                        if connector == '\/' :
                            left_branch['formulas'].append(left)
                            right_branch['formulas'].append(right)
                        else:
                            left_branch['formulas'].append('~' + left)
                            right_branch['formulas'].append(right)
                        tableau.append(left_branch)
                        tableau.append(right_branch)
                        progressed = True
                        break
                if kind == 7:
                    inner = f[1:]
                    if parse(inner) == 6:
                        branch['expanded'].add(f)
                        continue
                    branch['expanded'].add(f)
            branch['formulas'].extend(new_formulas)
        if not _closed(branch):
            if all(_is_literal(f) or f in branch['expanded'] for f in branch['formulas']):
                branch_clear = True
                break
    if branch_clear:
        return 1
    if undetermined:
        return 2
    return 0

#------------------------------------------------------------------------------------------------------------------------------:
#                                            DO NOT MODIFY THE CODE BELOW THIS LINE!                                           :
#------------------------------------------------------------------------------------------------------------------------------:

lines = []
try:
    while True:
        lines.append(input())
except EOFError:
    pass

parseOutputs = ['not a formula',
                'an atom',
                'a negation of a first order logic formula',
                'a universally quantified formula',
                'an existentially quantified formula',
                'a binary connective first order formula',
                'a proposition',
                'a negation of a propositional formula',
                'a binary connective propositional formula']

satOutput = ['is not satisfiable', 'is satisfiable', 'may or may not be satisfiable']



if not lines:
    firstline = ''
else:
    firstline = lines[0]

PARSE = False
if 'PARSE' in firstline:
    PARSE = True

SAT = False
if 'SAT' in firstline:
    SAT = True

for line in lines[1:]:
    if line[-1] == '\n':
        line = line[:-1]
    parsed = parse(line)

    if PARSE:
        output = "%s is %s." % (line, parseOutputs[parsed])
        if parsed in [5,8]:
            output += " Its left hand side is %s, its connective is %s, and its right hand side is %s." % (lhs(line), con(line),rhs(line))
        print(output)

    if SAT:
        if parsed:
            tableau = [theory(line)]
            print('%s %s.' % (line, satOutput[sat(tableau)]))
        else:
            print('%s is not a formula.' % line)
