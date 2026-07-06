"""
This program computes "linear combinatory closures" of some simple
equations. It is based on the following rule for turning a lambda
term (with a free variable x) into a term built only from the
combinators B, C, I:

    lambda*x. x     = i
    lambda*x. (p q) = c (lambda*x. p) q      if x occurs free in p
    lambda*x. (p q) = b p (lambda*x. q)      if x occurs free in q

We represent a term either as:
  - a single letter, like "x" or "b" (a plain Python string), or
  - an application of two terms, written as the tuple:
        ("APP", left_term, right_term)

For example, the term "b x y" (meaning ((b x) y)) is represented as:
    ("APP", ("APP", "b", "x"), "y")
"""

# The letters we treat as variables (things we can abstract over).
VARIABLES = {"x", "y", "z"}

# The letters we treat as constants (the combinators themselves).
CONSTANTS = {"b", "c", "i"}


# ----------------------------------------------------------------------
# Step 1: turn a string like "c(bx)y" into our tuple representation
# ----------------------------------------------------------------------

def parse(text):
    """
    Parse a string such as "c(c(bbx)y)z" into a term made of tuples.
    Application is left-associative and written by just writing terms
    next to each other. Parentheses can be used to group things.
    """
    text = text.replace(" ", "")   # ignore spaces, just in case
    position = [0]                # a mutable "cursor" into the string

    def peek():
        # Look at the current character without consuming it.
        if position[0] < len(text):
            return text[position[0]]
        return None

    def parse_one_symbol():
        # Parse either a single letter, or a parenthesized sub-expression.
        char = peek()
        if char == "(":
            position[0] += 1                 # skip "("
            inner_term = parse_application()
            # the next character must be ")"
            position[0] += 1                 # skip ")"
            return inner_term
        else:
            position[0] += 1                 # consume the letter
            return char

    def parse_application():
        # Parse a sequence of symbols applied to each other, left to right.
        term = parse_one_symbol()
        while peek() is not None and peek() != ")":
            next_term = parse_one_symbol()
            term = ("APP", term, next_term)
        return term

    return parse_application()


# ----------------------------------------------------------------------
# Step 2: find which variables occur free in a term
# ----------------------------------------------------------------------

def free_variables(term):
    """Return the set of variables that occur in this term."""
    if isinstance(term, str):
        # It's a single letter: a variable or a constant.
        if term in VARIABLES:
            return {term}
        else:
            return set()
    else:
        # It's an application ("APP", left, right).
        _, left, right = term
        return free_variables(left) | free_variables(right)


# ----------------------------------------------------------------------
# Step 3: the lambda* operator itself
# ----------------------------------------------------------------------

def lambda_star(variable, term):
    """
    Compute lambda*(variable). term, following the three rules:

        lambda*x. x     = i
        lambda*x. (p q) = c (lambda*x. p) q      if x is free in p
        lambda*x. (p q) = b p (lambda*x. q)      if x is free in q
    """
    # Case 1: the term is just the variable itself.
    if term == variable:
        return "i"

    # Case 2: the term is an application (p q).
    _, p, q = term
    p_has_variable = variable in free_variables(p)
    q_has_variable = variable in free_variables(q)

    if p_has_variable:
        # lambda*x.(p q) = c (lambda*x. p) q
        new_p = lambda_star(variable, p)
        return ("APP", ("APP", "c", new_p), q)

    if q_has_variable:
        # lambda*x.(p q) = b p (lambda*x. q)
        new_q = lambda_star(variable, q)
        return ("APP", ("APP", "b", p), new_q)

    # If we get here, the variable was not free in the term at all.
    raise ValueError(f"{variable} is not free in this term")


# ----------------------------------------------------------------------
# Step 4: print a term back out as a readable string
# ----------------------------------------------------------------------

def term_to_string(term):
    """Turn our tuple representation back into a compact string."""
    if isinstance(term, str):
        return term

    _, left, right = term
    left_text = term_to_string(left)
    right_text = term_to_string(right)

    # Only add parentheses around the right side if it is itself
    # an application (this keeps the output as short as possible).
    if not isinstance(right, str):
        right_text = "(" + right_text + ")"

    return left_text + right_text


# ----------------------------------------------------------------------
# Step 5: close an equation over all of its free variables
# ----------------------------------------------------------------------

def variables_in_order_of_appearance(term):
    """
    Return the free variables of a term, in the order they first
    appear when reading the term from left to right.
    """
    order = []

    def visit(sub_term):
        if isinstance(sub_term, str):
            if sub_term in VARIABLES and sub_term not in order:
                order.append(sub_term)
        else:
            _, left, right = sub_term
            visit(left)
            visit(right)

    visit(term)
    return order


def close_equation(left_text, right_text):
    """
    Given both sides of an equation as strings, close it by applying
    lambda* for every free variable, and print the result.

    We abstract the variables in reverse order of first appearance,
    so that if the variables appear as x, y, z, the result reads as
        lambda*x (lambda*y (lambda*z (equation)))
    exactly like a normal nested lambda x. lambda y. lambda z. ...
    """
    left_term = parse(left_text)
    right_term = parse(right_text)

    variables = variables_in_order_of_appearance(left_term)
    # Also pick up any variable that only appears on the right side.
    for v in variables_in_order_of_appearance(right_term):
        if v not in variables:
            variables.append(v)

    # Abstract the last-appearing variable first (innermost).
    for variable in reversed(variables):
        left_term = lambda_star(variable, left_term)
        right_term = lambda_star(variable, right_term)

    print(f"{left_text} = {right_text}")
    print(f"  free variables: {variables}")
    print(f"  closure:        {term_to_string(left_term)} = {term_to_string(right_term)}")
    print()


# ----------------------------------------------------------------------
# Step 6: run it on the list of axioms
# ----------------------------------------------------------------------

axioms = [
    ("ib", "b"),
    ("i(bx)", "bx"),
    ("i(bxy)", "bxy"),
    ("ic", "c"),
    ("i(cx)", "cx"),
    ("i(cxy)", "cxy"),
    ("ii", "i"),
    ("bix", "bxi"),
    ("c(c(bbx)y)z", "cx(yz)"),
    ("c(b(bx)y)z", "bcx(cyz)"),
    ("b(bxy)z", "bx(byz)"),
    ("c(c(bcx)y)z", "c(cxz)y"),
    ("c(b(cx)y)z", "b(xz)y"),
    ("b(cxy)z", "c(bxz)y"),
]

for left_text, right_text in axioms:
    close_equation(left_text, right_text)
