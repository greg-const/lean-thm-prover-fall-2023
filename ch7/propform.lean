inductive prop_formula : Type
| tt : prop_formula
| ff : prop_formula
| land : prop_formula → prop_formula → prop_formula
| lor : prop_formula → prop_formula → prop_formula
| lnot : prop_formula → prop_formula

def A := prop_formula.tt
def B := prop_formula.ff
def C := prop_formula.ff

def p : prop_formula :=
  prop_formula.land A (prop_formula.lor B (prop_formula.lnot C)) -- A ∧ ( B ∨ ¬C)


def eval : prop_formula → bool
| (prop_formula.tt) := tt
| (prop_formula.ff) := ff
| (prop_formula.land p q) := eval p ∧ eval q
| (prop_formula.lor p q) := eval p ∨ eval q
| (prop_formula.lnot p) := ¬ (eval p)

#eval eval p -- Output: true


-- open in lean online
-- https://leanprover-community.github.io/lean-web-editor/#code=inductive%20prop_formula%20%3A%20Type%0A%7C%20tt%20%3A%20prop_formula%0A%7C%20ff%20%3A%20prop_formula%0A%7C%20land%20%3A%20prop_formula%20%E2%86%92%20prop_formula%20%E2%86%92%20prop_formula%0A%7C%20lor%20%3A%20prop_formula%20%E2%86%92%20prop_formula%20%E2%86%92%20prop_formula%0A%7C%20lnot%20%3A%20prop_formula%20%E2%86%92%20prop_formula%0A%0Adef%20A%20%3A%3D%20prop_formula.tt%0Adef%20B%20%3A%3D%20prop_formula.ff%0Adef%20C%20%3A%3D%20prop_formula.ff%0A%0Adef%20p%20%3A%20prop_formula%20%3A%3D%0A%20%20prop_formula.land%20A%20%28prop_formula.lor%20B%20%28prop_formula.lnot%20C%29%29%20--%20A%20%E2%88%A7%20%28%20B%20%E2%88%A8%20%C2%ACC%29%0A%0A%0Adef%20eval%20%3A%20prop_formula%20%E2%86%92%20bool%0A%7C%20%28prop_formula.tt%29%20%3A%3D%20tt%0A%7C%20%28prop_formula.ff%29%20%3A%3D%20ff%0A%7C%20%28prop_formula.land%20p%20q%29%20%3A%3D%20eval%20p%20%E2%88%A7%20eval%20q%0A%7C%20%28prop_formula.lor%20p%20q%29%20%3A%3D%20eval%20p%20%E2%88%A8%20eval%20q%0A%7C%20%28prop_formula.lnot%20p%29%20%3A%3D%20%C2%AC%20%28eval%20p%29%0A%0A%23eval%20eval%20p%20--%20Output%3A%20true
--
