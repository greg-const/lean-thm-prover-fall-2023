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
