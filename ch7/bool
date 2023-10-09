namespace hidden
inductive bool : Type
| ff : bool
| tt : bool

-- BEGIN
def band (b1 b2 : bool) : bool :=
bool.cases_on b1 hidden.bool.ff b2

def bor (b1 b2 : bool) : bool :=
bool.cases_on b1 b2 hidden.bool.tt

def bnot (b1 : bool) : bool :=
bool.cases_on b1 hidden.bool.tt hidden.bool.ff
-- END

def bt1 : bool := hidden.bool.tt
def bt2 : bool := hidden.bool.tt
def bf1 : bool := hidden.bool.ff

--#reduce

#eval band bt1 bf1
#eval bor bf1 bf1
#eval bnot bt1



end hidden
