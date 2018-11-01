import data.nat.prime
open nat

inductive pf (p : ℕ): Type
| of_int : ℤ → pf

namespace pf

variables {p : ℕ} 

protected def zero : pf p := of_int p (int.zero)
protected def one : pf p := of_int p (int.one)

instance : has_zero (pf p) := ⟨pf.zero⟩
instance : has_one (pf p) := ⟨pf.one⟩

lemma of_int_zero : of_int p (0 : ℤ) = (0 : pf p) := rfl
lemma of_int_one : of_int p (1 : ℤ) = (1 : pf p) := rfl

protected def equiv : (pf p) → (pf p) → Prop
  | (of_int _ m) (of_int _ n) := if (m % p = n % p) then true else false

instance : has_equiv (pf p) := ⟨pf.equiv⟩

protected def add : pf p → pf p → pf p
| (of_int _ m) (of_int _ n) := of_int _ ((m + n) % p)

instance : has_add (pf p) := ⟨pf.add⟩

end pf

def p := 5
def a : (pf p) := 0
def b : (pf p) := 5

#print p
#print a
#print b

