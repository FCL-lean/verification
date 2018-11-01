import data.nat.prime
open nat

inductive pf {p : ℕ}
| of_int : ℤ → pf

namespace pf

variables {p : ℕ} 

protected def zero : @pf p := of_int (int.zero)
protected def one : @pf p := of_int (int.one)

instance : has_zero (@pf p) := ⟨pf.zero⟩
instance : has_one (@pf p) := ⟨pf.one⟩

lemma of_int_zero : of_int (0 : ℤ) = (0 : @pf p) := rfl
lemma of_int_one : of_int (1 : ℤ) = (1 : @pf p) := rfl

protected def equiv : (@pf p) → (@pf p) → Prop
  | (of_int m) (of_int n) := (m % p) = (n % p)

infix `≡` := pf.equiv

protected theorem equiv.refl {α : @pf p} : pf.equiv α α := by cases α; unfold pf.equiv

protected theorem equiv.symm {α β : @pf p} : α ≡ β → β ≡ α := 
  begin
    intro h,
    cases α, cases β,
    unfold pf.equiv at *,
    exact symm h
  end 

protected theorem equiv.trans {α β γ : @pf p} : α ≡ β → β ≡ γ → α ≡ γ := 
  begin 
    intros h1 h2,
    cases α, cases β, cases γ,
    unfold pf.equiv at *,
    exact trans h1 h2,
  end


protected theorem equiv.is_equivalence : equivalence (@pf.equiv p) := 
mk_equivalence (@pf.equiv p) (@equiv.refl p) (@equiv.symm p) (@equiv.trans p)

instance : has_equiv (@pf p) := ⟨pf.equiv⟩

def decidable_eq_lem (a b : ℤ) : decidable (@of_int p a ≡ @of_int p b) := int.decidable_eq _ _ 

instance decidable_eq (α β : @pf p) : decidable (α ≡ β) :=
  by cases α; cases β; apply decidable_eq_lem

protected def add : @pf p → @pf p → @pf p
| (of_int m) (of_int n) := of_int ((m + n) % p)

instance : has_add (@pf p) := ⟨pf.add⟩

end pf


