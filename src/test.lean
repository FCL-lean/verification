import data.nat.prime
import data.int.modeq
open nat

inductive pf {p : ℕ}
| of_int : ℤ → pf

namespace pf

variables {p : ℕ} {m: prime p}

/-- equivalence --/
protected def eq : (@pf p) → (@pf p) → Prop
  | (of_int m) (of_int n) := m ≡ n [ZMOD p]

notation a `≡` b := pf.eq a b

@[refl] protected theorem eq.refl {α : @pf p} : α ≡ α := by cases α; unfold pf.eq

@[symm] protected theorem eq.symm {α β : @pf p} : α ≡ β → β ≡ α := 
  begin
    intro h,
    cases α, cases β,
    unfold pf.eq at *,
    exact int.modeq.symm h
  end 

@[trans] protected theorem eq.trans {α β γ : @pf p} : α ≡ β → β ≡ γ → α ≡ γ := 
  begin 
    intros h1 h2,
    cases α, cases β, cases γ,
    unfold pf.eq at *,
    exact int.modeq.trans h1 h2
  end

protected theorem equiv.is_equivalence : equivalence (@pf.eq p) := 
  mk_equivalence (@pf.eq p) (@eq.refl p) (@eq.symm p) (@eq.trans p)

instance : has_equiv (@pf p) := ⟨pf.eq⟩

instance decidable_eq (α β : @pf p) : decidable (α ≡ β) := 
  by cases α; cases β; apply int.decidable_eq

lemma eq_lem (n : ℤ) : @of_int p n ≡ @of_int p (n % p) := 
  begin
    unfold pf.eq at *,
    symmetry,
    apply int.modeq.mod_modeq n p
  end

/-- zero one --/
protected def zero : @pf p := of_int (int.zero)
protected def one : @pf p := of_int (int.one)

instance : has_zero (@pf p) := ⟨pf.zero⟩
instance : has_one (@pf p) := ⟨pf.one⟩

lemma of_int_zero : of_int (0 : ℤ) ≡ (0 : @pf p) := eq.refl
lemma of_int_one : of_int (1 : ℤ) ≡ (1 : @pf p) := eq.refl

/-- arithmetic --/
protected def add : @pf p → @pf p → @pf p
| (of_int m) (of_int n) := of_int (m + n)

protected def mul : @pf p → @pf p → @pf p
| (of_int m) (of_int n) := of_int (m * n)

protected def sub : @pf p → @pf p → @pf p
| (of_int m) (of_int n) := of_int (m - n)

instance : has_add (@pf p) := ⟨pf.add⟩
instance : has_mul (@pf p) := ⟨pf.mul⟩
instance : has_sub (@pf p) := ⟨pf.sub⟩

theorem pf_add {α β γ η: @pf p} (h₁ : α ≡ β) (h₂ : γ ≡ η) : α + γ ≡ β + η := 
  begin
    cases α, cases β, cases γ, cases η,
    apply int.modeq.modeq_add h₁ h₂
  end

theorem pf_mul {α β γ η : @pf p} (h₁ : α ≡ β) (h₂ : γ ≡ η) : α * γ ≡ β * η := 
  begin 
    cases α, cases β, cases γ, cases η,
    apply int.modeq.modeq_mul h₁ h₂    
  end

theorem pf_sub {α β γ η: @pf p} (h₁ : α ≡ β) (h₂ : γ ≡ η) : α - γ ≡ β - η := 
  begin
    cases α, cases β, cases γ, cases η,
    apply int.modeq.modeq_sub h₁ h₂
  end

end pf
