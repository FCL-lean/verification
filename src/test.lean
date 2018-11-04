import data.nat.prime
import data.int.basic
import data.int.modeq

open nat

lemma add_nat_ge_self (b : ℕ) : ∀ a : ℕ, a + b ≥ b 
| 0 := begin simp, apply less_than_or_equal.refl end
| (succ m) := begin rw succ_add, apply le_succ_of_le, apply add_nat_ge_self end

lemma mul_succ_ge_self (a : ℕ) : ∀ (n : ℕ), n * (succ a) ≥ n :=
begin
  intro,
  show n * (succ a) ≥ n, from
    calc
      n * (succ a) = n * a + n : rfl
             ...   ≥ n : (@add_nat_ge_self n (n*a))
end

lemma mod_range {b : ℕ} : (b > 0) → ∀ (x : ℤ), 0 ≤ x % b ∧ x % b < b := 
begin
  assume h₁, assume x,
  apply and.intro,
  begin 
    apply int.mod_nonneg, simp,
    assume h₃,
    rw h₃ at *,
    let h₃₂ : 0 ≤ 0, apply less_than_or_equal.refl,
    apply (absurd h₁),
    apply (not_lt_of_le h₃₂),
  end,
  begin
    apply int.mod_lt_of_pos,
    apply int.coe_nat_lt.elim_right,
    assumption
  end,
end

lemma mul_mod_lem {b : ℕ} : ∀ (a x : ℤ), a * x ≡ a * (x % b) [ZMOD b] := 
begin
  intros,
  let h₁ : x ≡ (x % b) [ZMOD b],
  begin
    apply int.modeq.symm,
    apply int.modeq.mod_modeq
  end,
  let h₂ := int.modeq.modeq_mul_left,
  swap, exact b, swap, exact x, swap, exact (x % b), 
  apply (h₂ a h₁)
end

lemma int_coe_to_nat_eq : ∀ (x : ℤ), (x > 0) → (↑(int.to_nat x) = x) :=
begin
  intros x h₀,
  cases x,
  let h₁ : int.to_nat (int.of_nat x) = x,
  refl, rw h₁ at *, refl,
  let h₂ := int.neg_succ_lt_zero x,
  let h₃ := not_lt_of_le (le_of_lt h₂),
  apply (absurd h₀ h₃)
end

def pf {p : ℕ} := {e : ℤ// prime p ∧ 0 ≤ e ∧ e < p}

namespace pf

variable { p: ℕ }

def int_to_pf (x : ℤ) {h: prime p} : @pf p := 
  ⟨x % p, begin 
       apply and.intro, 
       assumption,
       apply mod_range,
       apply (prime.pos h)
      end⟩

lemma pf_coprime (a: @pf p): (a.1 > 0) → coprime (int.to_nat a.1) p := 
begin
  assume h₀,
  cases a,
  simp at *,
  cases a_val, 
    let h₀₀ : int.to_nat (int.of_nat a_val) = a_val,
    refl,
    rw h₀₀ at *,
    cases a_val, 
    begin
      let h₀₁ : (int.of_nat 0) ≤ 0,
      refl,
      let h₀₂ := not_lt_of_le h₀₁,
      apply absurd h₀ h₀₂,
    end,
    begin
      let h₁ : ¬ (has_dvd.dvd p (succ a_val)),
      begin
        intro, cases a, cases a_w, cases a_h,
            
        let h₁₁ : succ a_val ≥ p,
        rw a_h, 
        apply mul_succ_ge_self,
        apply (absurd a_property.right.right), 
        let h₁₂ := int.coe_nat_le.elim_right,
        swap, exact p, swap, exact (succ a_val),
        exact (not_lt_of_le (h₁₂ h₁₁))
      end,
      let h₂ := (@prime.coprime_iff_not_dvd p (succ a_val) a_property.left).elim_right, apply coprime.symm, exact (h₂ h₁)
    end,
    begin
      let h₃₁ := int.neg_succ_lt_zero a_val,
      let h₃₂ := not_lt_of_le (le_of_lt h₃₁),
      apply (absurd h₀ h₃₂)
    end
end

theorem inv_exist (e : @pf p) (h₁ : e.1 > 0) : (∃ (x : @pf p), e.1 * x.1 ≡ 1 [ZMOD p]) :=
  begin
    let h₂ := int.modeq.mod_coprime ((pf_coprime e) h₁),
    cases e, simp at *, simp at *,
    begin
      apply exists.elim h₂,
      intros x h₃,
      apply exists.intro,
      swap, exact (@int_to_pf p x e_property.left), rw int_to_pf, simp,
      apply int.modeq.trans, apply int.modeq.symm,
      apply mul_mod_lem,
      rw int_coe_to_nat_eq at *,
      apply h₃, repeat {try {exact h₁}},
    end
  end

end pf

    
      




end
