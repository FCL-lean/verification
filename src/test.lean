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

lemma mul_mod_lem {a b : ℕ} : ∀ (x : ℤ), a * x ≡ a * (x % b) [ZMOD b] := 
begin
  intro,
  let h₁ : x ≡ (x % b) [ZMOD b],
  begin
    apply int.modeq.symm,
    apply int.modeq.mod_modeq
  end,
  let h₂ := int.modeq.modeq_mul_left,
  swap, exact b, swap, exact x, swap, exact (x % b), 
  apply (h₂ a h₁)
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

lemma pf_inv_trans_lem₁ {a b : ℕ} {h₁ : b > 0} (h₂ : ∃ (x : ℤ), a * x ≡ 1 [ZMOD b]) : (∃ (x : ℤ), (x ≥ 0) ∧ x < b ∧ a * x ≡ 1 [ZMOD b]) := 
begin
  apply exists.elim h₂,
  assume x, assume fx,
    
  apply exists.intro,
  swap,
  exact (x % b),
  let h := mod_range h₁ x,
  apply and.intro, apply h.left,
  apply and.intro, apply h.right,
  begin
    apply int.modeq.trans, apply int.modeq.symm,
    apply mul_mod_lem,
    assumption
  end
end

lemma pf_inv_trans_lem₂ {a : ℕ} {h₁ : prime p} (h₂ : ∃ (x : ℤ), (x ≥ 0) ∧ x < p ∧ a * x ≡ 1 [ZMOD p]) : (∃ (x : @pf p), a * x.1 ≡ 1 [ZMOD p]) :=
begin
  apply exists.elim h₂,
  assume x, assume h₃,
  apply exists.intro,
  swap, exact (@int_to_pf p x h₁), rw int_to_pf, simp,
  apply int.modeq.trans, apply int.modeq.symm,
  apply mul_mod_lem,
  apply h₃.right.right
end

theorem inv_exist (e : @pf p) (h₁ : e.1 > 0) : (∃ (x : @pf p), e.1 * x.1 ≡ 1 [ZMOD p]) :=
  begin
    let h₂ := int.modeq.mod_coprime ((pf_coprime e) h₁),
    cases e, simp at *, simp at *,
    let h₃ := pf_inv_trans_lem₁,
    swap, exact (int.to_nat e_val), swap, exact p,
    begin
      let h₄ := pf_inv_trans_lem₂,
      swap, exact p, swap, exact (int.to_nat e_val),
      let h₄₁ : ↑(int.to_nat e_val) = e_val,
      begin
        cases e_val,
        let h₄₂ : int.to_nat (int.of_nat e_val) = e_val,
        refl, rw h₄₂ at *, refl,
        let h₃₁ := int.neg_succ_lt_zero e_val,
        let h₃₂ := not_lt_of_le (le_of_lt h₃₁),
        apply (absurd h₁ h₃₂)
      end,
      let h₅ := (h₄ (h₃ h₂)),
      rw h₄₁ at *,
      assumption,
      apply e_property.left
    end,
    begin
        apply (prime.pos e_property.left)
    end,
  end


end pf

    
      




end
