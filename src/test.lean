import data.nat.prime
import data.int.basic
import data.int.modeq
def pf (p : ℕ) [nat.prime p] := { e: ℤ // 0 ≤ e ∧ e < p }

section PF
variable p : ℕ
variable [prime_p : nat.prime p]




def ge_sub_zero: Π (a b : ℕ), a ≥ b → b - a = 0 :=
  λ a b p, match a, b, p with
           | nat.zero, nat.zero, (nat.less_than_or_equal.refl nat.zero) := by trivial
           | nat.succ a1, nat.succ a2, (nat.less_than_or_equal.refl _) := begin simp, apply nat.sub_self end
           | nat.succ a1, nat.zero, (nat.less_than_or_equal.step m1) := begin simp end
           | nat.succ a1, nat.succ a2, (nat.less_than_or_equal.step m1) := 
              begin
                simp,
                let m := _match a1 a2 _,
                assumption,
                apply nat.le_trans,
                apply nat.le_succ,
                assumption,
              end
           end

def sub_nat_nat_ge_zero : Π (a b : ℕ), a ≥ b → int.sub_nat_nat a b ≥ 0
| nat.zero nat.zero p := by trivial
| nat.zero (nat.succ b) p := 
begin 
  unfold int.sub_nat_nat,
  simp,
  cases nat.succ b,
  simp,
  cases p
end
| (nat.succ a) nat.zero p := 
begin
  unfold int.sub_nat_nat,
  simp
end
| (nat.succ a) (nat.succ b) p :=
begin
  unfold int.sub_nat_nat,
  simp,
  cases h: b - a,
  trivial,
  unfold int.sub_nat_nat,
  let eq0: b - a = 0,
  apply ge_sub_zero,
  apply nat.le_of_succ_le_succ,
  assumption,
  rw [eq0] at h,
  cases h
end

def mod_in_range: Π (a : ℤ), (p > 0) → ((a % p) ≥ 0) ∧ (a % p < p) :=
begin
  intros a prove,
  unfold has_mod.mod,
  apply and.intro,
  begin
    cases a,
    by trivial,
    begin
      unfold int.mod,
      eapply sub_nat_nat_ge_zero,
      apply nat.mod_lt, 
      rw [int.nat_abs_of_nat],
      assumption
    end
  end,
  begin
    apply int.mod_lt_of_pos,
    apply (int.coe_nat_lt_coe_nat_iff 0 p).elim_right,
    assumption
  end
end

-- instance from ℤ
def pf_add (a b: @pf p prime_p) : @pf p prime_p := 
   ⟨((a.1 + b.1) % p), begin 
                         apply mod_in_range p (a.val + b.val) _,
                         apply nat.prime.pos,
                         assumption
                       end⟩
def pf_sub (a b: @pf p prime_p) : @pf p prime_p := 
   ⟨((a.1 - b.1) % p), begin 
                         apply mod_in_range p (a.val - b.val) _,
                         apply nat.prime.pos,
                         assumption
                       end⟩
def pf_mul (a b: @pf p prime_p) : @pf p prime_p := 
   ⟨((a.1 * b.1) % p), begin 
                         apply mod_in_range p (a.val * b.val) _,
                         apply nat.prime.pos,
                         assumption
                       end⟩
def pf_one : @pf p prime_p := ⟨1, begin apply and.intro, trivial, apply (int.coe_nat_lt_coe_nat_iff 1 p).elim_right, exact nat.prime.ge_two prime_p end⟩

def pf_to_nat (a : @pf p prime_p) : ℕ := 
begin
  exact int.to_nat a.val
end


def pf_inv_lem (a b : ℤ) (p : ℕ) : (gt p 0) → (a * (b % p)) % p = (a * b) % p :=
begin 
  intros,
  apply int.modeq.modeq_mul_left,
  apply int.modeq.mod_modeq,
end

def pf_inv_lem2 (a b : ℤ) (p : ℕ) : (gt p 0) → (a % p * b) % p = (a * b) % p :=
begin
  intros,
  apply int.modeq.modeq_mul_right,
  apply int.modeq.mod_modeq,
end

def mul_gt (a b: ℕ): (nat.succ a) * b ≥ b :=
begin
  induction b,
  constructor,
  unfold has_mul.mul,
  unfold nat.mul,
  -- succ a * succ b = succ a * b + succ a
  unfold has_add.add,
  unfold nat.add,
  unfold ge,
  apply nat.succ_le_succ,
  apply le_trans,
  exact b_ih,
-- nat.succ a * b_n + 0 ≤ nat.add (nat.mul (nat.succ a) b_n) a
  let q:= @nat.add_le_add_left 0 a _ (nat.succ a * b_n),
  rw [←nat.add_zero (nat.succ a * b_n)],
  assumption,
  apply nat.zero_le,
end

lemma gt_not_dvd (a b: ℕ): (gt b a) → ¬ a = 0 → (gt b 1) → ¬ (has_dvd.dvd b a) :=
begin
  intros,
  intro,
  unfold has_dvd.dvd at a_4,
  cases a_4,
  cases a,
  apply a_2, trivial,
  rw a_4_h at a_1,
  cases b,
  cases a_3,
  rw mul_comm at a_1,
  unfold gt at a_1,
  cases a_4_w,
  cases a_4_h,
  let h := mul_gt a_4_w (nat.succ b),
  exact absurd h (not_le_of_lt a_1)
end

def pf_coprime (a: @pf p prime_p): (gt a.val 0) → nat.coprime (@pf_to_nat p prime_p a) p :=
begin
  intro a_gt_0,
  unfold pf_to_nat,
  cases a,
  simp at *,
  cases a_val,
  swap,
  cases a_gt_0,
  change nat.coprime (int.to_nat (↑ a_val)) p,
  unfold int.to_nat,
  let h: a_val < p,
  cases a_property,
  apply int.coe_nat_lt.elim_left,
  assumption,
  unfold nat.coprime,
  rw nat.gcd_comm,
  apply (nat.prime.coprime_iff_not_dvd prime_p).elim_right,
  let pr := nat.prime_def_lt'.elim_left prime_p,
  let prr := pr.right,
  cases a_val,
  cases a_gt_0,
  cases a_val,
  unfold has_dvd.dvd,
  intro,
  cases a,
  rw a_h at h,
  let m : a_w < 1,
  apply (@lt_of_mul_lt_mul_left _ _ _ _ p),
  simp,
  assumption,
  apply nat.zero_le,
  unfold has_lt.lt at m,
  cases m,
  cases a_h,
  cases m_a,
  intro,
  apply gt_not_dvd (nat.succ (nat.succ a_val)) p,
  assumption,
  trivial,
  exact nat.prime.ge_two prime_p,
  assumption
end



lemma pf_inv_ex (a : @pf p prime_p): (gt a.val 0) → ∃ (y: @pf p prime_p), @pf_mul p prime_p a y = @pf_one p prime_p :=
begin
  intro gt_a_0,
  let h: nat.coprime (@pf_to_nat p prime_p a) p,
  swap,
  let m := int.modeq.mod_coprime h,
  apply (exists.elim m),
  intros a1 a2,
  apply exists.intro,
  swap,
  exact ⟨(a1 % p), begin exact mod_in_range p a1 (begin apply nat.prime.pos, assumption end) end⟩,
  unfold pf_mul,
  unfold pf_one,
  simp,
  unfold pf_to_nat at a2,
  rw pf_inv_lem,
  rw int.to_nat_of_nonneg at a2,
  unfold int.modeq at a2,
  rwa (@int.mod_eq_of_lt 1) at a2,
  trivial,
  apply int.coe_nat_lt.elim_right,
  exact nat.prime.gt_one prime_p,
  apply @int.le_trans 0 1,
  trivial,
  assumption,
  exact nat.prime.pos prime_p,
  apply pf_coprime,
  assumption
end

end PF
instance pf_field {prime : ℕ} [pr : nat.prime prime]: field (@pf prime pr) := 
   field.mk (@pf_add prime pr)
