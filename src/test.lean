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
                assumption
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
  let r := a.val % p,
  exact int.to_nat r
end

def pf_inv_ex (a : @pf p prime_p) : ∃ (y: @pf p prime_p), @pf_mul p prime_p a y = @pf_one p prime_p :=
begin
  let h: nat.coprime (@pf_to_nat p prime_p a) p,
  swap,
  apply exists.intro,
  swap,
  let m := int.modeq.mod_coprime h,
  cases m,
end

end PF
instance pf_field {prime : ℕ} [pr : nat.prime prime]: field (@pf prime pr) := 
   field.mk (@pf_add prime pr)
