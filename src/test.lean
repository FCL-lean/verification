import data.nat.prime
import data.int.basic
def pf (p : ℕ) [nat.prime p] := { e: ℤ // 0 ≤ e ∧ e < p }

section PF
variable p : ℕ
variable [prime_p : nat.prime p]

def sub_a_a_eq_zero (a : ℕ): a - a = 0:=
begin
  induction a,
  begin trivial end,
  begin 
    simp,
    assumption
  end
end

def ge_sub_zero: Π (a b : ℕ), a ≥ b → b - a = 0 :=
  λ a b p, match a, b, p with
           | nat.zero, nat.zero, (nat.less_than_or_equal.refl nat.zero) := by trivial
           | nat.succ a1, nat.succ a2, (nat.less_than_or_equal.refl _) := begin simp, exact sub_a_a_eq_zero a2 end
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


-- instance from ℤ
def pf_add (a b: @pf p prime_p) : @pf p prime_p := ⟨((a.1 + b.1) % p), 
                begin apply and.intro, 
                begin
                  unfold has_mod.mod,
                  cases a.val + b.val,
                  trivial,
                  unfold int.mod,
                  eapply sub_nat_nat_ge_zero,
                  show int.nat_abs p > a_1 % int.nat_abs p, 
                           by { apply nat.mod_lt, 
                                unfold nat.prime at prime_p, 
                                cases prime_p,
                                rw [int.nat_abs_of_nat],
                                eapply (@lt.trans _ _ 0 1),
                                constructor,
                                assumption
                              },

                end,
                begin
                  apply int.mod_lt_of_pos,
                  cases prime_p,
                  apply (int.coe_nat_lt_coe_nat_iff 0 p).elim_right,
                  eapply (@lt.trans _ _ 0 1),
                  constructor,
                  assumption
               end   
               end⟩


end PF
