import data.nat.prime
def pf (p : ℕ) [nat.prime p] := { e: ℤ // 0 ≤ e ∧ e < p }

section PF
variable p : ℕ
variable [prime_p : nat.prime p]
#print instances has_mod

def sub_nat_nat_ge_zero : Π (a b : ℕ), int.sub_nat_nat a b ≥ 0
| nat.zero nat.zero := by trivial
| nat.zero (nat.succ b) := begin unfold int.sub_nat_nat, simp,  end
| (nat.succ a) nat.zero := sorry
| (nat.succ a) (nat.succ b) := sorry

def pf_add (a b: @pf p prime_p) : @pf p prime_p := ⟨((a.1 + b.1) % p), 
                begin apply and.intro, 
                begin
                  unfold has_mod.mod,
                  cases a.val + b.val,
                  trivial,
                  unfold int.mod,
                  unfold int.sub_nat_nat, -- (-m - 1) mod n = |n| - (succ (m % |n|))
                end
                end⟩
instance pf_field : field (@pf p m) := 
  field.mk

end PF
