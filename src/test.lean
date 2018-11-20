import data.finset
import linear_algebra.multivariate_polynomial
import ring_theory.ideals
import tactic.find
variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {ι : Type*}
variables [comm_semiring α]
variables [decidable_eq α]
variables [comm_ring (mv_polynomial ℕ α)]

variable (ss : set (mv_polynomial ℕ α))

class is_monomial_order (α : Type*) (r : α → α → Prop) extends has_add α, is_linear_order α r :=
    (mono_order : ∀ a b w : α, (r a b) → r (a + w) (b + w) )

namespace finsupp

lemma in_not (a : ℕ →₀ ℕ) : ∀ x : ℕ, x ∈ a.support ∨ x ∉ a.support := 
    by intro; apply classical.or_not

def le_aux : (ℕ →₀ ℕ) → (ℕ →₀ ℕ) → ℕ → Prop
| a b 0 := a 0 ≤ b 0
| a b (nat.succ m) := (a (nat.succ m) < b (nat.succ m)) ∨ 
                        ((a (nat.succ m) = b (nat.succ m)) ∧ le_aux a b m) 
    
def max (a : ℕ →₀ ℕ) : ℕ := a.support.sup id
def max_ab (a b : ℕ →₀ ℕ) : ℕ := (a.support ∪ b.support).sup id
protected def le : (ℕ →₀ ℕ) → (ℕ →₀ ℕ) → Prop := λ a b, le_aux a b $ max_ab a b

instance : has_le (ℕ →₀ ℕ) := ⟨finsupp.le⟩ 

lemma add_gt (a b : ℕ →₀ ℕ) : a ≤ (a + b) := 
begin
    unfold has_le.le finsupp.le,
    induction (max_ab a (a + b)),
    all_goals {unfold le_aux},
    all_goals {simp},
    by_cases (b (nat.succ n) > 0), left, assumption,
    right,
    let h' := nat.le_zero_iff.elim_left (le_of_not_gt h),
    rw h', simp, assumption
end

lemma gt_max_not_in : ∀ (a : ℕ →₀ ℕ) (x : ℕ), (x > max a) → x ∉ a.support :=
begin
    intros a x h₁ h₂,
    unfold max at *,
    let h₃ : id x ≤ finset.sup (a.support) id := finset.le_sup h₂,
    rw id at *,
    apply (absurd h₁ (not_lt_of_ge h₃))
end

lemma gt_sup_eq_zero (a : ℕ →₀ ℕ) : ∀ k : ℕ, max a < k → a k = 0 :=
begin
    intros,
    have h : k ∉ a.support := gt_max_not_in a k a_1,
    have h' := in_not a k,
    cases h', exact absurd h' h,
    apply not_mem_support_iff.elim_left, assumption
end

lemma max_ab_ge_max_a : ∀ (a b : ℕ →₀ ℕ), max_ab a b ≥ max a :=
begin
    intros a b,
    unfold max_ab max,
    rw finset.sup_union, apply lattice.le_sup_left,
end

lemma max_ab_ge_max_b : ∀ (a b : ℕ →₀ ℕ), max_ab a b ≥ max b :=
begin
    intros a b,
    unfold max_ab max,
    rw finset.sup_union, apply lattice.le_sup_right,
end

lemma gt_max_ab_not_in : ∀ (a b : ℕ →₀ ℕ) (x : ℕ), (x > max_ab a b) → x ∉ a.support ∧ x ∉ b.support :=
begin
    intros a b x h₁,
    unfold max_ab at *, 
    rw finset.sup_union at *,
    have h₄ : finset.sup (a.support) id < x := lt_of_le_of_lt lattice.le_sup_left h₁,
    have h₅ : finset.sup (b.support) id < x := lt_of_le_of_lt lattice.le_sup_right h₁,
    apply and.intro, 
    all_goals {intro h₂},
    apply (gt_max_not_in a x h₄ h₂),
    apply (gt_max_not_in b x h₅ h₂),
end

lemma support_contain_a (a b : ℕ →₀ ℕ) : a.support ⊆ (a + b).support :=
begin
    unfold has_subset.subset,
    intros a_1 h,
    let ha := (a.mem_support_to_fun a_1).elim_left h,
    have hab : (a + b).to_fun a_1 ≠ 0,
    have r : ∀ x : (ℕ →₀ ℕ), x.to_fun = ⇑x, by intro; refl,
    rw r at *, simp, intro ha',
    apply (absurd ha' ha),
    apply ((a + b).mem_support_to_fun a_1).elim_right hab,
end

lemma support_contain_b (a b : ℕ →₀ ℕ) : b.support ⊆ (a + b).support := by rw add_comm; apply support_contain_a

lemma union_support_contain (a b : ℕ →₀ ℕ) : a.support ∪ b.support ⊆ (a + b).support :=
begin
    have ha := support_contain_a a b,
    have hb := support_contain_b a b,

    
end

lemma max_ab_lt_add (a b w : ℕ →₀ ℕ) : max_ab a b ≤ max_ab (a + w) (b + w) :=
begin
    unfold max_ab,
end

lemma le_of_succ_eq (a b : ℕ →₀ ℕ) (i  : ℕ) (hlei : le_aux a b i) 
      (hi_succ : a (i + 1) = b (i + 1)) : le_aux a b (i + 1) :=
begin
    unfold le_aux,
    apply or.inr, apply and.intro,
    repeat {assumption},
end

lemma le_of_succ_eqs (a b : ℕ →₀ ℕ) (i j : ℕ) (hlei : le_aux a b i) 
    (hk : ∀ k : ℕ, i < k → k ≤ (i + j) → a k = b k) : le_aux a b (i + j) :=
begin
    revert i,
    induction j,
    begin
        intros i hlei hk, assumption,
    end,
    begin
        intros i hlei hk,
        apply le_of_succ_eq,
        apply j_ih, assumption,
        intros k hik hki,
        apply (hk k hik (nat.le_succ_of_le hki)),
        apply hk,
        let h : i < i + nat.succ j_n := nat.lt_add_of_pos_right (nat.zero_lt_succ j_n),
        assumption, refl,
    end,
end

lemma le_add (a b w : ℕ →₀ ℕ) (i : ℕ) (hab : le_aux a b i) : le_aux (a + w) (b + w) i :=
begin
    induction i,
    all_goals {unfold le_aux at *, simp},
    assumption,
    cases hab, left, assumption,
    cases hab, apply or.inr, apply and.intro, assumption,
    apply (i_ih hab_right),
end

lemma mono_order_lem : ∀ (a b w : ℕ →₀ ℕ), (a ≤ b) → ((a + w) ≤ (b + w)) := 
begin 
    intros a b w hab,
    unfold has_le.le finsupp.le at *,
    apply le_add,
    have h := le_of_succ_eqs a b (max_ab a b) ((max_ab (a + w) (b + w)) - (max_ab a b)) hab _ ,
    rw nat.add_sub_of_le at h, assumption,
    swap,
    intros,
    rw nat.add_sub_of_le at a_2,
    rw [gt_sup_eq_zero a k, gt_sup_eq_zero b k],
    have h' := max_ab_ge_max_b a b,
    apply nat.lt_of_le_of_lt h' a_1,
    have h' := max_ab_ge_max_a a b,
    apply nat.lt_of_le_of_lt h' a_1,
end

instance : is_monomial_order (ℕ →₀ ℕ) finsupp.le := sorry

end finsupp


def leading_term (p : mv_polynomial ℕ α) : mv_polynomial ℕ α := sorry

def buchberger {s : set (mv_polynomial ℕ α)} : set (mv_polynomial ℕ α) := sorry