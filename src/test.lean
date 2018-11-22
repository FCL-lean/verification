import data.finset
import linear_algebra.multivariate_polynomial
import ring_theory.ideals
import tactic.find
variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {ι : Type*}
variables [comm_semiring α]
variables [decidable_eq α] [decidable_linear_order α]
variables [comm_ring (mv_polynomial ℕ α)]


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

protected def lt : (ℕ →₀ ℕ) → (ℕ →₀ ℕ) → Prop := λ a b, a ≤ b ∧ a ≠ b
instance : has_lt (ℕ →₀ ℕ) := ⟨finsupp.lt⟩

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
    intros elem p,
    have lem := finset.mem_union.elim_left p,
    cases lem,
    exact ha lem,
    exact hb lem,
end

lemma finset_max_le (a b : finset ℕ) : finset.sup a id ≤ finset.sup (a ∪ b) id :=
begin
    rw finset.sup_union,
    apply lattice.le_sup_left,
end
lemma max_ab_lt_add (a b w : ℕ →₀ ℕ) : max_ab a b ≤ max_ab (a + w) (b + w) :=
begin
    unfold max_ab,
    have prf := λ (a b : ℕ →₀ ℕ), finset.subset.antisymm (union_support_contain a b) finsupp.support_add,
    repeat {rw [←prf] },
    rw [ finset.union_assoc, finset.union_comm b.support w.support ],
    rw [←finset.union_assoc w.support, finset.union_idempotent, 
         finset.union_comm w.support, ←finset.union_assoc],
    apply finset_max_le,
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
    rw [gt_sup_eq_zero a k, gt_sup_eq_zero b k],
    have h' := max_ab_ge_max_b a b,
    apply nat.lt_of_le_of_lt h' a_1,
    have h' := max_ab_ge_max_a a b,
    apply nat.lt_of_le_of_lt h' a_1,
    apply max_ab_lt_add,
end
lemma not_le_not_ge_eq (a b : ℕ) : ¬ a < b → ¬ b < a → a = b :=
begin
    intros,
    have h := lt_trichotomy a b,
    cases h, exact absurd h a_1,
    cases h, assumption, exact absurd h a_2,
end

instance : is_monomial_order (ℕ →₀ ℕ) finsupp.le := sorry
instance : decidable_rel finsupp.le := λ a b, 
begin 
    unfold finsupp.le,
    induction max_ab a b,
    unfold le_aux, apply_instance,
    unfold le_aux,
    by_cases (a (nat.succ n) < b (nat.succ n)),
    exact is_true (or.inl h),
    by_cases (a (nat.succ n) > b (nat.succ n)),
    let m : ¬ (a (nat.succ n) < b (nat.succ n) ∨ a (nat.succ n) = 
          b (nat.succ n) ∧ le_aux a b n),
    intro t, cases t with t'; dedup,
    exact h t',
    cases t, rw t_left at *, exact h h_1,
    exact is_false m,
    dedup, have m := not_le_not_ge_eq _ _ h h_1,
    cases ih,
    have m : ¬ (a (nat.succ n) < b (nat.succ n) ∨ a (nat.succ n) = 
          b (nat.succ n) ∧ le_aux a b n),
    intro, cases a_1,
    exact absurd a_1 h,
    cases a_1,
    exact absurd a_1_right ih,
    exact is_false m,
    exact is_true (or.inr (and.intro m ih)),
end

end finsupp


namespace mv_polynomial

def leading_term (p : mv_polynomial ℕ α) : mv_polynomial ℕ α := 
   dite (p.support.sort finsupp.le = list.nil) 
        (λ prf, mv_polynomial.C (p.to_fun 0))
        (λ nprf, let g := list.last (p.support.sort finsupp.le) nprf 
                 in finsupp.single g (p.to_fun g))

def leading_term' (p : mv_polynomial ℕ α) : ℕ →₀ ℕ := 
   dite (p.support.sort finsupp.le = list.nil) 
        (λ prf, 0)
        (λ nprf, list.last (p.support.sort finsupp.le) nprf)

def leading_coeff (p : mv_polynomial ℕ α) : α := 
   dite (p.support.sort finsupp.le = list.nil) 
        (λ prf, p.to_fun 0)
        (λ nprf, let g := list.last (p.support.sort finsupp.le) nprf 
                 in p.to_fun g)

protected def lt (a b : mv_polynomial ℕ α) : Prop := a.leading_term' < b.leading_term'
instance : has_lt (mv_polynomial ℕ α) := ⟨mv_polynomial.lt⟩ 

/-
lemma constant_poly_or_not (p : mv_polynomial ℕ α) : decidable (∃ a : α, p = mv_polynomial.C a) := 
    if h₀ : p.support = ∅ 
        then is_true 
            begin 
                unfold C monomial finsupp.single,
                apply (exists.intro (0 : α)),
                simp,
                apply finsupp.ext, intro,
                rw iff.elim_left finsupp.support_eq_empty h₀,
                refl,
            end
    else    if h₁ : p.support = {0} 
                then  is_true
                    begin
                        unfold C monomial,
                        apply (exists.intro (p.to_fun 0)),
                        apply finsupp.ext, intro,
                        change p.to_fun a = (finsupp.single 0 (p.to_fun 0)).to_fun a,
                        unfold finsupp.single, simp,
                        by_cases 0 = a,
                        simp [h],
                        rw if_neg h,
                        have ha : a ∉ p.support,
                        rw [h₁, finset.insert_empty_eq_singleton, finset.mem_singleton], 
                        apply ne.symm, assumption,
                        apply finsupp.not_mem_support_iff.elim_left ha,
                    end
            else is_false
                begin
                    unfold C monomial finsupp.single,
                    intro,
                    cases a,
                    rw a_h at *,
                    by_cases a_w = 0,
                    rw h at *, simp at *, assumption, simp at h₁,
                    rw (if_neg h) at h₁,
                    apply (ne_self_iff_false (finset.singleton 0)).mp h₁,
                end
-/

def mv_trichotomy (p : mv_polynomial ℕ α) : psum (p = mv_polynomial.C 0) 
            (psum (Σ'a : α, p = mv_polynomial.C a) ((Σ'a : α, p = mv_polynomial.C a) → false)):= 
if h₀ : p.support = ∅ 
    then
    begin
        left, 
        unfold C monomial finsupp.single,
        simp,
        apply finsupp.ext, intro,
        rw iff.elim_left finsupp.support_eq_empty h₀,
        refl,
    end
else if h₁ : p.support = {0} 
        then 
        begin
            right, left,
            unfold C monomial,
            apply (psigma.mk (p.to_fun 0)),
            apply finsupp.ext, intro,
            change p.to_fun a = (finsupp.single 0 (p.to_fun 0)).to_fun a,
            unfold finsupp.single, simp,
            by_cases 0 = a,
            simp [h],
            rw if_neg h,
            have ha : a ∉ p.support,
            rw [h₁, finset.insert_empty_eq_singleton, finset.mem_singleton], 
            apply ne.symm, assumption,
            apply finsupp.not_mem_support_iff.elim_left ha,
        end
    else
    begin
        right, right,
        intro h,
        unfold C monomial finsupp.single at h,
        cases h,
        by_cases h_fst = 0,
        rw h at *, simp [h_snd] at *, assumption, 
        simp [h_snd] at *,
        rw (if_neg h) at h₁,
        apply (ne_self_iff_false (finset.singleton 0)).mp h₁,
    end


def leading_term_lcm (p q : mv_polynomial ℕ α) : mv_polynomial ℕ α := 
begin
    have hp := mv_trichotomy p,
    have hq := mv_trichotomy q,
    cases hp, exact mv_polynomial.C 0,
    cases hq, exact mv_polynomial.C 0,
    cases hp, all_goals {cases hq},
    begin
        cases hp, cases hq,
        exact mv_polynomial.C (max hp_fst hq_fst),
    end,
    begin
        cases hp,
        let coeff := max hp_fst (q.to_fun (q.leading_term')),
        exact monomial q.leading_term' coeff,
    end,
    begin
        cases hq,
        let coeff := max hq_fst (p.to_fun (p.leading_term')),
        exact monomial p.leading_term' coeff,
    end,
    begin
        let coeff := max (p.to_fun (p.leading_term')) (q.to_fun (q.leading_term')),
        let supp := finsupp.zip_with max (max_self 0) p.leading_term' q.leading_term',
        exact monomial supp coeff,
    end
end

def div (a b : mv_polynomial ℕ α) : Σ'q r, r < b ∧ a = b * q + r := 
begin

end

def s_poly (p q : mv_polynomial ℕ α) : mv_polynomial ℕ α := sorry

def buchberger {s : set (mv_polynomial ℕ α)} : set (mv_polynomial ℕ α) := sorry

end mv_polynomial