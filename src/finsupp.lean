import finset
import linear_algebra.multivariate_polynomial
import ring_theory.ideals
import tactic.find
import util
variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {ι : Type*}
variables [discrete_field α]
variables [decidable_eq α] [decidable_linear_order α]
--variables [comm_ring (mv_polynomial ℕ α)]
variables [has_zero γ] [has_zero δ] [decidable_eq γ] [decidable_eq δ]

class is_monomial_order (α : Type*) (r : α → α → Prop) extends has_add α, is_linear_order α r :=
    (mono_order : ∀ a b w : α, (r a b) → r (a + w) (b + w) )

namespace finsupp

lemma in_not (a : γ →₀ δ) : ∀ x : γ, x ∈ a.support ∨ x ∉ a.support := 
    by intro; apply classical.or_not

def le_aux : (ℕ →₀ ℕ) → (ℕ →₀ ℕ) → ℕ → Prop
| a b 0 := a 0 ≤ b 0
| a b (nat.succ m) := (a (nat.succ m) < b (nat.succ m)) ∨ 
                        ((a (nat.succ m) = b (nat.succ m)) ∧ le_aux a b m) 


protected def max (a : ℕ →₀ ℕ) : ℕ := a.support.sup id
protected def max_ab (a b : ℕ →₀ ℕ) : ℕ := (a.support ∪ b.support).sup id

protected def le : (ℕ →₀ ℕ) → (ℕ →₀ ℕ) → Prop := λ a b, le_aux a b $ finsupp.max_ab a b

lemma le_refl : ∀ a : ℕ →₀ ℕ, finsupp.le a a := 
begin 
    intro, unfold finsupp.le,
    induction finsupp.max_ab a a;
    unfold le_aux, right, apply and.intro, refl, assumption,
end

lemma le_aux_trans : ∀ (a b c : ℕ →₀ ℕ) (k : ℕ), (le_aux a b k) → (le_aux b c k) → (le_aux a c k) :=
begin
    intros a b c k hab hbc,
    induction k;
    unfold le_aux at *, apply le_trans hab hbc,
    cases hab; cases hbc,
    left, apply lt_trans hab hbc,
    left, apply (lt_of_lt_of_le hab (le_of_eq hbc.left)),
    left, apply (lt_of_le_of_lt (le_of_eq hab.left) hbc),
    right, apply and.intro, apply eq.trans hab.left hbc.left,
    apply k_ih hab.right hbc.right,
end

lemma max_ab_ge_max_a : ∀ (a b : ℕ →₀ ℕ), finsupp.max_ab a b ≥ finsupp.max a :=
begin
    intros a b,
    unfold finsupp.max_ab finsupp.max,
    rw finset.sup_union, apply lattice.le_sup_left,
end

lemma max_ab_ge_max_b : ∀ (a b : ℕ →₀ ℕ), finsupp.max_ab a b ≥ finsupp.max b :=
begin
    intros a b,
    unfold finsupp.max_ab finsupp.max,
    rw finset.sup_union, apply lattice.le_sup_right,
end

lemma gt_max_not_in : ∀ (a : ℕ →₀ ℕ) (x : ℕ), (x > finsupp.max a) → x ∉ a.support :=
begin
    intros a x h₁ h₂,
    unfold finsupp.max at *,
    let h₃ : id x ≤ finset.sup (a.support) id := finset.le_sup h₂,
    rw id at *,
    apply (absurd h₁ (not_lt_of_ge h₃))
end

lemma gt_sup_eq_zero (a : ℕ →₀ ℕ) : ∀ k : ℕ, finsupp.max a < k → a k = 0 :=
begin
    intros,
    have h : k ∉ a.support := gt_max_not_in a k a_1,
    have h' := in_not a k,
    cases h', exact absurd h' h,
    apply not_mem_support_iff.elim_left, assumption
end

lemma le_aux_of_ge_max (a b : ℕ →₀ ℕ) (i : ℕ) (h : finsupp.le a b) (hi : i ≥ finsupp.max_ab a b) : le_aux a b i :=
begin
    unfold finsupp.le at h,
    induction i,
    unfold le_aux, 
    rw nat.le_zero_iff.1 hi at h, 
    unfold le_aux at h, assumption,
    from if hi₁ : nat.succ i_n = finsupp.max_ab a b
        then by rw hi₁; assumption
        else 
        begin
            have hi₂ := ne_iff_lt_or_gt.1 hi₁,
            cases hi₂,
            apply (absurd hi₂ (not_lt_of_ge hi)),
            have hia := gt_sup_eq_zero a (nat.succ i_n) (lt_of_le_of_lt (max_ab_ge_max_a a b) hi₂),
            have hib := gt_sup_eq_zero b (nat.succ i_n) (lt_of_le_of_lt (max_ab_ge_max_b a b) hi₂),
            rw hib.symm at hia,
            unfold le_aux, 
            right, apply and.intro, assumption,
            apply i_ih (nat.le_of_lt_succ hi₂),
        end,
end

lemma le_of_ge_max_aux (a b : ℕ →₀ ℕ) (i : ℕ) : le_aux a b ((finsupp.max_ab a b) + i) → finsupp.le a b :=
begin
    intro hi,
    induction i,
    unfold has_le.le preorder.le finsupp.le,
    assumption,
    unfold le_aux at hi,
    have hi₁ : nat.succ (finsupp.max_ab a b + i_n) > (finsupp.max_ab a b), 
    have hi₂ : (finsupp.max_ab a b + i_n) < nat.succ(finsupp.max_ab a b + i_n), apply nat.lt_succ_self,
    have hi₃ : (finsupp.max_ab a b) ≤ (finsupp.max_ab a b + i_n), simp, apply lt_of_le_of_lt hi₃ hi₂,
    have hia := gt_sup_eq_zero a (nat.succ (finsupp.max_ab a b + i_n)) (lt_of_le_of_lt (max_ab_ge_max_a a b) hi₁),
    have hib := gt_sup_eq_zero b (nat.succ (finsupp.max_ab a b + i_n)) (lt_of_le_of_lt (max_ab_ge_max_b a b) hi₁),
    rw [hia, hib] at hi,
    repeat {cases hi},
    apply i_ih hi_right,
end

lemma le_trans : ∀ a b c : ℕ →₀ ℕ, finsupp.le a b → finsupp.le b c → finsupp.le a c :=
begin
    intros a b c hab hbc,
    unfold finsupp.le at hab hbc,
    generalize hs : [(finsupp.max_ab a b), (finsupp.max_ab b c), (finsupp.max_ab a c)] = s,
    generalize hk: s.to_finset.sup id = k, rw [←hs] at hk,
    have hkab : (finsupp.max_ab a b) ≤ k, rw ←hk, simp,
    have hkbc : (finsupp.max_ab b c) ≤ k, rw ←hk, simp, rw ←lattice.sup_assoc, apply lattice.le_sup_right,
    have hkac : (finsupp.max_ab a c) ≤ k, rw ←hk, simp, rw [lattice.sup_comm, lattice.sup_assoc], apply lattice.le_sup_left,
    have hab' := le_aux_of_ge_max a b k hab hkab,
    have hbc' := le_aux_of_ge_max b c k hbc hkbc,
    have hac' := le_aux_trans a b c k hab' hbc',
    apply le_of_ge_max_aux,
    swap, exact (k - (finsupp.max_ab a c)),
    rw nat.add_sub_of_le hkac,
    assumption,
end

instance : preorder (ℕ →₀ ℕ) :=
{
    le := finsupp.le,
    le_refl := le_refl,
    le_trans := le_trans,
}

instance : has_le (ℕ →₀ ℕ) := ⟨preorder.le⟩
instance : has_lt (ℕ →₀ ℕ) := ⟨preorder.lt⟩ 

lemma le_antisymm_aux_zero : ∀ (a b : ℕ →₀ ℕ) (i : ℕ),
    le_aux a b i → le_aux b a i → a 0 = b 0
| a b i :=
begin
    induction i; intros,
    unfold le_aux at *, apply nat.le_antisymm; assumption,
    unfold le_aux at *; cases a_1; cases a_2, 
    apply false.elim,
    apply nat.lt_lt_antisym; assumption,
    cases a_2, rw a_2_left at *,
    apply false.elim, apply nat.lt_irrefl _ a_1,
    cases a_1, rw a_1_left at *, apply false.elim,
    apply nat.lt_irrefl _ a_2,
    cases a_1, cases a_2, apply i_ih; assumption,
end

lemma le_antisymm_aux : ∀ (a b : ℕ →₀ ℕ) (i j: ℕ),
    le_aux a b (i + j) → le_aux b a (i + j) → a i = b i
| a b i j le1 le2 :=
begin
    induction j,
    cases i; simp at *; unfold le_aux at *,
    apply nat.le_antisymm le1 le2,
    cases le1; cases le2, apply false.elim,
    apply nat.lt_lt_antisym le1 le2,
    cases le2, symmetry, assumption, cases le1,
    assumption, cases le1, assumption,
    unfold le_aux at *, cases le1; cases le2,
    apply false.elim, apply nat.lt_lt_antisym le1 le2,
    cases le2, rw le2_left at *, apply false.elim, 
    apply nat.lt_irrefl _ le1,
    cases le1, rw le1_left at *, apply false.elim,
    apply nat.lt_irrefl _ le2,
    cases le1; cases le2,
    exact j_ih le1_right le2_right,
end

lemma le_antisymm :  ∀ (a b : ℕ →₀ ℕ), a ≤ b → b ≤ a → a = b := 
λ a b hab hba, 
    begin
        have hab₀ := hab,
        have hba₀ := hba,
        unfold has_le.le preorder.le finsupp.le at hab hba,
        apply ext,
        intro x,
        have h : (finsupp.max_ab a b) = (finsupp.max_ab b a),
        unfold finsupp.max_ab, rw finset.union_comm,
        induction x; rw h at hab, 
        rw [←zero_add (finsupp.max_ab b a)] at hab hba,
        apply le_antisymm_aux a b 0 (finsupp.max_ab b a) hab hba,
        have hab' : le_aux a b (nat.succ x_n + (finsupp.max_ab b a)),
            have h : (nat.succ x_n + (finsupp.max_ab b a)) ≥ finsupp.max_ab a b, rw h, apply nat.le_add_left,
            apply (le_aux_of_ge_max a b (nat.succ x_n + (finsupp.max_ab b a)) hab₀ h),
        have hba' : le_aux b a (nat.succ x_n + (finsupp.max_ab b a)),
            have h : (nat.succ x_n + (finsupp.max_ab b a)) ≥ finsupp.max_ab b a, apply nat.le_add_left,
            apply (le_aux_of_ge_max b a (nat.succ x_n + (finsupp.max_ab b a)) hba₀ h),
        apply le_antisymm_aux a b (nat.succ x_n) (finsupp.max_ab b a) hab' hba',
    end

lemma le_total : ∀  a b : ℕ →₀ ℕ, a ≤ b ∨ b ≤ a :=
λ a b, 
begin
    unfold has_le.le preorder.le finsupp.le,
    have h : (finsupp.max_ab a b) = (finsupp.max_ab b a),
        unfold finsupp.max_ab, rw finset.union_comm,
    rw h,
    induction (finsupp.max_ab b a);
    unfold le_aux, apply nat.le_total,
    have h_tri := lt_trichotomy (a (nat.succ n)) (b (nat.succ n)),
    cases ih;
    cases h_tri, any_goals {left, left, assumption},
    all_goals {cases h_tri}, any_goals {right, left, assumption},
    left, right, apply (and.intro h_tri ih),
    right, right, apply (and.intro h_tri.symm ih),
    
end

instance : decidable_rel finsupp.le := λ a b, 
begin 
    unfold finsupp.le,
    induction finsupp.max_ab a b,
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
    dedup, have m := nat.not_le_not_ge_eq _ _ h h_1,
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

instance : decidable_linear_order (ℕ →₀ ℕ) :=
{
    le := preorder.le,
    le_refl := preorder.le_refl,
    le_trans := preorder.le_trans,
    le_antisymm := le_antisymm,
    le_total := le_total,
    decidable_le := finsupp.decidable_rel,
}

lemma add_gt (a b : ℕ →₀ ℕ) : a ≤ (a + b) := 
begin
    unfold has_le.le preorder.le finsupp.le,
    induction (finsupp.max_ab a (a + b)),
    all_goals {unfold le_aux},
    all_goals {simp},
    by_cases (b (nat.succ n) > 0), left, assumption,
    right,
    let h' := nat.le_zero_iff.elim_left (le_of_not_gt h),
    rw h', simp, assumption,
end


lemma eq_zero_not_in (a : ℕ →₀ ℕ) (i : ℕ): a i = 0 → i ∉ a.support := begin apply imp_not_comm.1 (a.mem_support_to_fun i).1, end

lemma in_sup_ge_max : ∀ (a : ℕ →₀ ℕ) (b : ℕ), b ∈ a.support → finsupp.max a ≥ b :=
begin
    intros, unfold finsupp.max, unfold ge, apply @finset.le_sup _ _ _ _ id _ a_1,
end

lemma gt_max_ab_not_in : ∀ (a b : ℕ →₀ ℕ) (x : ℕ), (x > finsupp.max_ab a b) → x ∉ a.support ∧ x ∉ b.support :=
begin
    intros a b x h₁,
    unfold finsupp.max_ab at *, 
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

lemma max_ab_lt_add (a b w : ℕ →₀ ℕ) : finsupp.max_ab a b ≤ finsupp.max_ab (a + w) (b + w) :=
begin
    unfold finsupp.max_ab,
    have prf := λ (a b : ℕ →₀ ℕ), finset.subset.antisymm (union_support_contain a b) finsupp.support_add,
    repeat {rw [←prf] },
    rw [ finset.union_assoc, finset.union_comm b.support w.support ],
    rw [←finset.union_assoc w.support, finset.union_idempotent, 
         finset.union_comm w.support, ←finset.union_assoc],
    apply finset.nat.max_le,
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
    unfold has_le.le preorder.le finsupp.le at *,
    apply le_add,
    have h := le_of_succ_eqs a b (finsupp.max_ab a b) ((finsupp.max_ab (a + w) (b + w)) - (finsupp.max_ab a b)) hab _ ,
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

instance : is_monomial_order (ℕ →₀ ℕ) finsupp.le :=
{
    mono_order := mono_order_lem,
}

lemma finsupp.max_ab_in_a_sup_or_b_sup : Π (a b : ℕ →₀ ℕ),
    a.support ≠ ∅ ∨ b.support ≠ ∅ →
    finsupp.max_ab a b ∈ a.support 
    ∨ finsupp.max_ab a b ∈ b.support
| a b ne :=
begin
    cases ne,
    by_cases (b.support = ∅),
    unfold finsupp.max_ab, rw h, rw finset.union_empty,
    left, apply finset.nat.mem_of_sup_id, assumption,
    all_goals { apply finset.nat.union_sup_in_a_or_b, assumption, },
end

lemma eq_zero_not_finsupp.max_ab : Π (a b : ℕ →₀ ℕ) (i : ℕ),
    a (nat.succ i) = 0 → b (nat.succ i) = 0 → finsupp.max_ab a b ≠ (nat.succ i) 
| a b i eqa eqb eqi:=
begin
    unfold finsupp.max_ab at eqi,
    have ha := finsupp.eq_zero_not_in a (nat.succ i) eqa,
    have hb := finsupp.eq_zero_not_in b (nat.succ i) eqb,
    have hab := finset.not_mem_union.2 (and.intro ha hb),
    have h_nempty : (a.support ∪ b.support) ≠ ∅,
    from if h : (a.support ∪ b.support) = ∅
        then 
        begin 
            rw h at eqi, simp at eqi,
            have hi : i ≤ nat.succ i, apply nat.le_succ,
            rw [←eqi, ←lattice.eq_bot_iff, eqi] at hi,
            apply (absurd hi.symm (nat.succ_ne_self i)),
        end
        else by assumption,
    have h : (nat.succ i) ∈ (a.support ∪ b.support), 
        have h' := (finset.nat.mem_of_sup_id h_nempty), rw eqi at h', assumption,
    apply absurd h hab,
end

def finsupp_le_sup_le : Π (a b : ℕ →₀ ℕ),
    a ≤ b → finsupp.max a ≤ finsupp.max b
| a b le :=
begin
    unfold has_le.le preorder.le finsupp.le at le,
    generalize h : finsupp.max_ab a b = x,
    rw h at le,
    cases x,
    unfold finsupp.le_aux at le,
    swap,
    unfold finsupp.le_aux at le, cases le,
    rw ←h at le,
    have gt_zero := lt_of_le_of_lt (zero_le _) le,
    have neq_zero := zero_lt_iff_ne_zero.elim_left gt_zero,
    have max_ab_in_supp := finsupp.mem_support_iff.elim_right neq_zero,
    have x := finsupp.in_sup_ge_max b (finsupp.max_ab a b) max_ab_in_supp,
    have y := finsupp.max_ab_ge_max_b a b, have z := nat.le_antisymm x y,
    rw [←z], exact finsupp.max_ab_ge_max_a a b,
    /- 
    1. 0 < b (finsupp.max_ab a b)
    2. 0 < b (finsupp.max_ab a b) 
            → finsupp.max_ab a b ∈ b.support
    3. finsupp.max_ab a b ∈ b.support 
            → finsupp.max b ≥ finsupp.max_ab a b
    4. therefore, finsupp.max_ab a b = finsupp.max b (anti)
    5. finsupp.max a ≤ finsupp.max_ab a b = finsupp.max b
     -/
    rw ←h at *, cases le,
    by_cases finsupp.max_ab a b ∈ a.support;
    by_cases finsupp.max_ab a b ∈ b.support; dedup,
    any_goals { try { have x := finsupp.in_sup_ge_max a (finsupp.max_ab a b) h_1 },
                try { have y := finsupp.in_sup_ge_max b (finsupp.max_ab a b) h_2 },
                dedup,
            },
    any_goals { have z := finsupp.max_ab_ge_max_b a b, have m := nat.le_antisymm y z,
    rw [←m], exact finsupp.max_ab_ge_max_a a b },
    have q := finsupp.not_mem_support_iff.elim_left h_2, rw q at le_left,
    have b_not := finsupp.not_mem_support_iff.elim_right le_left,
    exact absurd h_1 b_not,
    apply false.elim,
    apply eq_zero_not_finsupp.max_ab a b x;
    rw h at *; try { rw ←finsupp.not_mem_support_iff }; try { assumption },
    have h' : finset.sup (a.support ∪ b.support) id = 0 := h,
    have q := finset.nat.max_le a.support b.support,
    have q' := finset.nat.max_le b.support a.support,
    rw finset.union_comm at q',
    rw h' at *, 
    have eq1 := nat.le_antisymm q (nat.zero_le _),
    have eq2 := nat.le_antisymm q' (nat.zero_le _),
    unfold finsupp.max, rw [eq1, eq2],
end

@[simp]
def max_ab_zero : Π (x : ℕ →₀ ℕ), finsupp.max_ab x 0 = finsupp.max x :=
begin
    intro x, unfold finsupp.max_ab, simp,
    trivial,
end
@[simp]
def max_ab_zero' : Π (x : ℕ →₀ ℕ), finsupp.max_ab 0 x = finsupp.max x :=
begin
    intro x, unfold finsupp.max_ab, simp,
    trivial,
end

def zero_le : Π (a : ℕ →₀ ℕ), 0 ≤ a :=
begin
    intros, apply finsupp.induction a,
    trivial, intros,
    apply le_trans _ _ _ a_4,
    rw add_comm,
    apply add_gt,
end

instance : lattice.semilattice_sup_bot (ℕ →₀ ℕ) := {
    bot := 0,
    le := finsupp.le,
    le_refl := le_refl,
    le_trans := le_trans,
    le_antisymm := le_antisymm,
    bot_le := zero_le,
    sup := max,
    le_sup_left := le_max_left,
    le_sup_right := le_max_right,
    sup_le := λ a b c, max_le
}

lemma mem_of_sup_id' : ∀ {a : finset (ℕ →₀ ℕ)}, a ≠ ∅ → a.sup id ∈ a
| a := finset.induction_on a (λ a, false.elim (a (refl _)))
    (λ x y notin ih notempty, begin 
        rw [finset.insert_eq, finset.sup_union, finset.mem_union, finset.sup_singleton],
        simp,
        from if h₁ : y = ∅ 
        then begin
            left,
            rw [h₁, finset.sup_empty, lattice.sup_bot_eq],
        end
        else begin
            from if h₂ : x < y.sup id
            then begin
                right, 
                rw [lattice.sup_of_le_right (le_of_lt h₂)],
                apply ih h₁,
            end
            else begin
                left,                
                rw [lattice.sup_of_le_left (le_of_not_lt h₂)],
            end
        end
    end)

def neq_zero_gt_zero : Π (x : ℕ →₀ ℕ), x ≠ 0 → 0 < x :=
begin
    intros,
    have m := @lt_or_eq_of_le _ _ 0 x (zero_le _),
    cases m, assumption, rw m at *, apply false.elim,
    apply a, trivial,
end

def single_inj1 : Π {a b: δ} {c d: γ}, (c ≠ 0) → single a c = single b d → a = b :=
begin
    intros, unfold single at *, simp at a_1,
    by_cases c = 0, rw h at *, simp at *,
    apply false.elim; assumption,
    simp [a_1] at a_2,
    by_cases d = 0, rw h at *, simp at *,
    apply false.elim; assumption,
    simp [a_1, h] at a_2,
    cases a_2, rw finset.singleton_inj at a_2_left,
    assumption,
end

def single_inj2 : Π (a b: δ) (c d: γ), single a c = single b d → c = d :=
begin
    intros, unfold single at *, simp at a_1,
    by_cases c = 0; rw h at *;
    by_cases d = 0; rw h at *,
    simp [h] at *, cases a_1, 
    unfold finset.singleton has_emptyc.emptyc finset.empty at a_1_left,
    simp at a_1_left, apply false.elim, assumption,
    tactic.unfreeze_local_instances, dedup, simp [h] at a_1,
    apply false.elim, assumption,
    tactic.unfreeze_local_instances, dedup, simp [h, h_1] at a_1,
    cases a_1, rw finset.singleton_inj at a_1_left,
    rw a_1_left at *, let m := congr_fun a_1_right b,
    simp at m, assumption,
end

def coe_f : Π (a : δ →₀ γ) (n : δ), a n = a.to_fun n := λ a n, rfl
-- protected def wf_lt : well_founded (@finsupp.has_lt.1) := sorry

end finsupp