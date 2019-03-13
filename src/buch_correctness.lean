import buchberger util seq

open mv_polynomial
open finsupp

namespace buch
variables {σ : Type*} {α : Type*} [decidable_eq σ] [decidable_eq α] [fintype σ] [decidable_linear_order (σ →₀ ℕ)] 
variables [discrete_field α] [is_well_founded (σ →₀ ℕ) (<)] [is_monomial_order (σ →₀ ℕ) (≤)] 

section reduction
variables (S : finset (mv_polynomial σ α))

/-
inductive red_one_step' : mv_polynomial σ α → mv_polynomial σ α → Prop
| trans : ∀ p r : mv_polynomial σ α, red_one_step' p.tl r.tl → p.lm = r.lm → p.lc = r.lc → red_one_step' p r
| red : ∀ p r : mv_polynomial σ α, (∃ (q : mv_polynomial σ α) (h₁ : q ∈ S) (h₂ : q.lm ∣ p.lm), reduction p q = r) → red_one_step' p r
-/

inductive red_one_step : mv_polynomial σ α → mv_polynomial σ α → Prop
| trans {a b} : ∀ p r : mv_polynomial σ α, red_one_step p r → a > p.lm → b ≠ 0
    → red_one_step ((monomial a b) + p) ((monomial a b) + r)
| base {a b} : ∀ p r : mv_polynomial σ α, a > p.lm → b ≠ 0 → 
    (∃ (q : mv_polynomial σ α) (h₁ : q ∈ S) (h₂ : q.lm ∣ a), reduction (monomial a b + p) q = r)
    → red_one_step ((monomial a b) + p) r

def reducible (p : mv_polynomial σ α) :=
    ∃ (q : mv_polynomial σ α) (hq : q ∈ S) (pₜ : σ →₀ ℕ) (hp : pₜ ∈ p.support), q.lm ∣ pₜ

notation a `→[` S `]` b := red_one_step S a b
notation a `↛[` S `]` b := ¬ red_one_step S a b

def red_plus : mv_polynomial σ α → mv_polynomial σ α → Prop := rtc (red_one_step S)
notation a `→[` S `]+` b := red_plus S a b
notation a `↛[` S `]+` b := ¬ red_plus S a b

def irreducible (p : mv_polynomial σ α) := ∀ (q : mv_polynomial σ α) (hq : q ∈ S) (pₜ ∈ p.support), q.lm ∤ pₜ

notation a `→[` S `]*` b := red_plus S a b ∧ irreducible S b

instance irreducible_decidable (p : mv_polynomial σ α) : decidable (irreducible S p) := finset.decidable_dforall_finset
instance reducible_decidable (p : mv_polynomial σ α) : decidable (reducible S p) := finset.decidable_dexists_finset

@[simp] lemma irred_not_red {p : mv_polynomial σ α} : irreducible S p ↔ ¬ reducible S p := by simp [irreducible, reducible]
lemma red_not_irred {p : mv_polynomial σ α} : ¬ irreducible S p ↔ reducible S p := by simp [irred_not_red]

lemma zero_irreducible : irreducible S 0 := by simp [irreducible]
lemma nez_of_not_irred {p : mv_polynomial σ α} (h : reducible S p) : p ≠ 0 := 
λ h', ((red_not_irred S).2 h) (by simp [h', zero_irreducible])

lemma red_one_step_reducible {p r : mv_polynomial σ α} (h : p →[S] r) : reducible S p :=
begin
    induction h with a b p r h₁ h₂ hb ih a b p r ha hb h,
    {
        rcases ih with ⟨q, ⟨hq, ⟨pₜ, ⟨hp, hpq⟩⟩⟩⟩,
        refine ⟨q, ⟨hq, ⟨pₜ, ⟨_, hpq⟩⟩⟩⟩,
        by_cases hb : b = 0,
        {simpa [hb] using hp},
        {simp [-mem_support_iff, -add_comm, support_add_eq (not_mem_disjoint (gt_lm_not_mem h₂) hb), hp]},
    },
    {
        rcases h with ⟨q, ⟨hq, ⟨hpq, _⟩⟩⟩,
        refine ⟨q, ⟨hq, ⟨a, ⟨_, hpq⟩⟩⟩⟩,
        rw [support_add_eq (not_mem_disjoint (gt_lm_not_mem ha) hb)],
        simp [support_monomial_eq hb], 
    }
end

lemma red_one_step_lm_ge {p r : mv_polynomial σ α} (h : p →[S] r) : p.lm ≥ r.lm :=
begin
    induction h with a b p r h₁ ha hb ih a b p r ha hb h₂,
    rw [lm_of_add_gt_lm ha hb, lm_of_add_gt_lm (lt_of_le_of_lt ih ha) hb], exact le_refl _,
    rcases h₂ with ⟨q, ⟨h₁, ⟨h₂, h₃⟩⟩⟩,
    rw ←h₃,
    by_cases hq : q = 0,
    simp [reduction, hq], exact le_refl _,
    apply le_of_lt (reduction_lm_lt _ _ hq);
    rwa [lm_of_add_gt_lm ha hb], apply ne_zero_of_gt ha,
end

lemma red_one_step_cases {p r : mv_polynomial σ α} (h : p →[S] r) : 
(p.lm = r.lm ∧ p.lc = r.lc ∧ (p.tl →[S] r.tl)) ∨ 
(∃ (q : mv_polynomial σ α) (h₁ : q ∈ S) (h₂ : q.lm ∣ p.lm), reduction p q = r) := 
begin
    cases h with a b p r h₁ ha hb a b p _ ha hb h₂,
    {
        conv at h {change ((monomial a b + p) →[S] (monomial a b + r))},
        change 
            ((monomial a b + p).lm = (monomial a b + r).lm ∧ (monomial a b + p).lc = (monomial a b + r).lc ∧ 
                ((monomial a b + p).tl →[S] (monomial a b + r).tl)) ∨ 
            ((∃ (q : mv_polynomial σ α) (h₁ : q ∈ S) (h₂ : q.lm ∣ (monomial a b + p).lm), 
                reduction (monomial a b + p) q = monomial a b + r)),
        left,
        have ha' := lt_of_le_of_lt (red_one_step_lm_ge S h₁) ha,
        rw [lm_of_add_gt_lm ha hb, lm_of_add_gt_lm ha' hb, lc_of_add_gt_lm ha hb, lc_of_add_gt_lm ha' hb,
            tl_of_add_gt_lm ha hb, tl_of_add_gt_lm ha' hb],
        simp [h₁],
    },
    {
        conv at h {change ((monomial a b + p) →[S] r)},
        change 
            ((monomial a b + p).lm = r.lm ∧ (monomial a b + p).lc = r.lc ∧ 
                ((monomial a b + p).tl →[S] r.tl)) ∨ 
            ((∃ (q : mv_polynomial σ α) (h₁ : q ∈ S) (h₂ : q.lm ∣ (monomial a b + p).lm), 
                reduction (monomial a b + p) q = r)),
        right,
        rwa [lm_of_add_gt_lm ha hb],
    }
end

lemma red_comp_minus (p q r : mv_polynomial σ α) (h : (p - q)→[S] r) :
    ∃ p' q', (p →[S]+ p') ∧ (q →[S]+ q') ∧ r = p' - q' :=
begin
    
end

lemma red_plus_irreducible {p q : mv_polynomial σ α} (hp : irreducible S p) (h : p →[S]+ q) : q = p :=
begin
    induction h with p₁ p₂ q₂ h p₃ q₃ r₃ hpq hqr hih₁ hih₂,
    refl,
    rcases (red_one_step_reducible S h) with ⟨q, ⟨hq, ⟨pₜ, ⟨hpₜ, hpq⟩⟩⟩⟩,
    apply absurd hpq (hp q hq pₜ hpₜ),
    simpa [hih₁ hp, hp] using hih₂,
end

lemma red_irreducible {p q : mv_polynomial σ α} (hp : irreducible S p) (h : p →[S]* q) : q = p :=
begin
    rcases h with ⟨h₁, h₂⟩,
    apply red_plus_irreducible S hp h₁,
end

lemma red_plus_trans {p r : mv_polynomial σ α} (h : p →[S]+ r) : r ≠ p → ∃ q, (p →[S] q) ∧ (q →[S]+ r) :=
begin
    induction h with _ p₂ r₂ h p₃ q₃ r₃ h₁ h₂ ih₁ ih₂, 
    {simp},
    {intro, use [r₂, h, rtc.refl _ _]},
    {
        by_cases q₃ = p₃, 
        {rwa ←h},
        {
            intro,
            rcases ih₁ h with ⟨t, ⟨ht₁, ht₂⟩⟩,
            use [t, ht₁, rtc.trans _ _ _ ht₂ h₂],
        }
    }
end

lemma red_star_trans {p r : mv_polynomial σ α} (h : p →[S]* r) : reducible S p → ∃ q, (p →[S] q) ∧ (q →[S]* r) := 
begin
    cases h with h₁ h₂, revert h₂, 
    induction h₁ with p₁ p₂ r₂ h₁ p₃ q₃ r₃ h₁ h₂ ih₁ ih₂, 
    {simp_intros h₂ h₃, apply absurd h₃ h₂}, 
    {simp_intros h₂ h₃, use [r₂, h₁, rtc.refl _ _, h₂]},
    {
        intros hr hp,
        by_cases hq : irreducible S q₃,
        {
            rcases ih₁ hq hp with ⟨t, ⟨ht₁, ht₂⟩⟩, 
            use [t, ht₁, by rwa red_plus_irreducible S hq h₂],
        },
        {
            by_cases hpq : q₃ = p₃, 
            {rw ←hpq, apply ih₂ hr (by rwa ←red_not_irred)},
            rcases red_plus_trans S h₁ hpq with ⟨t, ⟨ht₁, ht₂⟩⟩, 
            use [t, ht₁, rtc.trans _ _ _ ht₂ h₂, hr],
        }
    }
end

lemma red_confluent (p : mv_polynomial σ α) : ∀ r t, (p →[S]* r) → (p →[S]* t) → r = t :=
begin
    apply induction p, sorry,
    intros p ih r t hpr hpt,
    by_cases hp : irreducible S p,
    simp [red_irreducible S hp hpr, red_irreducible S hp hpt],
    rcases red_star_trans S hpr (by simpa using hp) with ⟨q₁, ⟨hqr₁, hqr₂⟩⟩,
    rcases red_star_trans S hpt (by simpa using hp) with ⟨q₂, ⟨hqt₁, hqt₂⟩⟩,
    cases red_one_step_cases S hqr₁; cases red_one_step_cases S hqt₁,
    {
        
    },
end

/-
lemma red_zero (r : mv_polynomial σ α) (h : 0 →[S] r) : r = 0 :=
begin
    cases h with r _ _ _ h₃ _ _ h,
    simp [lc_eqz_iff, h₃.symm],
    simp [reduction] at h,
    rcases h with ⟨_, ⟨_, ⟨_, h⟩⟩⟩,
    exact h.symm,
end

lemma red_diff_mem {p r : mv_polynomial σ α} (hpr : p ≠ r) (h : p →[S] r) : (p - r).lm ∈ p.support := begin
    induction h with p' r' h₁ h₂ h₃ ih p' r' h,
    rw [←lm_tl_eq p', ←lm_tl_eq r', ←h₂, ←h₃] at ⊢ hpr,
    simp [-mem_support_iff] at ⊢ hpr,
    apply finset.mem_of_subset _ (ih hpr),
    rw [add_comm, lm_tl_eq p'], 
    simp [tl, finset.erase_subset],

    rcases h with ⟨q, ⟨h₁, ⟨h₂, h₃⟩⟩⟩,
    have hp : p' ≠ 0 := λ h, hpr (by simp [reduction, h, h₃.symm]),
    have hq : q ≠ 0 := λ h, hpr (by simp [reduction, h, h₃.symm]),
    conv in (lm _) {
        simp [reduction, h₃.symm, 
        lm_of_mul_m hq (div_ne_zero (lc_nez_iff.1 hp) (lc_nez_iff.1 hq)), add_sub_cancel' h₂],
    },
    exact lm_mem_support hp,
end
-/

/-


lemma red_monomial (p r : mv_polynomial σ α) (h : p →[S] r) :
∃ (q : mv_polynomial σ α) (hq : q ∈ S), q.lm ∣ (p - r).lm := begin
    induction h,
    conv in (h_p - h_r) {
        rw [←lm_tl_eq h_p, ←lm_tl_eq h_r, h_h₂, h_h₃],
        simp, rw ←sub_eq_add_neg,
    }, assumption,
    rcases h_a with ⟨q, ⟨h₁, ⟨h₂, h₃⟩⟩⟩,
    refine ⟨q, ⟨h₁, _⟩⟩,
    by_cases hp : h_p = 0,
    simpa [hp, reduction, h₃.symm] using h₂,
    by_cases hq : q = 0,
    simp [hq],
    simp [h₃.symm, reduction, lm_of_mul_m hq (div_ne_zero (lc_nez_iff.1 hp) (lc_nez_iff.1 hq))],
end



lemma red_comp_minus (p q r : mv_polynomial σ α) (h : p - q →[S] r) :
    ∃ p' q', (p →[S] p') ∧ (q →[S] q') ∧ r = p' - q' :=
begin
    --generalize ht : p - q = t, rw ht at h,
    --rw [sub_eq_iff_eq_add.1 ht], clear ht p,
    --induction h with p r,
end

lemma red_of_add_right (p q r : mv_polynomial σ α) (h : p →[S]+ r) : p + q →[S]+ r + q :=
begin

end

lemma red_plus_minus (p r : mv_polynomial σ α) (hpt : p →[S]+ r)
: r = 0 → ∀ q t, (q →[S]+ t) → ((p + q) →[S]+ t) :=
begin

end

lemma red_confluent (h : ∀ (p q r), (p→[S]*q) → (p→[S]*r) → q = r) : 
∀ p ∈ ideal.span (↑S : set (mv_polynomial σ α)), p →[S]* 0 := 
λ p, begin
    

end
-/
end reduction

end buch