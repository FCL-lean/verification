import buchberger rtc wf_mv_polynomial

open mv_polynomial
open finsupp

namespace buch
variables {σ : Type*} {α : Type*} [decidable_eq σ] [decidable_eq α] [fintype σ] [decidable_linear_order (σ →₀ ℕ)] 
variables [discrete_field α] [is_well_founded (σ →₀ ℕ) (<)] [is_monomial_order (σ →₀ ℕ) (≤)] 

section reduction
variables (s : finset (mv_polynomial σ α)) {S : finset (mv_polynomial σ α)}

inductive red_one_step : mv_polynomial σ α → mv_polynomial σ α → Prop
| cons : ∀ {p r : mv_polynomial σ α}, p ≠ 0 → red_one_step p.TL r.TL → p.LT = r.LT → red_one_step p r
| red_LM : ∀ {p r : mv_polynomial σ α}, p ≠ 0 → 
    (∃ (q : mv_polynomial σ α) (h₁ : q ∈ s) (h₂ : q ≠ 0)  (h₃ : q.LM ∣ p.LM), reduction p q = r) → red_one_step p r

def reducible (p : mv_polynomial σ α) :=
    ∃ (q : mv_polynomial σ α) (hq₁ : q ∈ s) (hq₂ : q ≠ 0) (pₜ : σ →₀ ℕ) (hp : pₜ ∈ p.support), q.LM ∣ pₜ
def is_red_rel (p r : mv_polynomial σ α) :=
    ∃ (q : mv_polynomial σ α) (hq₁ : q ∈ s) (hq₂ : q ≠ 0) (pₜ : σ →₀ ℕ) (hp : pₜ ∈ p.support) (hqpₜ : q.LM ∣ pₜ), 
        r = p - q * monomial (pₜ - q.LM) (p pₜ / q.LC)

notation a `→[` S `]` b := red_one_step S a b
notation a `↛[` S `]` b := ¬ red_one_step S a b

def red_plus : mv_polynomial σ α → mv_polynomial σ α → Prop := rtc (red_one_step s)
notation a `→[` S `]+` b := red_plus S a b
notation a `↛[` S `]+` b := ¬ red_plus S a b

def irreducible (p : mv_polynomial σ α) := ∀ (q : mv_polynomial σ α) (hq₁ : q ∈ s) (hq₂ : q ≠ 0) (pₜ ∈ p.support), q.LM ∤ pₜ

notation a `→[` S `]*` b := red_plus S a b ∧ irreducible S b

instance irreducible_decidable (p : mv_polynomial σ α) : decidable (irreducible s p) := finset.decidable_dforall_finset
instance reducible_decidable (p : mv_polynomial σ α) : decidable (reducible s p) := finset.decidable_dexists_finset

@[simp] lemma irred_not_red {p : mv_polynomial σ α} : irreducible s p ↔ ¬ reducible s p := by simp [irreducible, reducible]
lemma red_not_irred {p : mv_polynomial σ α} : ¬ irreducible s p ↔ reducible s p := by simp [irred_not_red]

lemma zero_irreducible : irreducible S 0 := by simp [irreducible]
lemma zero_not_reducible : ¬ reducible S 0 := by rw ←irred_not_red; exact zero_irreducible
lemma zero_not_is_red_rel : ∀ {r}, ¬ is_red_rel S 0 r := by simp [is_red_rel]

lemma red_one_step_is_red_rel {p r : mv_polynomial σ α} : (p →[S] r) ↔ is_red_rel S p r :=
⟨λ h, begin
    induction h with p r hp hpr₁ hpr₂ ih p r hp h,
    {
        rcases ih with ⟨q, hq₁, hq₂, pₜ, hpₜ, hqpₜ, h⟩,
        rw [←@add_left_cancel_iff _ _ p.LT, ←add_sub_assoc, LM_TL_eq p, hpr₂, LM_TL_eq r, TL_apply_mem hpₜ] at h,
        refine ⟨q, hq₁, hq₂, pₜ, TL_support_subset hpₜ, hqpₜ, h⟩,
    },
    {
        rcases h with ⟨q, hq₁, hq₂, hpq, h⟩,
        refine ⟨q, hq₁, hq₂, p.LM, LM_mem_support hp, hpq, by rw ←h; refl⟩,
    }
end, begin 
    revert r,
    apply induction p,
    {intros r hr, apply absurd hr zero_not_is_red_rel},
    {
        intros p ih r hr,
        rcases hr with ⟨q, hq₁, hq₂, pₜ, hpₜ, hqpₜ, h⟩,
        by_cases hpₜp : pₜ = p.LM,
        {
            apply red_one_step.red_LM (nez_of_mem_support hpₜ), 
            refine ⟨q, hq₁, hq₂, by rwa ←hpₜp, by rw [h, hpₜp]; refl,⟩,
        },
        {
            have hp_LM : p.LM > (-(q * monomial (pₜ - LM q) (p pₜ / LC q))).LM,
            {
                simp [LM_of_mul_m, hq₂, div_ne_zero (mem_support_iff.1 hpₜ) (LC_nez_iff.1 hq₂), add_sub_cancel' hqpₜ],
                apply lt_of_le_of_ne (LM_rel' hpₜ) hpₜp
            },
            have hr : p.LT = r.LT := by simp [LT, h, LM_of_add_left hp_LM, LC_of_add_left hp_LM],
            
            apply red_one_step.cons (nez_of_mem_support hpₜ) (ih ⟨q, hq₁, hq₂, pₜ, mem_TL_support hpₜp hpₜ, hqpₜ, _⟩) hr,
            {
                rw [←@add_left_cancel_iff _ _ p.LT, ←add_sub_assoc, LM_TL_eq p, hr, LM_TL_eq r, TL_apply pₜ],
                simpa [ne.symm hpₜp] using h,
            },
        }
    }
end⟩

lemma is_red_rel_reducible {p r : mv_polynomial σ α} (h : is_red_rel S p r) : reducible S p :=
begin
    rcases h with ⟨q, hq₁, hq₂, pₜ, hpₜ, hqpₜ, _⟩,
    refine ⟨q, hq₁, hq₂, pₜ, hpₜ, hqpₜ⟩,
end

lemma reducible_is_red_rel {p : mv_polynomial σ α} (h : reducible S p) : ∃ r, is_red_rel S p r :=
begin
    rcases h with ⟨q, hq₁, hq₂, pₜ, hpₜ, hqpₜ⟩,
    refine ⟨p - q * monomial (pₜ - q.LM) (p pₜ / q.LC), q, hq₁, hq₂, pₜ, hpₜ, hqpₜ, rfl⟩,
end

lemma zero_red {r : mv_polynomial σ α} : (0 : mv_polynomial σ α) ↛[s] r  :=
λ h, zero_not_reducible (is_red_rel_reducible (by rwa red_one_step_is_red_rel at h))

lemma red_mem_S {q : mv_polynomial σ α} (hq₁ : q ∈ S) (hq₂ : q ≠ 0) : q →[S] 0 :=
begin
    rw red_one_step_is_red_rel,
    refine ⟨q, hq₁, hq₂, q.LM, LM_mem_support hq₂, by simp, _⟩,
    have h₁ : q q.LM = q.LC := rfl,
    have h₂ : (monomial 0 1 : mv_polynomial σ α) = C 1 := by simp [C],
    simp [h₁, div_self (LC_nez_iff.1 hq₂), h₂],
end

theorem red_plus_mul {p r : mv_polynomial σ α} (h : p →[S]+ r) : 
    ∀ a b, (monomial a b * p) →[S]+ (monomial a b * r) :=
begin
    intros a b,
    by_cases hb : b = 0,
    {simp [hb], exact rtc.refl'},
    {
        revert a b,
        induction h with p p r h p q r hpq hqr ih₁ ih₂;
        intros a b hb,
        {exact rtc.refl'},
        {
            apply rtc.base',
            rw red_one_step_is_red_rel at h ⊢,
            rcases h with ⟨q, hq₁, hq₂, pₜ, hp, hpq, h⟩,
            refine ⟨q, hq₁, hq₂, a + pₜ, mul_mem_mul_support hb _ hp, dvd_of_dvd_of_add' hpq _, 
                by rw [mul_apply hp, finsupp.add_sub_assoc' hpq, mul_div_assoc, ←monomial_mul_monomial, 
                mul_left_comm, ←mul_sub, h]⟩,
        },
        {exact rtc.trans' (ih₁ a b hb) (ih₂ a b hb)}
    }
end

lemma red_plus_zero_of_mul {p : mv_polynomial σ α} (h : p →[S]+ 0) : 
    ∀ a b, (monomial a b * p) →[S]+ 0 := by simpa using red_plus_mul h

lemma red_star_zero_of_mul {p : mv_polynomial σ α} (h : p →[S]* 0) : 
    ∀ a b, (monomial a b * p) →[S]* 0 := λ a b, ⟨red_plus_zero_of_mul h.left a b, zero_irreducible⟩

lemma lt_of_red_one_step {p r : mv_polynomial σ α} (h : p →[S] r) : r < p :=
begin
    induction h with p r hp h₁ h₂ ih p r hp h, 
    {apply lt.LM_eq hp h₂.symm ih},
    {
        rcases h with ⟨q, h₁, h₂, h₃, h₄⟩,
        rw ←h₄,
        by_cases hp' : p.LM = 0,
        {
            simp [hp'] at h₃,
            rw reduction_of_LM_eqz hp' h₃ h₂,
            apply lt.zero hp,
        },
        {apply lt.LM_lt (reduction_LM_lt h₃ hp' h₂)}
    }
end

lemma le_of_red_plus {p r : mv_polynomial σ α} (h : p →[S]+ r) : r < p ∨ r = p :=
begin
    induction h with _ _ _ h p q r hpq hqr ih₁ ih₂,
    {simp},
    {left, apply lt_of_red_one_step h},
    {
        cases ih₁; cases ih₂,
        {left, exact trans ih₂ ih₁},
        {left, rwa ih₂},
        {left, rwa ←ih₁},
        {right, rwa ih₂},
    }
end

lemma red_lt_of_le_of_lt {p q r : mv_polynomial σ α} (hpq : p →[S] q) (hqr : q →[S]+ r) : r < p :=
begin
    cases le_of_red_plus hqr,
    {exact trans h (lt_of_red_one_step hpq)},
    {simpa [h] using lt_of_red_one_step hpq}
end

lemma red_lt_of_le_of_lt' {p q r : mv_polynomial σ α} (hpq : p →[S] q) (hqr : q →[S]* r) : r < p :=
red_lt_of_le_of_lt hpq hqr.left

lemma red_one_step_LM_ge {p r : mv_polynomial σ α} (h : p →[S] r) : p.LM ≥ r.LM := LM_le_of_lt (lt_of_red_one_step h)
lemma red_plus_LM_ge {p r : mv_polynomial σ α} (h : p →[S]+ r) : p.LM ≥ r.LM :=
begin
    induction h with _ _ _ h _ _ _ _ _ ih₁ ih₂,
    {exact le_refl _},
    {exact red_one_step_LM_ge h},
    {exact ge_trans ih₁ ih₂},
end

lemma red_plus_irreducible {p q : mv_polynomial σ α} (hp : irreducible S p) (h : p →[S]+ q) : q = p :=
begin
    induction h with _ p q h p q r hpq hpr ih₁ ih₂, 
    {refl},
    {apply absurd (is_red_rel_reducible (by rwa red_one_step_is_red_rel at h)) (by simpa using hp)},
    {simpa [ih₁ hp, hp] using ih₂},
end

theorem red_star_irreducible {p q : mv_polynomial σ α} (hp : irreducible S p) (h : p →[S]* q) : q = p :=
red_plus_irreducible hp h.left

lemma red_const {p r : mv_polynomial σ α} (hp : p.LM = 0) (h : p →[S] r) : r = 0 :=
begin
    cases h with _ _ _ h _ _ _ hp' h,
    {apply absurd (by rwa TL_eqz_of_LM_eqz hp at h) (zero_red _)},
    {
        rcases h with ⟨q, h₁, h₂, h₃, h₄⟩,
        simp [hp] at h₃, 
        rw ←h₄,
        exact reduction_of_LM_eqz hp h₃ h₂,
    }
end

lemma red_plus_const {p r : mv_polynomial σ α} (hp : p.LM = 0) (h : p →[S]+ r) : p = r ∨ r = 0 :=
begin
    induction h with _ p r h p q r hpq hqr ih₁ ih₂,
    {simp},
    {simp [red_const hp h]},
    {
        cases ih₁ hp,
        {
            rw ←h at ih₂, 
            exact ih₂ hp,
        },
        {
            right,
            conv at ih₂ in (_ ∨ _) {rw eq_comm},
            simpa [h] using ih₂, 
        }
    }
end

lemma red_star_const {p r : mv_polynomial σ α} (hp : p.LM = 0) (h : p →[S]* r) : p = r ∨ r = 0 :=
red_plus_const hp h.left

lemma red_plus_trans {p r : mv_polynomial σ α} (h : p →[S]+ r) : p ≠ r → ∃ q, (p →[S] q) ∧ (q →[S]+ r) :=
begin
    induction h with _ p₂ r₂ h p₃ q₃ r₃ h₁ h₂ ih₁ ih₂, 
    {simp},
    {intro, use [r₂, h, rtc.refl']},
    {
        by_cases p₃ = q₃,
        {rwa h},
        {
            intro,
            rcases ih₁ h with ⟨t, ht₁, ht₂⟩,
            use [t, ht₁, rtc.trans' ht₂ h₂],
        } 
    }
end

lemma red_star_trans {p r : mv_polynomial σ α} (h : p →[S]* r) : reducible S p → ∃ q, (p →[S] q) ∧ (q →[S]* r) := 
λ hp, by simpa [h.right] using red_plus_trans h.left (λ hpr, ((irred_not_red S).1 h.right) (by rwa hpr at hp))

lemma exists_red_star (p : mv_polynomial σ α) : ∃ r, p →[s]* r :=
@well_founded.recursion (mv_polynomial σ α) (<) lt_wf _ p 
(begin
    intros p ih,
    by_cases hp : irreducible s p,
    {use [p, rtc.refl', hp]},
    {
        cases reducible_is_red_rel (by rwa ←red_not_irred) with q hq,
        rw ←red_one_step_is_red_rel at hq,
        rcases ih q (lt_of_red_one_step hq) with ⟨r, hr₁, hr₂⟩,
        refine ⟨r, rtc.base_trans hq hr₁, hr₂⟩,
    }
end)

lemma exists_red_star_of_red {p q : mv_polynomial σ α} (h : p →[S] q) : 
∃ r, (q →[S]* r) ∧ (p →[S]* r) :=
begin
    rcases exists_red_star S q with ⟨r, hr₁, hr₂⟩,
    refine ⟨r, ⟨hr₁, hr₂⟩, ⟨rtc.base_trans h hr₁, hr₂⟩⟩,
end

lemma exists_red_star_of_red_plus {p q : mv_polynomial σ α} (h : p →[S]+ q) : 
∃ r, (q →[S]* r) ∧ (p →[S]* r) :=
begin
    induction h with p p q h p₃ q₃ r₃ hpq hqr ih₁ ih₂,
    {
        cases exists_red_star S p with r h,
        use [r, h, h],
    },
    {exact exists_red_star_of_red h},
    {
        rcases ih₂ with ⟨r, hr₁, ⟨hr₂, hr₃⟩⟩,
        use [r, hr₁, ⟨rtc.trans' hpq hr₂, hr₃⟩],
    }
end

lemma red_m_not_mem {p q r : mv_polynomial σ α} (hq : q ≠ 0) {pₜ} (hpₜ : pₜ ∈ p.support) 
(hqpₜ : q.LM ∣ pₜ) (h : r = p - q * monomial (pₜ - q.LM) (p pₜ / q.LC)) : pₜ ∉ r.support :=
begin
    have h_LC : (q * monomial (pₜ - LM q) (p pₜ / LC q)) pₜ = (q * monomial (pₜ - LM q) (p pₜ / LC q)).LC,
        have h₁ : p pₜ / q q.LM ≠ 0 := div_ne_zero (by simpa using hpₜ) (LC_nez_iff.1 hq),
        simp [LC, LM_of_mul_m, hq, h₁, finsupp.add_sub_cancel' hqpₜ], refl,
    simp [h, h_LC, LC_of_mul_m, mul_div_cancel' _ (LC_nez_iff.1 hq)],
end

lemma sub_red_comp {p r : mv_polynomial σ α} (h : p →[S] r) :
∀ u, ∃ t₁ t₂, (p + u →[S]+ t₁) ∧ (u →[S]+ t₂) ∧ (r = t₁ - t₂) :=
λ u, begin
    rcases red_one_step_is_red_rel.1 h with ⟨q, hq₁, hq₂, pₜ, hpₜ, hqpₜ, h⟩,
    have hr := red_m_not_mem hq₂ hpₜ hqpₜ h,
    by_cases hpₜu : pₜ ∈ u.support;
    simp at hpₜu hr hpₜ,
    {
        by_cases hpₜ': pₜ ∈ (p + u).support,
        {
            refine ⟨p + u - q * monomial (pₜ - LM q) ((p + u) pₜ / LC q), 
                u - q * monomial (pₜ - LM q) (u pₜ / LC q), 
                rtc.base' (red_one_step_is_red_rel.2 ⟨q, hq₁, hq₂, pₜ, hpₜ', hqpₜ, rfl⟩),
                rtc.base' (red_one_step_is_red_rel.2 ⟨q, hq₁, hq₂, pₜ, by simpa using hpₜu, hqpₜ, rfl⟩), _⟩,
            {
                simp [-mul_neg_eq_neg_mul_symm, neg_mul_eq_mul_neg],
                rw [←mul_add, ←monomial_neg, ←neg_div, ←monomial_add_monomial, 
                div_add_div_same, neg_add_rev, ←add_assoc],                
                simp [neg_div, h],
            }
        },
        {
            simp [add_eq_zero_iff_neg_eq] at hpₜ',
            refine ⟨p + u, u - q * monomial (pₜ - LM q) (u pₜ / LC q), rtc.refl', 
                rtc.base' (red_one_step_is_red_rel.2 ⟨q, hq₁, hq₂, pₜ, by simpa using hpₜu, hqpₜ, rfl⟩),
                by simp [hpₜ'.symm, neg_div, h]⟩,
        }
    },
    {
        refine ⟨p + u - q * monomial (pₜ - q.LM) ((p + u) pₜ/ q.LC), u, 
            rtc.base' (red_one_step_is_red_rel.2 ⟨q, hq₁, hq₂, pₜ, by simpa [hpₜu] using hpₜ, hqpₜ, rfl⟩),
            rtc.refl', by simp [hpₜu, h]⟩,
    }
end

lemma sub_red_plus_comp {p r : mv_polynomial σ α} (h : p →[S]+ r) :
∀ u, ∃ t, (p + u →[S]+ r + t) ∧ (u →[S]+ t) :=
begin
    induction h with r p r h p q r hpq hqr ih₁ ih₂;
    intros u,
    {refine ⟨u, rtc.refl', rtc.refl'⟩},
    {
        rcases sub_red_comp h u with ⟨t₁, t₂, h₁, h₂, h₃⟩, 
        refine ⟨t₂, by rwa eq_sub_iff_add_eq.1 h₃, h₂⟩,
    },
    {
        rcases ih₁ u with ⟨t₁, hput₁, hut₁⟩,
        rcases ih₂ t₁ with ⟨t₂, hqut₂, hut₂⟩,
        refine ⟨t₂, rtc.trans' hput₁ hqut₂, rtc.trans' hut₁ hut₂⟩,
    }
end

lemma sub_red_star_zero {p q : mv_polynomial σ α} (h : p - q →[S]* 0) :
∃ t, (p →[S]* t) ∧ (q →[S]* t) :=
begin
    rcases sub_red_plus_comp h.left q with ⟨r, hpr, hqr⟩,
    rcases exists_red_star S r with ⟨t, ht₁, ht₂⟩,
    refine ⟨t, ⟨rtc.trans' (by simpa using hpr) ht₁, ht₂⟩, ⟨rtc.trans' hqr ht₁, ht₂⟩⟩,
end

lemma red_add_of_red {p r : mv_polynomial σ α} (h : p →[S] r) : 
∀ u, ∃ t, (p + u →[S]+ t) ∧ (r + u →[S]+ t) :=
λ u, begin
    rcases red_one_step_is_red_rel.1 h with ⟨q, hq₁, hq₂, pₜ, hpₜ, hqpₜ, h⟩,
    have hr := red_m_not_mem hq₂ hpₜ hqpₜ h,
    by_cases hpₜu : pₜ ∈ u.support;
    simp at hpₜu hr,
    {
        by_cases hpₜ': pₜ ∈ (p + u).support,
        {
            refine ⟨r + u - q * monomial (pₜ - LM q) (u pₜ / LC q), _, _⟩;
            apply rtc.base'; rw [red_one_step_is_red_rel],
            {
                conv at h {
                    rw [←@add_right_cancel_iff _ _ (u - q * monomial (pₜ - q.LM) (u pₜ / q.LC)), ←add_sub_assoc],
                    to_rhs, rw [←add_sub_assoc, sub_add_eq_add_sub, sub_sub, ←mul_add, ←monomial_add_monomial, div_add_div_same, ←add_apply],
                },
                refine ⟨q, hq₁, hq₂, pₜ, hpₜ', hqpₜ, by rw h⟩,
            },
            {refine ⟨q, hq₁, hq₂, pₜ, by simpa [hr] using hpₜu, hqpₜ, by conv in ((r + u) pₜ) {simp [hr]},⟩}
        },
        {
            refine ⟨p + u, rtc.refl', _⟩,
            apply rtc.base',
            rw red_one_step_is_red_rel,
            refine ⟨q, hq₁, hq₂, pₜ, by simpa [hr] using hpₜu, hqpₜ, _⟩,
            simp [add_eq_zero_iff_eq_neg] at hpₜ',
            simp [h, hpₜ', neg_div, hr],
        }
    },
    {
        refine ⟨r + u, _, rtc.refl'⟩,
        apply rtc.base',
        rw [red_one_step_is_red_rel, h, sub_add_eq_add_sub],
        refine ⟨q, hq₁, hq₂, pₜ, by simpa [hpₜu] using hpₜ, hqpₜ, by simp [hpₜu]⟩,
    }
end

lemma red_of_TL_red {p r : mv_polynomial σ α} (h : p.TL →[S] r) :
p →[S] p.LT + r :=
begin
    by_cases hp : p.LM = 0,
    {
        rw [TL_eqz_of_LM_eqz hp] at h,
        apply absurd h (zero_red _),
    },
    {
        have hpr := gt_of_gt_of_ge (gt_TL_LM_of_LM_nez hp) (red_one_step_LM_ge h),
        apply red_one_step.cons (nez_of_LM_nez hp) (by rwa ←TL_of_add_gt_LM hpr (LC_nez_of_LM_nez hp) at h),
        simp [LT_of_add_right (by rwa eq_LM_of_monomial p.LM (LC_nez_of_LM_nez hp) at hpr)], refl,
    }
end

lemma red_plus_TL_plus {p r : mv_polynomial σ α} (h : p.TL →[S]+ r) :
p →[S]+ p.LT + r :=
begin
    conv in p {rw ←LM_TL_eq p},
    by_cases hp : p.LM = 0,
    {
        rw [TL_eqz_of_LM_eqz hp] at h ⊢,
        have hr : r = 0,
            by_contradiction hr,
            rcases red_plus_trans h (ne.symm hr) with ⟨_, hq, _⟩,
            exact (zero_red _) hq,
        simpa [hr] using rtc.refl',
    },
    {
        have := gt_TL_LM_of_LM_nez hp, revert this,
        induction h with _ p' r' h p' q' r' hpq hqr ih₁ ih₂;
        intro hp',
        {exact rtc.refl'},
        {     
            have := red_of_TL_red (by rwa ←TL_of_add_gt_LM hp' (LC_nez_of_LM_nez hp) at h),
            rw LT_of_add_gt_LM hp' (LC_nez_of_LM_nez hp) at this,
            apply rtc.base' this,
        },
        {exact rtc.trans' (ih₁ hp') (ih₂ (lt_of_le_of_lt (red_plus_LM_ge hpq) hp'))}
    }
end

lemma red_plus_TL_star {p r : mv_polynomial σ α} (h : p.TL →[S]* r) :
p →[S]+ p.LT + r := red_plus_TL_plus h.left

lemma LM_eq_lt_of_lt_TL {p q : mv_polynomial σ α} (h : q < p.TL) :  p.LT + q < p :=
begin
    by_cases hp₁ : p.LM = 0,
    {
        simp [TL_eqz_of_LM_eqz hp₁] at h,
        apply absurd h not_lt_zero,
    },
    {
        have hp₂ := nez_of_LM_nez hp₁,
        have hp₃ := LC_nez_iff.1 hp₂,
        have hq : p.LM > q.LM := lt_of_le_of_lt (LM_le_of_lt h) (gt_TL_LM_of_LM_nez hp₁),
        apply lt.LM_eq hp₂,
        {
            conv at hq in p.LM {rw ←LM_of_LT},
            rw LT_of_add_left hq,
            conv in (p.LT.LT) {rw LT, simp},
            refl,
        },
        {rwa [LT, TL_of_add_gt_LM hq hp₃]},
    }
end

lemma red_cons_reduction {p r : mv_polynomial σ α} (hpq₁ : p.TL →[S] r.TL) (hpq₂ : p.LT = r.LT) :
∀ q, ∃ u, (reduction p q →[S]* u) ∧ (reduction r q →[S]* u) :=
λ q, begin
    have hpr : (p →[S] r) := by simpa [hpq₂, LM_TL_eq r] using red_of_TL_red hpq₁,
    rcases red_add_of_red hpr (-q * monomial (p.LM - q.LM) (p.LC/q.LC)) with ⟨u, hpu, hru⟩,
    rcases exists_red_star S u with ⟨u', hu'₁, hu'₂⟩,
    refine ⟨u', ⟨rtc.trans' (by simpa [reduction] using hpu) hu'₁, hu'₂⟩, 
    ⟨rtc.trans' (by simpa [reduction, LM_eq_of_LT_eq hpq₂, LC_eq_of_LT_eq hpq₂] using hru) hu'₁, hu'₂⟩⟩,
end

theorem red_confluent (h : ∀ {p q} (hp : p ∈ S) (hq : q ∈ S), s_poly p q →[S]* 0) 
(p : mv_polynomial σ α) : ∀ {r t}, (p →[S]* r) → (p →[S]* t) → r = t :=
well_founded.recursion lt_wf p begin
    intros p ih r t hpr hpt,
    by_cases hp₁ : irreducible S p,
    {simp [red_star_irreducible hp₁ hpr, red_star_irreducible hp₁ hpt]},
    {
        by_cases hp₂ : p.LM = 0,
        {
            cases red_star_const hp₂ hpr,
            {
                rw h_1 at hp₁,
                cases hpr with _ hpr,
                apply absurd hpr hp₁,
            },
            {
                cases red_star_const hp₂ hpt,
                {
                    rw h_2 at hp₁,
                    cases hpt with _ hpt,
                    apply absurd hpt hp₁,
                },
                {rw [h_1, h_2]}
            }
        },
        {
            rcases red_star_trans hpr (by simpa using hp₁) with ⟨q₁, hpq₁, hq₁r⟩,
            rcases red_star_trans hpt (by simpa using hp₁) with ⟨q₂, hpq₂, hq₂t⟩,
            have hpq₁_lt := lt_of_red_one_step hpq₁,
            have hpq₂_lt := lt_of_red_one_step hpq₂,
            cases hqr : hpq₁ with a b hp₃ hpq₁₁ hpq₁₂ _ _ hp₃ hr_pq₁;
            cases hqt : hpq₂ with _ _ hp₃ hpq₂₁ hpq₂₂ _ _ hp₃ hr_pq₂; 
            clear hp₃ hqr hqt _x _x_1,
            {
                rcases exists_red_star_of_red hpq₁₁ with ⟨r'₁, hqr'₁, hpr'₁⟩,
                rcases exists_red_star_of_red hpq₂₁ with ⟨t'₁, hqt'₁, hpt'₁⟩,
                have hrt₁: r'₁ = t'₁ := ih _ (TL_lt hp₃) hpr'₁ hpt'₁,
                rcases exists_red_star_of_red_plus (red_plus_TL_star hqr'₁) with ⟨r'₂, hqr'₁₂, hqr'₂⟩,
                rcases exists_red_star_of_red_plus (red_plus_TL_star hqt'₁) with ⟨t'₂, hqt'₁₂, hqt'₂⟩,
                have hrt₂: r'₂ = t'₂ := ih (p.LT + t'₁) (LM_eq_lt_of_lt_TL (red_lt_of_le_of_lt' hpq₂₁ hqt'₁))
                    (by simpa [hrt₁, hpq₁₂] using hqr'₁₂) (by simpa [hpq₂₂] using hqt'₁₂), 
                simpa [ih _ hpq₁_lt hq₁r hqr'₂, ih _ hpq₂_lt hq₂t hqt'₂] using hrt₂,
            },
            {
                rcases hr_pq₂ with ⟨q, h₁, h₂, h₃, h₄⟩, 
                rcases red_cons_reduction hpq₁₁ hpq₁₂ q with ⟨u, hq₂u, hq₁u⟩, rw h₄ at hq₂u,
                have hq₁u' : (q₁ →[S]* u) := 
                    ⟨rtc.base_trans  
                        (red_one_step.red_LM (nez_of_LM_nez (by rwa [←LM_eq_of_LT_eq hpq₁₂])) ⟨q, h₁, h₂, by rwa ←LM_eq_of_LT_eq hpq₁₂, rfl⟩) 
                        hq₁u.left, hq₁u.right⟩,
                simp [ih _ hpq₁_lt hq₁r hq₁u', ih _ hpq₂_lt hq₂t hq₂u],
            },
            {
                rcases hr_pq₁ with ⟨q, h₁, h₂, h₃, h₄⟩, 
                rcases red_cons_reduction hpq₂₁ hpq₂₂ q with ⟨u, hq₁u, hq₂u⟩, rw h₄ at hq₁u,
                have hq₂u' : (q₂ →[S]* u) := 
                    ⟨rtc.base_trans 
                        (red_one_step.red_LM (nez_of_LM_nez (by rwa [←LM_eq_of_LT_eq hpq₂₂])) ⟨q, h₁, h₂, by rwa ←LM_eq_of_LT_eq hpq₂₂, rfl⟩)
                        hq₂u.left, hq₂u.right⟩,
                simp [ih _ hpq₁_lt hq₁r hq₁u, ih _ hpq₂_lt hq₂t hq₂u'],
            },
            {
                rcases hr_pq₁ with ⟨q₁', hq₁₁, hq₁₂, hq₁₃, hq₁₄⟩,
                rcases hr_pq₂ with ⟨q₂', hq₂₁, hq₂₂, hq₂₃, hq₂₄⟩, 
                cases exists_eq_mul_left_of_dvd (lcm_dvd hq₁₃ hq₂₃) with m hq₃,
                have hq : ((q₁ - q₂) →[S]* 0),
                {
                    have h_s : s_poly q₂' q₁' = 
                        (q₂' * monomial (m_lcm q₁'.LM q₂'.LM - q₂'.LM) q₂'.LC⁻¹) + -(q₁' * monomial (m_lcm q₁'.LM q₂'.LM - q₁'.LM) q₁'.LC⁻¹),                     
                        simp [s_poly, mul_comm, m_lcm_comm q₁'.LM q₂'.LM],
                    simp [hq₁₄.symm, hq₂₄.symm, reduction, hq₃, 
                    add_sub_assoc', finsupp.dvd_lcm_right, finsupp.dvd_lcm_left,
                    div_eq_mul_one_div p.LC, monomial_mul_monomial.symm,
                    mul_left_comm _ (monomial m p.LC)],
                    rw [neg_mul_eq_mul_neg, ←mul_add, ←h_s],
                    refine ⟨red_plus_zero_of_mul (h hq₂₁ hq₁₁).left _ _, zero_not_reducible⟩,
                },
                rcases sub_red_star_zero hq with ⟨u, hq₁u, hq₂u⟩,
                simp [ih _ hpq₁_lt hq₁r hq₁u, ih _ hpq₂_lt hq₂t hq₂u],
            }
        }
    }
end

lemma red_plus_insert {p r : mv_polynomial σ α} (h : p →[S]+ r) : ∀ a, p →[insert a S]+ r :=
begin
    induction h with _ p r h p q r hpq hqr ih₁ ih₂;
    intro a,
    {exact rtc.refl'},
    {
        apply rtc.base',
        rw red_one_step_is_red_rel at h ⊢,
        rcases h with ⟨q, hq₁, hq₂, pₜ, hpₜ, hqpₜ, h⟩,
        refine ⟨q, by simp [hq₁], hq₂, pₜ, hpₜ, hqpₜ, h⟩,
    },
    {exact rtc.trans' (ih₁ a) (ih₂ a)}
end

end reduction

section step
inductive buchstep : (list (mv_polynomial σ α) × list (mv_polynomial σ α) × list (mv_polynomial σ α)) 
→ (list (mv_polynomial σ α) × list (mv_polynomial σ α) × list (mv_polynomial σ α)) → Prop
| zero {p} : ∀ l₁ l₂ l₃, red_list p l₁ = 0 → buchstep ⟨l₁, p :: l₂, l₃⟩ ⟨l₁, l₂, l₃⟩
| non_zero {p} : ∀ l₁ l₂ l₃, red_list p l₁ ≠ 0 → 
    buchstep ⟨l₁, p :: l₂, l₃⟩ 
        ⟨(red_list p l₁) :: l₁, s_polyL (red_list p l₁) l₁ ++ l₂, s_polyL (red_list p l₁) l₁ ++ l₃⟩

def buchstep_plus : (list (mv_polynomial σ α) × list (mv_polynomial σ α) × list (mv_polynomial σ α)) 
→ (list (mv_polynomial σ α) × list (mv_polynomial σ α) × list (mv_polynomial σ α)) → Prop := rtc buchstep

lemma buchstep.zero' {p : mv_polynomial σ α} {l₁ l₂ l₃} (h : red_list p l₁ = 0) :
buchstep ⟨l₁, p :: l₂, l₃⟩ ⟨l₁, l₂, l₃⟩ := buchstep.zero l₁ l₂ l₃ h

lemma buchstep.non_zero' {p : mv_polynomial σ α} {l₁ l₂ l₃} (h : red_list p l₁ ≠ 0) :
buchstep ⟨l₁, p :: l₂, l₃⟩ ⟨(red_list p l₁) :: l₁, 
    s_polyL (red_list p l₁) l₁ ++ l₂, s_polyL (red_list p l₁) l₁ ++ l₃⟩ := buchstep.non_zero l₁ l₂ l₃ h

lemma red_list_aux_red_plus_aux : ∀ (p : mv_polynomial σ α) {l₁ l₂ : list (mv_polynomial σ α)}, 
l₂ ⊆ l₁ → (p →[l₁.to_finset]+ red_list_aux p l₂)
| p l₁ [] := by simp [red_list_aux]; exact rtc.refl'
| p l₁ (q :: l₂) := λ h, begin
    by_cases hp : p = 0,
    {simp [hp, zero_red_list_aux], exact rtc.refl'},
    {
        by_cases hqp : q.LM ∣ p.LM; simp [red_list_aux, hqp] at h ⊢,
        {
            by_cases hq : q = 0,
            {
                simp [reduction, hq],
                apply red_list_aux_red_plus_aux _ h.right,
            },
            {
                apply rtc.base_trans (red_one_step.red_LM hp ⟨q, by simp [h.left], hq, hqp, rfl⟩)
                (red_list_aux_red_plus_aux (reduction p q) h.right),
            }
        },
        {apply red_list_aux_red_plus_aux _ h.right}
    }
end

lemma red_list_aux_red_plus (p : mv_polynomial σ α) (l : list (mv_polynomial σ α)) :
(p →[l.to_finset]+ red_list_aux p l) := red_list_aux_red_plus_aux p (by simp)

lemma red_list_red_plus : ∀ (p : mv_polynomial σ α) (l : list (mv_polynomial σ α)),
(p →[l.to_finset]+ red_list p l) 
| p l := begin
    unfold red_list, simp,
    by_cases hp₁ : red_list_aux p l = p; simp [hp₁],
    {exact rtc.refl'},
    {
        by_cases hp₂ : p.LM = 0; simp [hp₂],
        {
            have h := red_plus_const hp₂ (red_list_aux_red_plus p l),
            simp [ne.symm hp₁] at h,
            simpa [h] using red_list_aux_red_plus p l,
        },
        {
            let : (red_list_aux p l).LM < p.LM, from red_list_aux_LM_lt l p hp₂ hp₁,
            apply rtc.trans' (red_list_aux_red_plus p l) (red_list_red_plus _ l),
        }
    }
end
using_well_founded 
{ rel_tac := λ _ _, `[exact ⟨_, inv_image.wf (λ a, a.1.LM) _inst_6.wf⟩] 
, dec_tac := tactic.assumption }

set_option class.instance_max_depth 50
lemma buchberger_buchplus : ∀ L : list (mv_polynomial σ α) × list (mv_polynomial σ α),
buchstep_plus ⟨L.1, L.2, s_polys L.1⟩ ⟨buchberger ⟨L.1, L.2⟩, [], s_polys (buchberger ⟨L.1, L.2⟩)⟩
| ⟨l₁, []⟩ := by unfold buchberger; simp; apply rtc.refl'
| ⟨l₁, (p :: l₂)⟩ := 
let lex := prod.lex ((>) : ideal (mv_polynomial σ α) → ideal (mv_polynomial σ α) → Prop) nat.lt in
begin
    unfold buchberger, 
    by_cases red_list p l₁ = 0; simp [h],
    {
        let : lex ⟨monomial_ideal l₁, l₂.length⟩ ⟨monomial_ideal l₁, (list.cons p l₂).length⟩ := 
            by right; rw [list.length_cons]; apply nat.lt_succ_self,
        apply rtc.base_trans (buchstep.zero' h) (buchberger_buchplus ⟨l₁, l₂⟩),
    },
    {
        let : lex ⟨monomial_ideal (list.cons (red_list p l₁) l₁), (s_polyL (red_list p l₁) l₁ ++ l₂).length⟩ 
            ⟨monomial_ideal l₁, (list.cons p l₂).length⟩ := 
            by left; exact ideal_increase l₁ p h,
        apply rtc.base_trans (buchstep.non_zero' h) 
            (buchberger_buchplus ⟨red_list p l₁ :: l₁, s_polyL (red_list p l₁) l₁ ++ l₂⟩)
    }
end
using_well_founded 
{ rel_tac := λ _ _, 
`[exact ⟨_, inv_image.wf (λ ⟨l₁, l₂⟩, prod.mk (monomial_ideal l₁) l₂.length) (prod.lex_wf ideal_wf nat.lt_wf)⟩ ] 
, dec_tac := tactic.assumption }

lemma buchstep_subset_or_red_eqz (L₁ L₂ : list (mv_polynomial σ α) × list (mv_polynomial σ α) × list (mv_polynomial σ α))
(h : buchstep_plus L₁ L₂) : (∀ a ∈ L₁.2.2, a ∈ L₁.2.1 ∨ (a →[L₁.1.to_finset]+ 0)) → 
∀ a ∈ L₂.2.2, a ∈ L₂.2.1 ∨ (a →[L₂.1.to_finset]+ 0) :=
begin
    induction h with _ L₁ L₂ h L₁ L₂ L₃ h₁ h₂ ih₁ ih₂,
    {simp},
    {
        cases h with p l₁ l₂ l₃ hp p l₁ l₂ l₃ hp,
        {
            simp_intros H a ha,
            rcases H a ha with ⟨h₁ | h₂⟩ | h₃,
            {right, simpa [hp, h₁] using red_list_red_plus p l₁},
            {left, exact h₂},
            {right, exact h₃},
        },
        {
            simp_intros H a' ha',
            cases ha',
            {simp [ha']},
            {
                rcases H a' ha' with ⟨h₁ | h₂⟩ | h₃,
                {
                    right, rw h₁,
                    apply rtc.trans_base (red_plus_insert (red_list_red_plus p l₁) (red_list p l₁)),
                    apply red_mem_S (finset.mem_insert_self _ _) hp,
                },
                {simp [h₂]},
                {
                    right,
                    apply red_plus_insert h₃,
                }
            }
        }
    },
    {
        simp_intros H,
        exact ih₂ (ih₁ H), 
    }
end

lemma s_poly_mem_s_polys : ∀ (l₁ l₂ : list (mv_polynomial σ α)),
(∀ x : mv_polynomial σ α, x ∈ s_polys l₁ → (x →[l₂.to_finset]* 0)) 
→ ∀ (p q : mv_polynomial σ α), p ∈ l₁ → q ∈ l₁ → (s_poly p q →[l₂.to_finset]* 0)
| [] := by simp
| (hd :: tl) := λ l₂ h p q hp hq, begin
    cases hp; cases hq,
    {
        simp [hp, hq, s_poly],
        refine ⟨rtc.refl', zero_not_reducible⟩,
    },
    {
        apply h, 
        simp [hp, s_polys, mem_s_polyL hq],
    },
    {
        rw s_poly_comm,
        have H : (monomial 0 1 : mv_polynomial σ α) = C 1 := by simp [C],
        simpa [H] using 
            red_star_zero_of_mul (h (s_poly q p) (by simp [s_polys, hq, mem_s_polyL hp])) 0 (-1),
    },
    {
        apply s_poly_mem_s_polys tl _  
            (λ x hx, h x (by simp [s_polys, hx])) p q hp hq,
    }
end

lemma buch_confluent_aux (l : list (mv_polynomial σ α)) :
∀ (p q ∈ buchberger ⟨l, s_polys l⟩), (s_poly p q →[(buchberger ⟨l, s_polys l⟩).to_finset]* 0) :=
begin
    apply s_poly_mem_s_polys,
    simp [zero_not_reducible],
    have := buchstep_subset_or_red_eqz ⟨l, s_polys l, s_polys l⟩ 
        ⟨buchberger ⟨l, s_polys l⟩, [], s_polys (buchberger ⟨l, s_polys l⟩)⟩ (buchberger_buchplus ⟨l, s_polys l⟩),
    simp at this,
    apply this,
    finish,
end

theorem buch_confluent (l : list (mv_polynomial σ α)) (p : mv_polynomial σ α) :
∀ {r t}, (p →[(buchberger ⟨l, s_polys l⟩).to_finset]* r) → (p →[(buchberger ⟨l, s_polys l⟩).to_finset]* t) → r = t :=
begin
    apply red_confluent,
    intros p q hp hq,
    apply buch_confluent_aux l p q (by simpa using hp) (by simpa using hq),
end

end step




end buch