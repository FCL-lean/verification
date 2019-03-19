import buchberger util wf_mv_polynomial

open mv_polynomial
open finsupp

namespace buch
variables {σ : Type*} {α : Type*} [decidable_eq σ] [decidable_eq α] [fintype σ] [decidable_linear_order (σ →₀ ℕ)] 
variables [discrete_field α] [is_well_founded (σ →₀ ℕ) (<)] [is_monomial_order (σ →₀ ℕ) (≤)] 

section reduction
variables (s : finset (mv_polynomial σ α)) {S : finset (mv_polynomial σ α)}

inductive red_one_step : mv_polynomial σ α → mv_polynomial σ α → Prop
| cons : ∀ {p r : mv_polynomial σ α}, p ≠ 0 → red_one_step p.tl r.tl → p.lm = r.lm → p.lc = r.lc → red_one_step p r
| red_lm : ∀ {p r : mv_polynomial σ α}, p ≠ 0 → 
    (∃ (q : mv_polynomial σ α) (h₁ : q ∈ s) (h₂ : q ≠ 0)  (h₃ : q.lm ∣ p.lm), reduction p q = r) → red_one_step p r

def reducible (p : mv_polynomial σ α) :=
    ∃ (q : mv_polynomial σ α) (hq₁ : q ∈ s) (hq₂ : q ≠ 0) (pₜ : σ →₀ ℕ) (hp : pₜ ∈ p.support), q.lm ∣ pₜ
def reducible' (p r : mv_polynomial σ α) :=
    ∃ (q : mv_polynomial σ α) (hq₁ : q ∈ s) (hq₂ : q ≠ 0) (pₜ : σ →₀ ℕ) (hp : pₜ ∈ p.support) (hqpₜ : q.lm ∣ pₜ), 
        r = p - q * monomial (pₜ - q.lm) (p pₜ / q.lc)

notation a `→[` S `]` b := red_one_step S a b
notation a `↛[` S `]` b := ¬ red_one_step S a b

def red_plus : mv_polynomial σ α → mv_polynomial σ α → Prop := rtc (red_one_step s)
notation a `→[` S `]+` b := red_plus S a b
notation a `↛[` S `]+` b := ¬ red_plus S a b

def irreducible (p : mv_polynomial σ α) := ∀ (q : mv_polynomial σ α) (hq₁ : q ∈ s) (hq₂ : q ≠ 0) (pₜ ∈ p.support), q.lm ∤ pₜ

notation a `→[` S `]*` b := red_plus S a b ∧ irreducible S b

instance irreducible_decidable (p : mv_polynomial σ α) : decidable (irreducible s p) := finset.decidable_dforall_finset
instance reducible_decidable (p : mv_polynomial σ α) : decidable (reducible s p) := finset.decidable_dexists_finset

@[simp] lemma irred_not_red {p : mv_polynomial σ α} : irreducible s p ↔ ¬ reducible s p := by simp [irreducible, reducible]
lemma red_not_irred {p : mv_polynomial σ α} : ¬ irreducible s p ↔ reducible s p := by simp [irred_not_red]

lemma zero_irreducible : irreducible S 0 := by simp [irreducible]
lemma zero_not_reducible : ¬ reducible S 0 := by rw ←irred_not_red; exact zero_irreducible
lemma zero_not_reducible' : ∀ {r}, ¬ reducible' S 0 r := by simp [reducible']

lemma red_one_step_reducible {p r : mv_polynomial σ α} (h : p →[S] r) : reducible S p :=
begin
    induction h with p r hp hpr₁ hpr₂ hpr₃ ih p r hp h,
    {
        rcases ih with ⟨q, hq₁, hq₂, pₜ, hp, hpq⟩,
        refine ⟨q, hq₁, hq₂, pₜ, tl_support_subset hp, hpq⟩,
    },
    {
        rcases h with ⟨q, hq₁, hq₂, hpq, _⟩,
        use [q, hq₁, hq₂, p.lm, lm_mem_support hp, hpq],
    }
end

lemma red_one_step_reducible' {p r : mv_polynomial σ α} : (p →[S] r) ↔ reducible' S p r :=
⟨λ h, begin
    induction h with p r hp hpr₁ hpr₂ hpr₃ ih p r hp h,
    {
        rcases ih with ⟨q, hq₁, hq₂, pₜ, hpₜ, hqpₜ, h⟩,
        rw [←@add_left_cancel_iff _ _ (monomial p.lm p.lc), 
            ←add_sub_assoc, lm_tl_eq p, hpr₂, hpr₃, lm_tl_eq r, tl_apply_mem hpₜ] at h,
        refine ⟨q, hq₁, hq₂, pₜ, tl_support_subset hpₜ, hqpₜ, h⟩,
    },
    {
        rcases h with ⟨q, hq₁, hq₂, hpq, h⟩,
        refine ⟨q, hq₁, hq₂, p.lm, lm_mem_support hp, hpq, by rw ←h; refl⟩,
    }
end, begin 
    revert r,
    apply induction p,
    {intros r hr, apply absurd hr zero_not_reducible'},
    {
        intros p ih r hr,
        rcases hr with ⟨q, hq₁, hq₂, pₜ, hpₜ, hqpₜ, h⟩,
        by_cases hpₜp : pₜ = p.lm,
        {
            apply red_one_step.red_lm (nez_of_mem_support hpₜ), 
            refine ⟨q, hq₁, hq₂, by rwa ←hpₜp, by rw [h, hpₜp]; refl,⟩,
        },
        {
            have h₁ : p pₜ / q.lc ≠ 0 := div_ne_zero (by simpa using hpₜ) (lc_nez_iff.1 hq₂),
            have hp_lm : p.lm > (q * monomial (pₜ - lm q) (p pₜ / lc q)).lm,
                simp [lm_of_mul_m hq₂ h₁, finsupp.add_sub_cancel' hqpₜ],
                apply lt_of_le_of_ne (lm_rel' _ hpₜ) hpₜp,
            have hr₁ : p.lm = r.lm := by rw [h, lm_of_sub_left hp_lm],
            have hr₂ : p.lc = r.lc := by rw [h, lc_of_sub_left hp_lm],
            apply red_one_step.cons (nez_of_mem_support hpₜ) _ hr₁ hr₂,
            {
                apply ih,
                refine ⟨q, hq₁, hq₂, pₜ, mem_tl_support hpₜp hpₜ, hqpₜ, _⟩,
                rwa [←@add_left_cancel_iff _ _ (monomial p.lm p.lc), ←add_sub_assoc, lm_tl_eq p, hr₁, hr₂, lm_tl_eq r, tl_apply _ _ hpₜp],
            },
        }
    }
end⟩

lemma zero_red {r : mv_polynomial σ α} : (0 : mv_polynomial σ α) ↛[s] r  :=
λ h, zero_not_reducible (red_one_step_reducible h)

lemma zero_red_plus {r : mv_polynomial σ α} (h : (0 : mv_polynomial σ α) →[S]+ r) : r = 0 :=
begin
    generalize hp : (0 : mv_polynomial σ α) = p, rw hp at h,
    revert hp,
    induction h with _ _ _ h p q r hpq hqr ih₁ ih₂,
    {simp},
    {
        intro hp, rw ←hp at h,
        apply absurd h (zero_red _),
    },
    {
        intro hp,
        rw [ih₁ hp] at ih₂, 
        exact ih₂ hp,
    }
end

lemma red_mem_S {q : mv_polynomial σ α} (hq₁ : q ∈ S) (hq₂ : q ≠ 0) : q →[S] 0 :=
begin
    rw red_one_step_reducible',
    refine ⟨q, hq₁, hq₂, q.lm, lm_mem_support hq₂, by simp, _⟩,
    have h₁ : q q.lm = q.lc := rfl,
    have h₂ : (monomial 0 1 : mv_polynomial σ α) = C 1 := by simp [C],
    simp [h₁, div_self (lc_nez_iff.1 hq₂), h₂],
end

lemma red_plus_mul {p r : mv_polynomial σ α} (h : p →[S]+ r) : 
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
            rw red_one_step_reducible' at h ⊢,
            rcases h with ⟨q, hq₁, hq₂, pₜ, hp, hpq, h⟩,
            refine ⟨q, hq₁, hq₂, a + pₜ, mul_mem_mul_support _ hp a b hb, dvd_of_dvd_of_add' hpq _, _⟩,
            rw [mul_apply hp, finsupp.add_sub_assoc' hpq, mul_div_assoc, 
            ←monomial_mul_monomial, mul_left_comm, ←mul_sub, h],
        },
        {exact rtc.trans' (ih₁ a b hb) (ih₂ a b hb)}
    }
end

lemma red_plus_zero {p : mv_polynomial σ α} (h : p →[S]+ 0) : 
    ∀ a b, (monomial a b * p) →[S]+ 0 := by simpa using red_plus_mul h

lemma red_star_zero {p : mv_polynomial σ α} (h : p →[S]* 0) : 
    ∀ a b, (monomial a b * p) →[S]* 0 := λ a b, ⟨red_plus_zero h.left a b, zero_irreducible⟩

lemma lt_of_red_one_step {p r : mv_polynomial σ α} (h : p →[S] r) : r < p :=
begin
    induction h with p r hp h₁ h₂ h₃ ih p r hp h, 
    {apply lt.lm_eq hp h₂.symm h₃.symm ih},
    {
        rcases h with ⟨q, h₁, h₂, h₃, h₄⟩,
        rw ←h₄,
        by_cases hp' : p.lm = 0,
        {
            simp [hp'] at h₃,
            have hq : q 0 ≠ 0,
                rw [←h₃, ←mem_support_iff],
                exact lm_mem_support h₂,
            conv {
                to_lhs,
                rw [eqC_of_lm_eqz.1 hp', eqC_of_lm_eqz.1 h₃, reduction_C_C hq],
            },
            apply lt.zero hp,
        },
        {
            apply lt.lm_lt,
            apply reduction_lm_lt h₃ hp' h₂, 
        }
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
begin
    cases hqr with hqr _,
    exact red_lt_of_le_of_lt hpq hqr,
end

lemma red_one_step_lm_ge {p r : mv_polynomial σ α} (h : p →[S] r) : p.lm ≥ r.lm := lm_le_of_lt (lt_of_red_one_step h)
lemma red_plus_lm_ge {p r : mv_polynomial σ α} (h : p →[S]+ r) : p.lm ≥ r.lm :=
begin
    induction h with _ _ _ h _ _ _ _ _ ih₁ ih₂,
    {exact le_refl _},
    {exact red_one_step_lm_ge h},
    {exact ge_trans ih₁ ih₂},
end

lemma red_star_lm_ge {p r : mv_polynomial σ α} (h : p →[S]* r) : p.lm ≥ r.lm :=
begin
    cases h with h _,
    exact red_plus_lm_ge h,
end

lemma reducible_red_one_step {p : mv_polynomial σ α} : reducible S p → ∃ r, p →[S] r :=
begin
    apply induction p,
    {intro h, apply absurd h zero_not_reducible},
    {
        intros p ih hp,
        rcases hp with ⟨q, ⟨hq₁,⟨hq₂, ⟨pₜ, ⟨hp, hpq⟩⟩⟩⟩⟩,
        by_cases h : pₜ = p.lm,
        {use [reduction p q, red_one_step.red_lm (nez_of_mem_support hp) ⟨q, hq₁, hq₂, by rwa ←h, rfl⟩]},
        {
            have hm_tl : pₜ ∈ p.tl.support := mem_tl_support h hp,
            have h_tl : reducible S p.tl,
                use [q, hq₁, hq₂, pₜ, hm_tl, hpq],
            rcases ih h_tl with ⟨r, h_tl'⟩,    
            refine ⟨monomial p.lm p.lc + r, _⟩,
            have hp' := lc_nez_iff.1 (nez_of_mem_support hp),
            have hr : p.lm > r.lm,
                apply lt_of_le_of_lt (red_one_step_lm_ge h_tl') (lm_gt_tl_lm (nez_of_mem_support hm_tl)),
            apply red_one_step.cons (nez_of_mem_support hp),
            {rwa tl_of_add_gt_lm hr hp'},
            {rw lm_of_add_gt_lm hr hp'},
            {rw lc_of_add_gt_lm hr hp'},
        }
    } 
end

lemma red_plus_irreducible {p q : mv_polynomial σ α} (hp : irreducible S p) (h : p →[S]+ q) : q = p :=
begin
    induction h with _ p q h p q r hpq hpr ih₁ ih₂, 
    {refl},
    {apply absurd (red_one_step_reducible h) (by simpa using hp)},
    {simpa [ih₁ hp, hp] using ih₂},
end

lemma red_star_irreducible {p q : mv_polynomial σ α} (hp : irreducible S p) (h : p →[S]* q) : q = p :=
begin
    rcases h with ⟨h₁, _⟩,
    apply red_plus_irreducible hp h₁,
end

lemma red_const {p r : mv_polynomial σ α} (hp : p.lm = 0) (h : p →[S] r) : r = 0 :=
begin
    cases h with _ _ _ h _ _ _ _ hp' h,
    {apply absurd (by rwa tl_eqz_of_lm_eqz hp at h) (zero_red _)},
    {
        rcases h with ⟨q, h₁, h₂, h₃, h₄⟩,
        simp [hp] at h₃, 
        have hq : q 0 ≠ 0,
            rw [←h₃, ←mem_support_iff],
            exact lm_mem_support h₂,
        rw [←h₄, eqC_of_lm_eqz.1 hp, eqC_of_lm_eqz.1 h₃, reduction_C_C hq],
    }
end

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

lemma red_plus_const {p r : mv_polynomial σ α} (hp : p.lm = 0) (h : p →[S]+ r) : p = r ∨ r = 0 :=
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

lemma red_star_const {p r : mv_polynomial σ α} (hp : p.lm = 0) (h : p →[S]* r) : p = r ∨ r = 0 :=
begin
    cases h with h _,
    exact red_plus_const hp h,
end

lemma red_star_trans {p r : mv_polynomial σ α} (h : p →[S]* r) : reducible S p → ∃ q, (p →[S] q) ∧ (q →[S]* r) := 
begin
    cases h with h₁ h₂, revert h₂,
    induction h₁ with p₁ p₂ r₂ h₁ p₃ q₃ r₃ h₁ h₂ ih₁ ih₂, 
    {simp_intros h₂ h₃, apply absurd h₃ h₂}, 
    {simp_intros h₂ h₃, use [r₂, h₁, rtc.refl', h₂]},
    {
        intros hr hp,
        by_cases hq : irreducible S q₃,
        {
            rcases ih₁ hq hp with ⟨t, ht₁, ht₂⟩, 
            use [t, ht₁, by rwa red_plus_irreducible hq h₂],
        },
        {
            by_cases hpq : p₃ = q₃, 
            {rw hpq, apply ih₂ hr (by rwa ←red_not_irred)},
            {
                rcases red_plus_trans h₁ hpq with ⟨t, ht₁, ht₂⟩,
                use [t, ht₁, rtc.trans' ht₂ h₂, hr],
            }
        }
    }
end

lemma exists_red_star (p : mv_polynomial σ α) : ∃ r, p →[s]* r :=
@well_founded.recursion (mv_polynomial σ α) (<) lt_wf _ p 
(begin
    intros p ih,
    by_cases hp : irreducible s p,
    {use [p, rtc.refl', hp]},
    {
        simp at hp,
        cases reducible_red_one_step hp with q hq,
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
(hqpₜ : q.lm ∣ pₜ) (h : r = p - q * monomial (pₜ - q.lm) (p pₜ / q.lc)) : pₜ ∉ r.support :=
begin
    have h_lc : (q * monomial (pₜ - lm q) (p pₜ / lc q)) pₜ = (q * monomial (pₜ - lm q) (p pₜ / lc q)).lc,
        have h₁ : p pₜ / q.lc ≠ 0 := div_ne_zero (by simpa using hpₜ) (lc_nez_iff.1 hq),
        have h_lm : (q * monomial (pₜ - lm q) (p pₜ / lc q)).lm = pₜ,
            rw [lm_of_mul_m hq h₁, finsupp.add_sub_cancel' hqpₜ],
        unfold mv_polynomial.lc at h_lm ⊢, rw [h_lm], refl, 
    simp [h, h_lc, lc_of_mul_m hq, mul_div_cancel' _ (lc_nez_iff.1 hq)],
end

lemma sub_red_comp {p r : mv_polynomial σ α} (h : p →[S] r) :
∀ u, ∃ t₁ t₂, (p + u →[S]+ t₁) ∧ (u →[S]+ t₂) ∧ (r = t₁ - t₂) :=
λ u, begin
    rw red_one_step_reducible' at h,
    rcases h with ⟨q, hq₁, hq₂, pₜ, hpₜ, hqpₜ, h⟩,
    have hr := red_m_not_mem hq₂ hpₜ hqpₜ h,
    by_cases hpₜu : pₜ ∈ u.support;
    simp at hpₜu hr hpₜ,
    {
        by_cases hpₜ': pₜ ∈ (p + u).support,
        {
            refine ⟨p + u - q * monomial (pₜ - lm q) ((p + u) pₜ / lc q), 
                u - q * monomial (pₜ - lm q) (u pₜ / lc q), 
                rtc.base' (red_one_step_reducible'.2 ⟨q, hq₁, hq₂, pₜ, hpₜ', hqpₜ, rfl⟩),
                rtc.base' (red_one_step_reducible'.2 ⟨q, hq₁, hq₂, pₜ, by simpa using hpₜu, hqpₜ, rfl⟩), _⟩,
            {
                simp [-mul_neg_eq_neg_mul_symm, neg_mul_eq_mul_neg],
                rw [←mul_add, ←monomial_neg, ←neg_div, ←monomial_add_monomial, 
                div_add_div_same, neg_add_rev, ←add_assoc, add_neg_self],
                simp [neg_div, h],
            }
        },
        {
            simp [add_eq_zero_iff_neg_eq] at hpₜ',
            refine ⟨p + u, u - q * monomial (pₜ - lm q) (u pₜ / lc q), rtc.refl', 
                rtc.base' (red_one_step_reducible'.2 ⟨q, hq₁, hq₂, pₜ, by simpa using hpₜu, hqpₜ, rfl⟩),
                by simp [hpₜ'.symm, neg_div, h]⟩,
        }
    },
    {
        refine ⟨p + u - q * monomial (pₜ - q.lm) ((p + u) pₜ/ q.lc), u, 
            rtc.base' (red_one_step_reducible'.2 ⟨q, hq₁, hq₂, pₜ, by simpa [hpₜu] using hpₜ, hqpₜ, rfl⟩),
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
        rw [eq_sub_iff_add_eq] at h₃,
        refine ⟨t₂, by rwa h₃, h₂⟩,
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
    simp at hpr,
    refine ⟨t, ⟨rtc.trans' hpr ht₁, ht₂⟩, ⟨rtc.trans' hqr ht₁, ht₂⟩⟩,
end

lemma red_add_of_red {p r : mv_polynomial σ α} (h : p →[S] r) : 
∀ u, ∃ t, (p + u →[S]+ t) ∧ (r + u →[S]+ t) :=
λ u, begin
    rw red_one_step_reducible' at h,
    rcases h with ⟨q, hq₁, hq₂, pₜ, hpₜ, hqpₜ, h⟩,
    have hr := red_m_not_mem hq₂ hpₜ hqpₜ h,
    by_cases hpₜu : pₜ ∈ u.support;
    simp at hpₜu hr,
    {
        by_cases hpₜ': pₜ ∈ (p + u).support,
        {
            refine ⟨r + u - q * monomial (pₜ - lm q) (u pₜ / lc q), _, _⟩;
            apply rtc.base'; rw [red_one_step_reducible'],
            {
                conv at h {
                    rw [←@add_right_cancel_iff _ _ (u - q * monomial (pₜ - q.lm) (u pₜ / q.lc)), ←add_sub_assoc],
                    to_rhs, rw [←add_sub_assoc, sub_add_eq_add_sub, sub_sub, ←mul_add, ←monomial_add_monomial, div_add_div_same, ←add_apply],
                },
                refine ⟨q, hq₁, hq₂, pₜ, hpₜ', hqpₜ, by rw h⟩,
            },
            {refine ⟨q, hq₁, hq₂, pₜ, by simpa [hr] using hpₜu, hqpₜ, by conv in ((r + u) pₜ) {simp [hr]},⟩}
        },
        {
            simp [add_eq_zero_iff_eq_neg] at hpₜ',
            refine ⟨p + u, rtc.refl', _⟩,
            apply rtc.base',
            rw red_one_step_reducible',
            refine ⟨q, hq₁, hq₂, pₜ, by simpa [hr] using hpₜu, hqpₜ, _⟩,
            simp [h, hpₜ', neg_div, hr],
        }
    },
    {
        refine ⟨r + u, _, rtc.refl'⟩,
        apply rtc.base',
        rw [red_one_step_reducible', h, sub_add_eq_add_sub],
        refine ⟨q, hq₁, hq₂, pₜ, by simpa [hpₜu] using hpₜ, hqpₜ, by simp [hpₜu]⟩,
    }
end

lemma red_cons {p r : mv_polynomial σ α} (h : p →[S] r) :
∀ {a} {b : α}, a > p.lm → b ≠ 0
→ ((monomial a b + p) →[S] (monomial a b + r)) :=
λ a b ha hb, begin
    have har : a > r.lm := lt_of_le_of_lt (red_one_step_lm_ge h) ha,
    apply red_one_step.cons (add_monomial_nez (gt_lm_not_mem ha) hb),
    {rwa [tl_of_add_gt_lm ha hb, tl_of_add_gt_lm har hb]},
    {rw [lm_of_add_gt_lm ha hb, lm_of_add_gt_lm har hb]},
    {rw [lc_of_add_gt_lm ha hb, lc_of_add_gt_lm har hb]},
end

lemma red_plus_cons' {p r : mv_polynomial σ α} (h : p →[S]+ r) : 
∀ {a} {b : α}, a > p.lm → b ≠ 0
→ ((monomial a b + p) →[S]+ (monomial a b + r)) :=
begin
    induction h with _ p r h p q r hpq hqr ih₁ ih₂;
    intros a b ha hb,
    {exact rtc.refl'},
    {
        apply rtc.base,
        apply red_cons h, assumption',
    },
    {exact rtc.trans' (ih₁ ha hb) (ih₂ (lt_of_le_of_lt (red_plus_lm_ge hpq) ha) hb)}
end

lemma red_of_tl_red {p r : mv_polynomial σ α} (h : p.tl →[S] r) :
p →[S] monomial p.lm p.lc + r :=
begin
    conv {congr, skip, rw ←lm_tl_eq p},
    by_cases hp : p.lm = 0,
    {
        rw [tl_eqz_of_lm_eqz hp] at h,
        apply absurd h (zero_red _),
    },
    {exact red_cons h (gt_tl_lm_of_lm_nez hp) (lc_nez_of_lm_nez hp)}
end

lemma red_plus_tl_star {p r : mv_polynomial σ α} (h : p.tl →[S]* r) :
p →[S]+ monomial p.lm p.lc + r :=
begin
    cases h with h _,
    conv {congr, skip, rw ←lm_tl_eq p},
    by_cases hp : p.lm = 0,
    {
        rw [tl_eqz_of_lm_eqz hp] at h ⊢,
        simp [zero_red_plus h],
        exact rtc.refl',
    },
    {exact red_plus_cons' h (gt_tl_lm_of_lm_nez hp) (lc_nez_of_lm_nez hp)}
end

lemma lm_eq_lt_of_lt_tl {p q : mv_polynomial σ α} (h : q < p.tl) :  monomial p.lm p.lc + q < p :=
begin
    by_cases hp₁ : p.lm = 0,
    {
        simp [tl_eqz_of_lm_eqz hp₁] at h,
        apply absurd h not_lt_zero,
    },
    {
        have hp₂ : p ≠ 0,
            intro hp, simp [hp, tl] at h, exact not_lt_zero h,
        have hp₃ := lc_nez_iff.1 hp₂,
        have hq : p.lm > q.lm := lt_of_le_of_lt (lm_le_of_lt h) (gt_tl_lm_of_lm_nez hp₁),
        apply lt.lm_eq hp₂,
        {rw [lm_of_add_gt_lm hq hp₃]},
        {rw [lc_of_add_gt_lm hq hp₃]},
        {rwa [tl_of_add_gt_lm hq hp₃]},
    }
end

lemma red_confluent_aux {p q : mv_polynomial σ α} (hpq₁ : p.tl →[S] q.tl) (hpq₂ : p.lm = q.lm) (hpq₃ : p.lc = q.lc)
: ∃ r₁ r₂, (q.tl →[S]* r₁) ∧ (p.tl →[S]* r₁) ∧ (monomial (lm p) (lc p) + r₁ →[S]* r₂) ∧ (q →[S]* r₂) :=
begin
    rcases exists_red_star_of_red hpq₁ with ⟨r₁, hqr₁, hpr₁⟩,
    rcases exists_red_star_of_red_plus (red_plus_tl_star hqr₁) with ⟨r₂, hqr₁₂, hqr₂⟩,
    use [r₁, r₂, hqr₁, hpr₁, by rwa [hpq₂, hpq₃], hqr₂],
end

lemma red_cons_reduction {p r : mv_polynomial σ α} (hpq₁ : p.tl →[S] r.tl) (hpq₂ : p.lm = r.lm) (hpq₃ : p.lc = r.lc) :
∀ q, ∃ u, (reduction p q →[S]+ u) ∧ (reduction r q →[S]+ u) :=
λ q, begin
    have h_red : ∀ {a b : mv_polynomial σ α}, 
        reduction a b = a + -b * monomial (a.lm -b.lm) (a.lc / b.lc) := λ a b, by simp [reduction],
    rcases red_add_of_red (red_of_tl_red hpq₁) (-q * monomial (p.lm - q.lm) (p.lc/q.lc)) with ⟨u, hq₂u, hq₁u⟩,
    refine ⟨u, by rwa h_red, by rwa [hpq₂, hpq₃, lm_tl_eq r, ←h_red] at hq₁u⟩,
end

lemma red_confluent (h : ∀ {p q} (hp : p ∈ S) (hq : q ∈ S), s_poly p q →[S]* 0) 
(p : mv_polynomial σ α) : ∀ {r t}, (p →[S]* r) → (p →[S]* t) → r = t :=
well_founded.recursion lt_wf p begin
    intros p ih r t hpr hpt,
    by_cases hp₁ : irreducible S p,
    {simp [red_star_irreducible hp₁ hpr, red_star_irreducible hp₁ hpt]},
    {
        by_cases hp₂ : p.lm = 0,
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
            cases hqr : hpq₁ with a b hp₃ hpq₁₁ hpq₁₂ hpq₁₃ _ _ hp₃ hr_pq₁;
            cases hqt : hpq₂ with _ _ hp₃ hpq₂₁ hpq₂₂ hpq₂₃ _ _ hp₃ hr_pq₂; 
            clear hp₃ hqr hqt _x _x_1,
            {
                rcases red_confluent_aux hpq₁₁ hpq₁₂ hpq₁₃ with ⟨r', r'', hq₁r', hpr', hq₁r''₁, hq₁r''₂⟩,
                rcases red_confluent_aux hpq₂₁ hpq₂₂ hpq₂₃ with ⟨t', t'', hq₂t', hpt', hq₂t''₁, hq₂t''₂⟩,
                rw ih _ (tl_lt hp₃) hpr' hpt' at hq₁r''₁,
                simp [ih _ hpq₁_lt hq₁r hq₁r''₂, ih _ hpq₂_lt hq₂t hq₂t''₂,
                ih _ (lm_eq_lt_of_lt_tl (red_lt_of_le_of_lt' hpq₂₁ hq₂t')) hq₁r''₁ hq₂t''₁],
            },
            {
                rcases hr_pq₂ with ⟨q, h₁, h₂, h₃, h₄⟩, 
                rcases red_cons_reduction hpq₁₁ hpq₁₂ hpq₁₃ q with ⟨u, hq₂u, hq₁u⟩, rw h₄ at hq₂u,
                have hq₁u' := rtc.base_trans (red_one_step.red_lm (by rwa [lc_nez_iff, ←hpq₁₃, ←lc_nez_iff]) 
                    ⟨q, h₁, h₂, by rwa ←hpq₁₂, rfl⟩) hq₁u,
                rcases exists_red_star_of_red_plus hq₁u' with ⟨q₁u, h_uq₁u, h_q₁q₁u⟩,
                rcases exists_red_star_of_red_plus hq₂u with ⟨q₂u, h_uq₂u, h_q₂q₂u⟩,
                simp [ih _ hpq₂_lt hq₂t h_q₂q₂u, ih _ hpq₁_lt hq₁r h_q₁q₁u,
                ih _ (red_lt_of_le_of_lt hpq₂ hq₂u) h_uq₁u h_uq₂u],
            },
            {
                rcases hr_pq₁ with ⟨q, h₁, h₂, h₃, h₄⟩, 
                rcases red_cons_reduction hpq₂₁ hpq₂₂ hpq₂₃ q with ⟨u, hq₁u, hq₂u⟩, rw h₄ at hq₁u,
                have hq₂u' := rtc.base_trans (red_one_step.red_lm (by rwa [lc_nez_iff, ←hpq₂₃, ←lc_nez_iff]) 
                    ⟨q, h₁, h₂, by rwa ←hpq₂₂, rfl⟩) hq₂u,
                rcases exists_red_star_of_red_plus hq₂u' with ⟨q₂u, h_uq₂u, h_q₂q₂u⟩,
                rcases exists_red_star_of_red_plus hq₁u with ⟨q₁u, h_uq₁u, h_q₁q₁u⟩,
                simp [ih _ hpq₂_lt hq₂t h_q₂q₂u, ih _ hpq₁_lt hq₁r h_q₁q₁u,
                ih _ (red_lt_of_le_of_lt hpq₁ hq₁u) h_uq₁u h_uq₂u],
            },
            {
                rcases hr_pq₁ with ⟨q₁', hq₁₁, hq₁₂, hq₁₃, hq₁₄⟩,
                rcases hr_pq₂ with ⟨q₂', hq₂₁, hq₂₂, hq₂₃, hq₂₄⟩, 
                cases exists_eq_mul_left_of_dvd (lcm_dvd hq₁₃ hq₂₃) with m hq₃,
                have hq : ((q₁ - q₂) →[S]* 0),
                {
                    have h_s : s_poly q₂' q₁' = 
                        (q₂' * monomial (m_lcm q₁'.lm q₂'.lm - q₂'.lm) q₂'.lc⁻¹) + -(q₁' * monomial (m_lcm q₁'.lm q₂'.lm - q₁'.lm) q₁'.lc⁻¹),
                        have : ¬ (q₂'.lc = 0 ∨ q₁'.lc = 0),
                            simp [not_or_distrib], use [lc_nez_iff.1 hq₂₂, lc_nez_iff.1 hq₁₂],
                        simp [s_poly, mul_comm, m_lcm_comm q₁'.lm q₂'.lm, lcm, this], 
                    simp [hq₁₄.symm, hq₂₄.symm, reduction, hq₃, 
                    add_sub_assoc', finsupp.dvd_lcm_right, finsupp.dvd_lcm_left,
                    div_eq_mul_one_div p.lc, monomial_mul_monomial.symm,
                    mul_left_comm _ (monomial m p.lc)],
                    rw [neg_mul_eq_mul_neg, ←mul_add, ←h_s],
                    refine ⟨red_plus_zero (h hq₂₁ hq₁₁).left _ _, zero_not_reducible⟩,
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
        rw red_one_step_reducible' at h ⊢,
        rcases h with ⟨q, hq₁, hq₂, pₜ, hpₜ, hqpₜ, h⟩,
        refine ⟨q, by simp [hq₁], hq₂, pₜ, hpₜ, hqpₜ, h⟩,
    },
    {exact rtc.trans' (ih₁ a) (ih₂ a)}
end

end reduction

section step
inductive buchstep : ((list (mv_polynomial σ α) × list (mv_polynomial σ α)) × list (mv_polynomial σ α)) 
→ ((list (mv_polynomial σ α) × list (mv_polynomial σ α)) × list (mv_polynomial σ α)) → Prop
| zero {p} : ∀ l₁ l₂ l₃, red_list p l₁ = 0 → buchstep ⟨⟨l₁, p :: l₂⟩, l₃⟩ ⟨⟨l₁, l₂⟩, l₃⟩
| non_zero {p} : ∀ l₁ l₂ l₃, red_list p l₁ ≠ 0 → 
    buchstep ⟨⟨l₁, p :: l₂⟩, l₃⟩ 
        ⟨⟨(red_list p l₁) :: l₁, s_polyL (red_list p l₁) l₁ ++ l₂⟩, s_polyL (red_list p l₁) l₁ ++ l₃⟩

notation `‘` l₁ `,` l₂ `,` l₃ `’→‘` l₁' `,` l₂' `,` l₃' `’` := buchstep ⟨⟨l₁, l₂⟩, l₃⟩ ⟨⟨l₁', l₂'⟩, l₃'⟩

def buchstep_plus : ((list (mv_polynomial σ α) × list (mv_polynomial σ α)) × list (mv_polynomial σ α)) 
→ ((list (mv_polynomial σ α) × list (mv_polynomial σ α)) × list (mv_polynomial σ α)) → Prop := rtc buchstep

notation `‘` l₁ `,` l₂ `,` l₃ `’→+‘` l₁' `,` l₂' `,` l₃' `’` := buchstep_plus ⟨⟨l₁, l₂⟩, l₃⟩ ⟨⟨l₁', l₂'⟩, l₃'⟩

lemma buchstep.zero' {p : mv_polynomial σ α} {l₁ l₂ l₃} (h : red_list p l₁ = 0) :
‘l₁, p :: l₂, l₃’→‘l₁, l₂, l₃’ := buchstep.zero l₁ l₂ l₃ h

lemma buchstep.non_zero' {p : mv_polynomial σ α} {l₁ l₂ l₃} (h : red_list p l₁ ≠ 0) :
‘l₁, p :: l₂, l₃’→‘(red_list p l₁) :: l₁, 
    s_polyL (red_list p l₁) l₁ ++ l₂, s_polyL (red_list p l₁) l₁ ++ l₃’ := buchstep.non_zero l₁ l₂ l₃ h

lemma reduction_red_one_step : ∀ {p q : mv_polynomial σ α} {l : list (mv_polynomial σ α)},
p ≠ 0 → q ∈ l → q ≠ 0 → q.lm ∣ p.lm → (p →[l.to_finset] reduction p q) :=
λ p q l hp hq₁ hq₂ hqp, begin
    rw red_one_step_reducible',
    refine ⟨q, by simp [hq₁], hq₂, p.lm, lm_mem_support hp, hqp, by simp [reduction]; refl,⟩,
end

lemma red_list_aux_red_plus_aux : ∀ (p : mv_polynomial σ α) {l₁ l₂ : list (mv_polynomial σ α)}, 
l₂ ⊆ l₁ → (p →[l₁.to_finset]+ red_list_aux p l₂)
| p l₁ [] := by simp [red_list_aux]; exact rtc.refl'
| p l₁ (q :: l₂) := λ h, begin
    by_cases hp : p = 0,
    {simp [hp, zero_red_list_aux], exact rtc.refl'},
    {
        simp at h,
        by_cases hqp : q.lm ∣ p.lm; simp [red_list_aux, hqp],
        {
            by_cases hq : q = 0,
            {
                simp [reduction, hq],
                apply red_list_aux_red_plus_aux,
                exact h.right,
            },
            {
                apply rtc.base_trans (reduction_red_one_step hp h.left hq hqp)
                (red_list_aux_red_plus_aux (reduction p q) h.right),
            }
        },
        {
            apply red_list_aux_red_plus_aux,
            exact h.right,
        }
    }
end

lemma red_list_aux_red_plus (p : mv_polynomial σ α) (l : list (mv_polynomial σ α)) :
(p →[l.to_finset]+ red_list_aux p l) := red_list_aux_red_plus_aux p (by simp)

lemma exists_red_of_red_list_aux_neq : ∀ (p : mv_polynomial σ α) (l₁ l₂ : list (mv_polynomial σ α)),
l₂ ⊆ l₁ → red_list_aux p l₂ ≠ p → p.lm = 0 → (p →[l₁.to_finset] 0) 
| p l₁ [] := by simp [red_list_aux]
| p l₁ (q :: l₂) := λ h hp₂ hp₃, begin
    by_cases hp₁ : p = 0,
    {
        simp [hp₁] at hp₂,
        apply absurd (zero_red_list_aux _) hp₂,
    },
    {
        simp at h,
        by_cases hq : q = 0,
        {
            simp [hq, red_list_aux, reduction] at hp₂,
            apply exists_red_of_red_list_aux_neq p l₁ l₂ h.right hp₂ hp₃,
        },
        {
            by_cases hq' : q.lm = 0,
            {
                rw red_one_step_reducible',
                refine ⟨q, by simp [h.left], hq, p.lm, lm_mem_support hp₁, by simp [hp₃, hq'], _⟩,
                conv {
                    to_rhs, 
                    congr, rw [eqC_of_lm_eqz.1 hp₃], skip,
                    congr, rw [eqC_of_lm_eqz.1 hq'],
                },
                have : q 0 ≠ 0,
                    rw ←hq', simpa [mv_polynomial.lc] using lc_nez_iff.1 hq,
                simp [C, monomial_mul_monomial, hp₃, hq', mv_polynomial.lc, mul_div_cancel' _ this],
            },
            {
                simp [red_list_aux, hp₃, hq'] at hp₂,
                apply exists_red_of_red_list_aux_neq p l₁ l₂ h.right hp₂ hp₃,
            }
        }
    }
end

lemma red_list_red_plus : ∀ (p : mv_polynomial σ α) (l : list (mv_polynomial σ α)),
(p →[l.to_finset]+ red_list p l) 
| p l := begin
    unfold red_list, simp,
    by_cases hp₁ : red_list_aux p l = p; simp [hp₁],
    {exact rtc.refl'},
    {
        by_cases hp₂ : p.lm = 0; simp [hp₂],
        {apply rtc.base' (exists_red_of_red_list_aux_neq p l l (by simp) hp₁ hp₂)},
        {
            let : (red_list_aux p l).lm < p.lm, from red_list_aux_lm_lt' l p hp₂ hp₁,
            apply rtc.trans' (red_list_aux_red_plus p l)
                (red_list_red_plus _ l),
        }
    }
end
using_well_founded 
{ rel_tac := λ _ _, `[exact ⟨_, inv_image.wf (λ a, a.1.lm) _inst_6.wf⟩] 
, dec_tac := tactic.assumption }

lemma buchberger_buchplus : ∀ L : list (mv_polynomial σ α) × list (mv_polynomial σ α),
‘ L.1, L.2, s_polys L.1’→+‘buchberger ⟨L.1, L.2⟩, [], s_polys (buchberger ⟨L.1, L.2⟩)’
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

lemma buchstep_subset_or_red_eqz (L₁ L₂ : (list (mv_polynomial σ α) × list (mv_polynomial σ α)) × list (mv_polynomial σ α))
(h : buchstep_plus L₁ L₂) : (∀ a ∈ L₁.2, a ∈ L₁.1.2 ∨ (a →[L₁.1.1.to_finset]+ 0)) → 
∀ a ∈ L₂.2, a ∈ L₂.1.2 ∨ (a →[L₂.1.1.to_finset]+ 0) :=
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
            red_star_zero (h (s_poly q p) (by simp [s_polys, hq, mem_s_polyL hp])) 0 (-1),
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
    have := buchstep_subset_or_red_eqz ⟨⟨l, s_polys l⟩, s_polys l⟩ 
        ⟨⟨buchberger ⟨l, s_polys l⟩, []⟩, s_polys (buchberger ⟨l, s_polys l⟩)⟩ (buchberger_buchplus ⟨l, s_polys l⟩),
    simp at this,
    apply this,
    finish,
end

lemma buch_confluent (l : list (mv_polynomial σ α)) (p : mv_polynomial σ α) :
∀ {r t}, (p →[(buchberger ⟨l, s_polys l⟩).to_finset]* r) → (p →[(buchberger ⟨l, s_polys l⟩).to_finset]* t) → r = t :=
begin
    apply red_confluent,
    intros p q hp hq,
    apply buch_confluent_aux l p q (by simpa using hp) (by simpa using hq),
end

end step




end buch