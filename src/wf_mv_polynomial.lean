import order_mv_polynomial

open mv_polynomial finsupp

namespace mv_polynomial
variables {σ : Type*} {α : Type*} [decidable_eq σ] [decidable_eq α] [fintype σ] [decidable_linear_order (σ →₀ ℕ)] 
[is_well_founded (σ →₀ ℕ) (<)] [is_monomial_order (σ →₀ ℕ) (≤)] 
section lt
variables [comm_ring α]

lemma tl_eqz_of_lm_eqz {p : mv_polynomial σ α} (h : p.lm = 0) : p.tl = 0 :=
begin
    by_contradiction,
    apply (not_lt_of_le (finsupp.zero_le p.tl.lm)),
    simpa [h] using lm_rel_gt _ _ (lm_mem_support a),
end

lemma gt_tl_lm_of_lm_nez {p : mv_polynomial σ α} (h : p.lm ≠ 0) : p.lm > p.tl.lm :=
begin
    by_cases htl : p.tl = 0,
    {simp [htl], apply finsupp.zero_lt_iff_ne_zero.2 h},
    {apply lm_rel_gt _ _ (lm_mem_support htl)},
end

inductive lt : (mv_polynomial σ α) → (mv_polynomial σ α) → Prop
| zero : ∀ {p : mv_polynomial σ α}, p ≠ 0 → lt 0 p
| lm_eq : ∀ {p q : mv_polynomial σ α}, q ≠ 0 → p.lm = q.lm → p.lc = q.lc → lt p.tl q.tl → lt p q
| lm_lt : ∀ {p q : mv_polynomial σ α}, p.lm < q.lm → lt p q

instance : has_lt (mv_polynomial σ α) := ⟨lt⟩

lemma lm_le_of_lt {x y : mv_polynomial σ α} (h : x < y) : x.lm ≤ y.lm := 
begin
    cases h,
    simp [finsupp.zero_le],
    apply le_of_eq, assumption,
    apply le_of_lt, assumption,
end

lemma not_lt_zero {x : mv_polynomial σ α} : ¬ x < 0 :=
λ h, begin
    cases h,
    {finish},
    {finish},
    {apply (not_lt_zero _) (by simpa using h_a)},
end

lemma acc_zero : acc ((<) : mv_polynomial σ α → mv_polynomial σ α → Prop) 0 := 
begin
    apply acc.intro,
    intros y hy,
    apply absurd hy not_lt_zero,
end

lemma acc_C : ∀ a, acc ((<) : mv_polynomial σ α → mv_polynomial σ α → Prop) (C a) :=
λ a, begin
    apply acc.intro,
    intros y hy,
    cases hy with _ _ _ _ hy₁ hy₂ hy₃ hy₄ _ _ hy,
    {simp [acc_zero]},
    {
        conv at hy₂ {change y.lm = (monomial 0 a).lm, simp},
        conv at hy₃ {change y.lc = (monomial 0 a).lc, simp},
        conv at hy₄ {
            change lt y.tl (monomial 0 a).tl,
            simp [tl_eqz_of_lm_eqz hy₂, tl_eqz_of_lm_eqz (@lm_of_monomial' σ _ _ _ _ _ a)],
        },
        apply absurd hy₄ not_lt_zero,
    },
    {
        conv at hy {change y.lm < (monomial 0 a).lm, simp},
        apply absurd hy (finsupp.not_lt_zero _),
    }
end

lemma acc_monomial_add (p : mv_polynomial σ α)
(h : acc ((<) : mv_polynomial σ α → mv_polynomial σ α → Prop) p)
: ∀ a b, a > p.lm → b ≠ 0 → acc (<) (monomial a b) → acc (<) (monomial a b + p) :=
begin
    apply acc.rec_on h,
    intros _ ih₁ ih₂ a b ha hb h,
    by_cases hx : x = 0,
    {simpa [hx] using h},
    {
        apply acc.intro,
        intros y hy,
        cases hy with _ _ _ _ hy₁ hy₂ hy₃ hy₄ _ _ hy,
        {simp [acc_zero]},
        {
            conv at hy₁ {change monomial a b + x ≠ 0},
            conv at hy₂ {change y.lm = (monomial a b + x).lm, rw lm_of_add_gt_lm ha hb},
            conv at hy₃ {change y.lc = (monomial a b + x).lc, rw lc_of_add_gt_lm ha hb},
            conv at hy₄ {change lt y.tl (monomial a b + x).tl, rw tl_of_add_gt_lm ha hb},
            rw [←lm_tl_eq y, hy₂, hy₃],
            apply ih₂ _ hy₄ _ _ (lt_of_le_of_lt (lm_le_of_lt hy₄) ha) hb h,
        },
        {
            conv at hy {
                change y.lm < (monomial a b + x).lm, 
                rw [lm_of_add_gt_lm ha hb, ←@lm_of_monomial _ _ _ _ _ _ a _ hb]
            },
            apply acc.inv h (lt.lm_lt hy),
        }
    }
end

lemma acc_monomial : ∀ a b, acc ((<) : mv_polynomial σ α → mv_polynomial σ α → Prop) (monomial a b) := 
λ a,  well_founded.recursion _inst_5.wf a (begin
    intros x ih b,
    by_cases hb : b = 0,
    {simp [hb, acc_zero]},
    {
        apply acc.intro,
        intros y hy,
        cases hy with _ _ _ _ hy₁ hy₂ hy₃ hy₄ _ _ hy,
        {simp [acc_zero]},
        {
            conv at hy₄ {change lt y.tl (monomial x b).tl, simp},
            apply absurd hy₄ not_lt_zero,
        },
        {
            by_cases hy' : y.lm = 0,
            {rw [eqC_of_lm_eqz.1 hy'], apply acc_C},
            {
                conv at hy {change y.lm < (monomial x b).lm, simp [hb]},
                have h := ih y.lm hy y.lc,
                rw ←lm_tl_eq y,
                apply acc_monomial_add _ _ _ _ (gt_tl_lm_of_lm_nez hy') (lc_nez_of_lm_nez hy') h,
                {
                    apply acc.inv h,
                    apply lt.lm_lt, 
                    simp [lc_nez_of_lm_nez hy'],
                    apply gt_tl_lm_of_lm_nez hy',
                },
            }
        }
    }
end)

lemma lt_wf : well_founded ((<) : mv_polynomial σ α → mv_polynomial σ α → Prop) := 
well_founded.intro (λ p, begin
    by_cases hp : p.lm = 0,
    {rw eqC_of_lm_eqz.1 hp, apply acc_C},
    {
        rw ←lm_tl_eq p,
        have h := acc_monomial p.lm p.lc,
        apply acc_monomial_add _ _ _ _ (gt_tl_lm_of_lm_nez hp) (lc_nez_of_lm_nez hp) h,
        {
            apply acc.inv h,
            apply lt.lm_lt, 
            simp [lc_nez_of_lm_nez hp],
            apply gt_tl_lm_of_lm_nez hp,
        }
    }
end)

instance : has_well_founded (mv_polynomial σ α) := 
{r := (<), wf := lt_wf}

lemma tl_lt {p : mv_polynomial σ α} (h : p ≠ 0) : p.tl < p :=
begin
    by_cases hp : p.lm = 0,
    {simp [tl_eqz_of_lm_eqz hp], exact lt.zero h},
    {
        apply lt.lm_lt,
        apply gt_tl_lm_of_lm_nez hp,
    }
end

lemma nez_of_gt {p q : mv_polynomial σ α} (h : p < q) : q ≠ 0 :=
λ h', begin
    rw h' at h,
    exact not_lt_zero h,
end

lemma gt_zero_of_gt {p q : mv_polynomial σ α} (h : p < q) : 0 < q := lt.zero (nez_of_gt h)

instance : is_trans (mv_polynomial σ α) (<) :=
⟨λ p q r hpq, begin 
    revert r,
    induction hpq with _ _ p q hq hpq₁ hpq₂ hpq₃ ih p q hpq;
    intros r hqr,
    {exact gt_zero_of_gt hqr},
    {
        cases hqr with _ _ _ _ hr hqr₁ hqr₂ hqr₃ _ _ hqr,
        {finish},
        {exact lt.lm_eq hr (by rwa hpq₁) (by rwa hpq₂) (ih _ hqr₃)},
        {exact lt.lm_lt (lt_of_le_of_lt (le_of_eq hpq₁) hqr)}
    },
    {
        cases hqr with _ _ _ _ hr hqr₁ hqr₂ hqr₃ _ _ hqr,
        {exact absurd hpq (finsupp.not_lt_zero _)},
        {exact lt.lm_lt (lt_of_lt_of_le hpq (le_of_eq hqr₁))},
        {exact lt.lm_lt (lt_trans hpq hqr)}
    }
end⟩

instance : is_irrefl (mv_polynomial σ α) (<) :=
⟨λ p, begin
    apply induction p,
    {exact not_lt_zero},
    {
        intros p ih hp,
        cases hp with _ _ _ _ hp h₁ h₂ h₃ _ _ h,
        {finish},
        {exact ih h₃},
        {exact (lt_irrefl _) h}
    }
end⟩

end lt
end mv_polynomial