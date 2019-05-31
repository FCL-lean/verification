import order_mv_polynomial

open mv_polynomial finsupp

namespace mv_polynomial
variables {σ : Type*} {α : Type*} [decidable_eq σ] [decidable_eq α] [fintype σ] [decidable_linear_order (σ →₀ ℕ)] 
[is_well_founded (σ →₀ ℕ) (<)] [is_monomial_order (σ →₀ ℕ) (≤)] 
section lt
variables [comm_ring α]

inductive lt : (mv_polynomial σ α) → (mv_polynomial σ α) → Prop
| zero : ∀ {p : mv_polynomial σ α}, p ≠ 0 → lt 0 p
| LM_eq : ∀ {p q : mv_polynomial σ α}, q ≠ 0 → p.LM = q.LM → p.LC = q.LC → lt p.TL q.TL → lt p q
| LM_lt : ∀ {p q : mv_polynomial σ α}, p.LM < q.LM → lt p q

instance : has_lt (mv_polynomial σ α) := ⟨lt⟩

lemma LM_le_of_lt {x y : mv_polynomial σ α} (h : x < y) : x.LM ≤ y.LM := 
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
        conv at hy₂ {change y.LM = (monomial 0 a).LM, simp},
        conv at hy₃ {change y.LC = (monomial 0 a).LC, simp},
        conv at hy₄ {
            change lt y.TL (monomial 0 a).TL,
            simp [TL_eqz_of_LM_eqz hy₂, TL_eqz_of_LM_eqz (@LM_of_monomial' σ _ _ _ _ _ a)],
        },
        apply absurd hy₄ not_lt_zero,
    },
    {
        conv at hy {change y.LM < (monomial 0 a).LM, simp},
        apply absurd hy (finsupp.not_lt_zero _),
    }
end

lemma acc_monomial_add {a b} (h : acc (<) (monomial a b))
: ∀ p : mv_polynomial σ α, a > p.LM → b ≠ 0 → acc (<) (monomial a b + p) :=
λ p ha hb, begin
    have : acc (<) p := acc.inv h (lt.LM_lt (by simpa [hb] using ha)),
    induction this with x ih₁ ih₂,
    by_cases hx : x = 0,
    {simpa [hx] using h},
    {
        apply acc.intro,
        intros y hy,
        cases hy with _ _ _ _ hy₁ hy₂ hy₃ hy₄ _ _ hy,
        {simp [acc_zero]},
        {
            conv at hy₁ {change monomial a b + x ≠ 0},
            conv at hy₂ {change y.LM = (monomial a b + x).LM, rw LM_of_add_gt_LM ha hb},
            conv at hy₃ {change y.LC = (monomial a b + x).LC, rw LC_of_add_gt_LM ha hb},
            conv at hy₄ {change lt y.TL (monomial a b + x).TL, rw TL_of_add_gt_LM ha hb},
            rw [←LM_TL_eq y, hy₂, hy₃],
            apply ih₂ _ hy₄ (lt_of_le_of_lt (LM_le_of_lt hy₄) ha),
        },
        {
            conv at hy {
                change y.LM < (monomial a b + x).LM, 
                rw [LM_of_add_gt_LM ha hb, ←@LM_of_monomial _ _ _ _ _ _ a _ hb]
            },
            apply acc.inv h (lt.LM_lt hy),
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
            conv at hy₄ {change lt y.TL (monomial x b).TL, simp},
            apply absurd hy₄ not_lt_zero,
        },
        {
            by_cases hy' : y.LM = 0,
            {rw [eqC_of_LM_eqz.1 hy'], apply acc_C},
            {
                conv at hy {change y.LM < (monomial x b).LM, simp [hb]},
                rw ←LM_TL_eq y,
                apply acc_monomial_add (ih y.LM hy y.LC) _ (gt_TL_LM_of_LM_nez hy') (LC_nez_of_LM_nez hy'),
            }
        }
    }
end)

theorem lt_wf : well_founded ((<) : mv_polynomial σ α → mv_polynomial σ α → Prop) := 
well_founded.intro (λ p, begin
    by_cases hp : p.LM = 0,
    {rw eqC_of_LM_eqz.1 hp, apply acc_C},
    {
        rw ←LM_TL_eq p,
        apply acc_monomial_add (acc_monomial p.LM p.LC) _ (gt_TL_LM_of_LM_nez hp) (LC_nez_of_LM_nez hp),
    }
end)

instance : has_well_founded (mv_polynomial σ α) := 
{r := (<), wf := lt_wf}

lemma TL_lt {p : mv_polynomial σ α} (h : p ≠ 0) : p.TL < p :=
begin
    by_cases hp : p.LM = 0,
    {simp [TL_eqz_of_LM_eqz hp], exact lt.zero h},
    {
        apply lt.LM_lt,
        apply gt_TL_LM_of_LM_nez hp,
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
        {exact lt.LM_eq hr (by rwa hpq₁) (by rwa hpq₂) (ih _ hqr₃)},
        {exact lt.LM_lt (lt_of_le_of_lt (le_of_eq hpq₁) hqr)}
    },
    {
        cases hqr with _ _ _ _ hr hqr₁ hqr₂ hqr₃ _ _ hqr,
        {exact absurd hpq (finsupp.not_lt_zero _)},
        {exact lt.LM_lt (lt_of_lt_of_le hpq (le_of_eq hqr₁))},
        {exact lt.LM_lt (lt_trans hpq hqr)}
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