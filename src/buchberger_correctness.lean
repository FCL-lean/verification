import buchberger

variables {α : Type*}

namespace mv_polynomial
namespace fin_n
variables {n : ℕ}

variables [discrete_field α] [decidable_linear_order α] 

lemma subset_of_buch_result' : ∀ (s₁ s₂ : list (Σ' (p: mv_polynomial (fin n) α), p ≠ 0)), 
    (s₁ ⊆ s₂)
    → s₁ ⊆ buchberger s₂
|s₁ s₂ := λ hs, begin
    unfold buchberger, simp,
    let result := buch_div_result s₂ (filter_non_zero (buch_s_polys (buch_pairs s₂))),
    by_cases h : s₂ = result,
    rw if_pos h, assumption,
    rw if_neg h,
    let : non_zero_poly_to_ideal result > non_zero_poly_to_ideal s₂ := ideal_increase s₂ (ne.symm h),
    apply subset_of_buch_result s₁ result,
    apply list.subset.trans hs, 
    apply subset_of_buch_div_result _ s₂,
end
using_well_founded 
{ rel_tac := λ _ _, 
`[exact ⟨_, inv_image.wf (λ s, non_zero_poly_to_ideal s.2) seqR.ideal_wf⟩] 
, dec_tac := tactic.assumption }

lemma subset_of_buch_result (s: list (Σ' (p: mv_polynomial (fin n) α), p ≠ 0)) :
    s ⊆ buchberger s := subset_of_buch_result' s s (by simp)

end fin_n
end mv_polynomial

