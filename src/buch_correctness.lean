import buchberger

open mv_polynomial
open finsupp

namespace buch
variables {σ : Type*} {α : Type*} [decidable_eq σ] [decidable_eq α] [discrete_field α] [fintype σ]
variables [decidable_linear_order (σ →₀ ℕ)]
/-
def red_one_step (S : finset (mv_polynomial σ α)) : mv_polynomial σ α → mv_polynomial σ α → Prop :=
    λ p q, ∃ (r : mv_polynomial σ α) (h₁ : r ∈ S) (h₂ : r.lm ∣ p.lm ), reduction p r = q

def red_plus (S : finset (mv_polynomial σ α)) : mv_polynomial σ α → mv_polynomial σ α → Prop := tc (red_one_step S)

def red_star (S : finset (mv_polynomial σ α)) : mv_polynomial σ α → mv_polynomial σ α → Prop := rtc (red_one_step S)

notation a `→[` S `]` b := red_one_step S a b

notation a `→[` S `]⁺` b := red_plus S a b

notation a `→[` S `]⋆` b := red_star S a b
-/


end buch