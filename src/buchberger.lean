import order_mv_polynomial
import util

open mv_polynomial
open finsupp

namespace buch
variables {σ : Type*} {α : Type*} [decidable_eq σ] [decidable_eq α] [discrete_field α]
variables [has_dec_linear_order (σ →₀ ℕ)]

section reduction

def reduction (a b : mv_polynomial σ α) (h : has_div a.hd b.hd) := a - b * (monomial (a.hd /ₘ b.hd ◂ h) (a.hd_val / b.hd_val))

def red_one_step (S : finset (mv_polynomial σ α)) : mv_polynomial σ α → mv_polynomial σ α → Prop :=
    λ p q, ∃ (r : mv_polynomial σ α) (h₁ : r ∈ S) (h₂ : has_div p.hd r.hd), reduction p r h₂ = q

def red_plus (S : finset (mv_polynomial σ α)) : mv_polynomial σ α → mv_polynomial σ α → Prop := tc (red_one_step S)

def red_star (S : finset (mv_polynomial σ α)) : mv_polynomial σ α → mv_polynomial σ α → Prop := rtc (red_one_step S)


notation a `→[` S `]` b := red_one_step S a b

notation a `→[` S `]⁺` b := red_plus S a b

notation a `→[` S `]⋆` b := red_star S a b

end reduction

def s_poly (p q : mv_polynomial σ α) : mv_polynomial σ α := 
    let X := m_lcm (hd p) (hd q) in
    let Xc := lcm (hd_val p) (hd_val q) in
    monomial (X /ₘ (hd p) ◂ (by apply m_lcm_has_div_left)) (Xc / (hd_val p)) * p - monomial (X /ₘ (hd q) ◂ (by apply m_lcm_has_div_right)) (Xc / (hd_val q)) * q

def s_polys (S : finset (mv_polynomial σ α)) : finset (mv_polynomial σ α) :=
do
    S.bind (λ a, 
        S.bind (λ b, 
            if a = b 
            then ∅
            else {s_poly a b}
        )
    )

def fileter_zero (S : finset (mv_polynomial σ α)) : finset (mv_polynomial σ α) := 
    finset.filter (λ a, a ≠ 0) S

end buch