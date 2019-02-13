import linear_algebra.multivariate_polynomial
import has_dec_linear_order
import order_finsupp

open finsupp
namespace mv_polynomial

section gcd_domain 
variables {σ : Type*} {α : Type*} [gcd_domain α] [decidable_eq α] [decidable_eq σ]
variables [has_dec_linear_order (σ →₀ ℕ)]

def lm_lcm (p q : mv_polynomial σ α) : mv_polynomial σ α :=
    monomial (m_lcm p.hd q.hd ) (lcm p.hd_val q.hd_val)

end gcd_domain

section discrete_field
variables {σ : Type*} {α : Type*} [decidable_eq σ] [decidable_eq α] [discrete_field α]
variables [has_dec_linear_order (σ →₀ ℕ)]

def s_poly (p q : mv_polynomial σ α) : mv_polynomial σ α := 
    let lm : (σ →₀ ℕ →₀ α) → (σ →₀ ℕ) := hd in
    let lc : (σ →₀ ℕ →₀ α) → α := hd_val in
    let X := m_lcm (lm p) (lm q) in
    let Xc := lcm (lc p) (lc q) in
    monomial (m_sub X (lm p)) (Xc / (lc p)) * p - monomial (m_sub X (lm q)) (Xc / (lc q)) * q

end discrete_field

end mv_polynomial