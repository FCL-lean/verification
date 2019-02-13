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

end mv_polynomial