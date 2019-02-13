import order_mv_polynomial

open mv_polynomial
open finsupp

namespace buch
variables {σ : Type*} {α : Type*} [decidable_eq σ] [decidable_eq α] [discrete_field α]
variables [has_dec_linear_order (σ →₀ ℕ)]

def s_poly (p q : mv_polynomial σ α) : mv_polynomial σ α := 
    let X := m_lcm (hd p) (hd q) in
    let Xc := lcm (hd_val p) (hd_val q) in
    monomial (m_sub X (hd p)) (Xc / (hd_val p)) * p - monomial (m_sub X (hd q)) (Xc / (hd_val q)) * q

end buch