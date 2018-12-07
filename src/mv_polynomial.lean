import linear_algebra.multivariate_polynomial
variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {ι : Type*}
variables [discrete_field α]
variables [decidable_eq α] [decidable_linear_order α]
variables [lattice.semilattice_sup_bot (β →₀ ℕ)] [decidable_eq (β →₀ ℕ)]
namespace mv_polynomial

section general

def leading_term' (a: mv_polynomial β α): β →₀ ℕ := a.support.sup id
def leading_term (a: mv_polynomial β α): mv_polynomial β α 
    := finsupp.single (a.support.sup id) (a.to_fun (a.support.sup id))

def leading_coeff (a: mv_polynomial β α): α := a.to_fun (a.support.sup id)
end general

end mv_polynomial