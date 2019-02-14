import linear_algebra.multivariate_polynomial ring_theory.noetherian

open finsupp
namespace mv_polynomial
variables {σ : Type*} {α : Type*} [decidable_eq σ] [decidable_eq α] [discrete_field α]

def HBT : is_noetherian (mv_polynomial σ α) (mv_polynomial σ α) := sorry

lemma ideal_wf : well_founded ((>) : ideal (mv_polynomial σ α) → ideal (mv_polynomial σ α) → Prop) := begin 
    rw ←is_noetherian_iff_well_founded, exact HBT,
end

end mv_polynomial