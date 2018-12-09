import data.finsupp



class bot_zero (σ : Type*) (τ : Type*) 
    [has_zero τ][lattice.semilattice_sup_bot (σ →₀ τ)]
    [has_zero (σ →₀ τ)] :=
(zero_bot : (0: σ →₀ τ) = ⊥)