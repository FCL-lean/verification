import linear_algebra.multivariate_polynomial

universe k
variables {σ : Type*} {α : Type*}
variables [decidable_eq σ] [decidable_eq α]

variables [comm_semiring α] {p q : mv_polynomial σ α}

def rel (a : Sort k) : Sort (max k 1) := a → a → Prop  
def bin_op (a : Sort k) : Sort k := a → a → a
def nocoeff_monomial_mul (a b: σ →₀ ℕ) : σ →₀ ℕ := a + b

structure monomial_order (le : rel (σ →₀ ℕ)) 
     (s : σ →₀ ℕ) : Prop :=
(linear : is_linear_order (σ →₀ ℕ) le)
(mon_order : ∀ (a b w : σ →₀ ℕ), le a b
     → le (nocoeff_monomial_mul a w) (nocoeff_monomial_mul b w))

section -- N-σ

-- set_option trace.class_instances true
def ℕ_le : rel (ℕ →₀ ℕ) := λ a b,
     match decidable_eq (@finsupp.sum ℕ ℕ ℕ nat.has_zero nat.add_comm_monoid a (λ _ n, n) ) with
     | _ := sorry 
end section

end

end