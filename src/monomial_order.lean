import linear_algebra.multivariate_polynomial
import tactic.find
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
#check (by apply_instance : ∀ (a : ℕ →₀ ℕ), decidable (0 ∈ a.support))
-- set_option trace.class_instances true
def ℕ_le_aux : (ℕ →₀ ℕ) → (ℕ →₀ ℕ) → ℕ → Prop
| a b 0 := a 0 ≤ b 0
| a b (nat.succ n) := a (nat.succ n) ≤ b (nat.succ n) 
                 ∨ ((¬ a (nat.succ n) ≤ b (nat.succ n)) ∧ ℕ_le_aux a b n)

instance ℕ_max_comm : is_commutative ℕ (λ (m n : ℕ), ite (m < n) n m) 
  := ⟨begin 
     intros,
     unfold ite,
     let tri := lt_trichotomy a b,
     cases h': nat.decidable_lt a b;
     cases h1': nat.decidable_lt b a;
     simp, 

end⟩ 

def ℕ_le : rel (ℕ →₀ ℕ) := 
   λ a b, ℕ_le_aux a b ((a.support ∪ b.support).fold (λ m n, ite (m < n) n m) 0 id)


end section

end

end