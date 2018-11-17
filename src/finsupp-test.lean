import data.finsupp
import linear_algebra.multivariate_polynomial
import ring_theory.ideals
variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {ι : Type*}
variables {σ : Type*}
variables [comm_ring α]
variables [decidable_eq σ] [decidable_eq α]
open mv_polynomial
def prod' : Π (x: list α) (y: list (mv_polynomial σ α)), (x.length = y.length) → mv_polynomial σ α
| [] [] rfl := 0
| (x :: xs) (y :: ys) p := C x * y + prod' xs ys (by simp at p; assumption)
def fin_gen (S: list (mv_polynomial σ α)) := { x : mv_polynomial σ α | ∃ (coeff : list α) (h: coeff.length = S.length), prod' coeff S h = x }
-- is_ideal (fin_gen S) = is_submodule (fin_gen S : set (mv_poly σ α))

-- class is_submodule {α : Type u} {β : Type v} [ring α] [module α β] (p : set β) : Prop
-- class is_ideal {α : Type u} [comm_ring α] (S : set α) extends is_submodule S : Prop

-- module α (mv_polynomial σ α)
-- is_submodule S
instance (S: list (mv_polynomial σ α)) : is_ideal (fin_gen S) := sorry
