import linear_algebra.multivariate_polynomial
import tactic.find
universe k
variables {σ : Type*} {α : Type*}


variables [decidable_eq σ] [decidable_eq α]

variables [comm_semiring α] {p q : mv_polynomial σ α}
def rel (a : Sort k) : Sort (max k 1) := a → a → Prop  
def bin_op (a : Sort k) : Sort k := a → a → a

@[reducible]
def nocoeff_monomial_mul (a b: σ →₀ ℕ) : σ →₀ ℕ := a + b

structure monomial_order (le : rel (σ →₀ ℕ)) : Prop :=
(linear : is_linear_order (σ →₀ ℕ) le)
(mon_order : ∀ (a b w : σ →₀ ℕ), le a b
     → le (nocoeff_monomial_mul a w) (nocoeff_monomial_mul b w))



-- set_option trace.class_instances true

constant const_a : ℕ →₀ ℕ
section -- N-σ


#check (by apply_instance : lattice.distrib_lattice ℕ)
#check const_a.support.val

def truncate : (ℕ →₀ ℕ) → ℕ → (ℕ →₀ ℕ) := λ a n,

inductive ℕ_lt_ind (a b : ℕ →₀ ℕ) : ℕ → Prop
| le_zero : a 0 < b 0 → ℕ_lt_ind 0
| le_succ_fst : ∀ (n : ℕ), a (nat.succ n) < b (nat.succ n) 
                            → ℕ_lt_ind (nat.succ n)
| le_succ_snd : ∀ (n : ℕ), a (nat.succ n) = b (nat.succ n) 
                            → ℕ_lt_ind n → ℕ_lt_ind (nat.succ n)

def ℕ_lt_aux : (ℕ →₀ ℕ) → (ℕ →₀ ℕ) → ℕ → Prop
| a b 0 := a 0 < b 0
| a b (nat.succ n) := a (nat.succ n) < b (nat.succ n) 
                 ∨ ((a (nat.succ n) = b (nat.succ n)) ∧ ℕ_lt_aux a b n)

inductive status : Type
| empty : status
| incomplete : status
| complete : status
open status

inductive ℕ_lt_alt : (ℕ →₀ ℕ) → (ℕ →₀ ℕ) → ℕ → status → Prop
| lt_nil : ℕ_lt_alt 0 0 0 empty
| lt_cons_empty : ∀ (a b : ℕ →₀ ℕ) (n : ℕ) (x y : ℕ),
     ℕ_lt_alt a b n empty → 
     ℕ_lt_alt (a + finsupp.single n x) (b + finsupp.single n y) n incomplete
| lt_cons_empty_complete : ∀ (a b : ℕ →₀ ℕ) (n : ℕ) (x y: ℕ),
     ℕ_lt_alt a b n empty → 
     x < y →
     ℕ_lt_alt (a + finsupp.single n x) (b + finsupp.single n x) n complete
| lt_cons_nonempty : ∀ (a b : ℕ →₀ ℕ) (n : ℕ) (x y : ℕ),
     ℕ_lt_alt a b n incomplete → 
     ℕ_lt_alt (a + finsupp.single (nat.succ n) x) (b + finsupp.single (nat.succ n) y) (nat.succ n) incomplete
| lt_cons_nonempty_complete : ∀ (a b : ℕ →₀ ℕ) (n : ℕ) (x y : ℕ),
     ℕ_lt_alt a b n incomplete →
     x < y →
     ℕ_lt_alt (a + finsupp.single (nat.succ n) x) (b + finsupp.single (nat.succ n) y) (nat.succ n) complete
| lt_cons_nonempty_complete' : ∀ (a b : ℕ →₀ ℕ) (n : ℕ) (x : ℕ),
     ℕ_lt_alt a b n complete →
     ℕ_lt_alt (a + finsupp.single (nat.succ n) x) (b + finsupp.single (nat.succ n) x) (nat.succ n) complete

open ℕ_lt_alt
def smax (a b : ℕ →₀ ℕ) : ℕ := (a.support ∪ b.support).sup id


def ℕ_lt : rel (ℕ →₀ ℕ) := 
   λ a b, 
        ℕ_lt_aux a b (smax a b)

lemma lt_to_alt_aux: ∀ (a b : ℕ →₀ ℕ)  (n : ℕ), 
    ℕ_lt_aux a b n → ℕ_lt_alt a b n complete :=
begin
     intros,
     induction n,
     unfold ℕ_lt_aux at a_1,
     let t := lt_cons_empty_complete 0 0 0 (a 0) (b 0) lt_nil a_1,
     
end

lemma lt_to_alt: ∀ (a b : ℕ →₀ ℕ), ℕ_lt a b → ℕ_lt_alt a b (smax a b) complete :=
begin
     intros,
     unfold ℕ_lt at a_1,
end

def ℕ_le : rel (ℕ →₀ ℕ) :=
    λ a b, ℕ_lt a b ∨ ∀ (i : ℕ), a i = b i


def ℕ_le_alt : rel (ℕ →₀ ℕ) := 


lemma ℕ_mon_order_lem : ∀ (a b w : ℕ →₀ ℕ) (h h': ℕ),
     (h = finset.sup (a.support ∪ b.support) id) 
     → (h' = finset.sup ((nocoeff_monomial_mul a w).support ∪ (nocoeff_monomial_mul b w).support) id)
     → ℕ_le_ind a b h 
     → ℕ_le_aux (nocoeff_monomial_mul a w) (nocoeff_monomial_mul b w) h'
| a b w h h' p1 p2 lep := 
    begin
    end

def ℕ_mon_order : ∀ (a b w : ℕ →₀ ℕ) (m : ℕ), ℕ_le_ind a b m
    → ℕ_le (a + w) (b + w) 
| a b w m (ℕ_le_ind.le_zero p) :=
begin
     
end
| a b w m (ℕ_le_ind.le_succ_fst m' p) := sorry
| a b w m (ℕ_le_ind.le_succ_snd m' p ih) :=
begin
     exact ℕ_mon_order a b w m' ih
end

/-
begin
     intros a b w lep,
     unfold ℕ_le finset.sup lattice.has_sup.sup
       lattice.semilattice_sup.sup lattice.semilattice_sup_bot.sup 
       lattice.distrib_lattice.sup  lattice.lattice.sup at lep,
     unfold ℕ_le,
     induction lep,
     
end-/

def ℕ_le_is_monomial_order : monomial_order ℕ_le := sorry

end section

end

end