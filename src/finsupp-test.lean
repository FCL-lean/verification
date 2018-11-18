import data.finsupp
import linear_algebra.multivariate_polynomial
import ring_theory.ideals
import data.zmod.basic
import linear_algebra.basic
variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {ι : Type*}
variables {σ : Type*}
variables [comm_ring α]
variables [decidable_eq σ] [decidable_eq α]
open mv_polynomial
#print submodule.lattice.has_Inf
def coeff_add : list α → list α → list α
| [] x := x
| x  [] := x
| (x :: xs) (y :: ys) := (x + y) :: coeff_add xs ys

def length_preserving : Π {s: Type*} (a b : list s), 
                           (list s → list s → list s) → 
                           Prop := λ s a b f, a.length = b.length → 
                                              a.length = (f a b).length 

lemma coeff_add_is_length_preserving : ∀ (a b : list α), 
                  length_preserving a b coeff_add :=
begin
    intro a, induction a; intro b; 
    unfold length_preserving; intros,
    cases b, simp, unfold coeff_add, simp, cases a,
    cases b, unfold coeff_add, unfold coeff_add, simp, 
    simp at a, let a_ih' := a_ih b_tl, unfold length_preserving at a_ih',
    exact a_ih' a,
end

def prod' : Π (x: list α) (y: list (mv_polynomial σ α)), (x.length = y.length) 
                                → mv_polynomial σ α
| [] [] rfl := 0
| (x :: xs) (y :: ys) p := C x * y + prod' xs ys (by simp at p; assumption)
def fin_gen (S: list (mv_polynomial σ α)) := 
      { x : mv_polynomial σ α | ∃ (coeff : list α) 
                    (h: coeff.length = S.length), prod' coeff S h = x }
-- is_ideal (fin_gen S) = is_submodule (fin_gen S : set (mv_poly σ α))

-- class is_submodule {α : Type u} {β : Type v} [ring α] [module α β] (p : set β) : Prop
-- class is_ideal {α : Type u} [comm_ring α] (S : set α) extends is_submodule S : Prop

-- module α (mv_polynomial σ α)
-- is_submodule S
open lattice
-- set_option trace.class_instances true
-- #print total_degree
def span' (s : set (mv_polynomial σ α)) : submodule α (mv_polynomial σ α) 
            := Inf (λ p, s ⊆ p) -- {p | s ⊆ p}
-- set of submodules, 
constant t : set (mv_polynomial σ α)
constant t2 : submodule α (mv_polynomial σ α)
def test : true :=
begin
    let m : submodule.span t = t2, swap,
    unfold submodule.span at m,
    unfold submodule.span,
    unfold Inf, unfold has_Inf.Inf,
    unfold set.Inter, unfold infi, unfold Inf, unfold has_Inf.Inf,
    unfold complete_lattice.Inf, unfold set.range, unfold set_of,
    unfold has_mem.mem, unfold set.mem, simp, 
end


-- set_option trace.simplify.rewrite true
instance (S: list (mv_polynomial σ α)) : add_comm_semigroup (fin_gen S) := 
{ add_assoc := sorry,
  add_comm := sorry,
  add := λ x y, ⟨x.val + y.val, 
     begin 
        unfold fin_gen, 
        rw [set.mem_set_of_eq], 
        cases x.property, cases y.property,
        cases h, cases h_1,
        apply exists.intro,
        swap, exact coeff_add w w_1,
        unfold coeff_add,
        apply exists.intro, swap,
        symmetry,
        rw [←h_w] at *,
        apply coeff_add_is_length_preserving w w_1,
        symmetry, assumption,
        rw [←h_1_h, ← h_h],
    end⟩ }

instance (S: list (mv_polynomial σ α)) : comm_ring (fin_gen S) := sorry

def ideal_mv_poly (S: list (mv_polynomial σ α)) : ideal (fin_gen S) := sorry
