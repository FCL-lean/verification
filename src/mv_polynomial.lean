import linear_algebra.multivariate_polynomial
import finsupp

variables {σ : Type*} {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {ι : Type*}

namespace mv_polynomial

section general
variables [decidable_eq σ] [decidable_eq α]

section comm_semiring
variables [comm_semiring α]

def mv_trichotomy (p : mv_polynomial σ α) : psum(p = C 0) 
            (psum (Σ'a : α, pprod (a ≠ 0) (p = C a)) ((Σ'a : α, p = C a) → false)):= 
if h₀ : p.support = ∅ 
    then
    begin
        rw iff.elim_left finsupp.support_eq_empty h₀,
        left, simp, refl,
    end
else if h₁ : p.support = {0} 
        then 
        begin
            right, left,
            unfold C monomial,
            apply (psigma.mk (p.to_fun 0)),
            apply pprod.mk, 
            exact finsupp.support_singleton_neq_zero h₁,
            apply finsupp.ext, intro,
            simp [finsupp.coe_f], unfold finsupp.single,
            by_cases 0 = a;
            simp [h], apply finsupp.support_singleton_eq_zero (ne.symm h) h₁,
        end
    else
    begin
        right, right,
        intro h, unfold C monomial finsupp.single at h,
        cases h,
        by_cases h_fst = 0; simp [h, h_snd] at *; assumption, 
    end
def mv_is_const_aux : Π (p : mv_polynomial σ α), (psum (p = mv_polynomial.C 0) 
            (psum (Σ'a : α, pprod (a ≠ 0) (p = mv_polynomial.C a)) 
                ((Σ'a : α, p = mv_polynomial.C a) → false))) → Prop
| p (psum.inl lp) := true
| p (psum.inr (psum.inl lp)) := true
| p (psum.inr (psum.inr rp)) := false

def mv_is_const (p : mv_polynomial σ α): Prop := mv_is_const_aux p (mv_trichotomy p)


def mv_is_const_neqz {p : mv_polynomial σ α}:
    mv_is_const p → p ≠ 0 → (Σ'a : α, pprod (a ≠ 0) (p = mv_polynomial.C a)) :=
begin
    intros, unfold mv_is_const at a,
    generalize h : mv_trichotomy p = m,
    rw h at a,
    cases m, rw m at a_1, apply false.elim, apply a_1, simp,
    cases m, assumption,
    unfold mv_is_const_aux at a,
    apply false.elim, assumption,
end

def ne_mv_is_const {p : mv_polynomial σ α}:
    ¬ mv_is_const p → (Σ'a : α, p = mv_polynomial.C a) → false :=
begin
    intros,
    generalize j : mv_trichotomy p = m,
    cases h:m, unfold mv_is_const at a,
    rw [j, h] at a, unfold mv_is_const_aux at a,
    apply a, trivial,
    cases h1:val, unfold mv_is_const at a,
    rw [j, h, h1] at a, unfold mv_is_const_aux at a,
    apply a, trivial, apply val_1, assumption,
end

instance (p : mv_polynomial σ α): decidable (mv_is_const p) :=
begin
    generalize t : mv_trichotomy p = m,
    cases h: m, apply is_true, rw val, simp,
    cases h: val, apply is_true, rw val_1.snd.snd, simp,
    unfold mv_is_const mv_is_const_aux,
    cases val_1, rw ←val_1_snd.snd, rw t,
    tactic.unfreeze_local_instances, dedup, 
    rw [h, h_1], unfold mv_is_const_aux,
    apply is_false, unfold mv_is_const,
    rw [t], tactic.unfreeze_local_instances, dedup,
    rw [h, h_1], unfold mv_is_const_aux, simp,
end


section semilattice
variables [lattice.semilattice_sup_bot (σ →₀ ℕ)]

def leading_monomial (a: mv_polynomial σ α): σ →₀ ℕ := a.support.sup id
def leading_term (a: mv_polynomial σ α): mv_polynomial σ α 
    := finsupp.single (a.support.sup id) (a.to_fun (a.support.sup id))

def leading_coeff (a: mv_polynomial σ α): α := a.to_fun (a.support.sup id)


def lead_tm'_eqz_const {a : mv_polynomial σ α}:
    a.leading_monomial = 0 
    → Σ' (c : α), a = C c :=
λ eqz,
begin 
    sorry
end


end semilattice

end comm_semiring
end general

end mv_polynomial