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

section semilattice
variables [lattice.semilattice_sup_bot (σ →₀ ℕ)]

def leading_monomial (a: mv_polynomial σ α): σ →₀ ℕ := a.support.sup id

def leading_term (a: mv_polynomial σ α): mv_polynomial σ α 
    := finsupp.single (a.support.sup id) (a.to_fun (a.support.sup id))

def leading_coeff (a: mv_polynomial σ α): α := a.to_fun (a.support.sup id)


section decidable_linear_order
variables [decidable_linear_order α]

def leading_term_lcm (p q : mv_polynomial σ α) : mv_polynomial σ α := 
begin
    have hp := mv_trichotomy p,
    have hq := mv_trichotomy q,
    cases hp, exact mv_polynomial.C 0,
    cases hq, exact mv_polynomial.C 0,
    cases hp, all_goals {cases hq},
    exact mv_polynomial.C (max hp.fst hq.fst),
    exact monomial q.leading_monomial (max hp.fst (q.to_fun (q.leading_monomial))),
    exact monomial p.leading_monomial (max hq.fst (p.to_fun (p.leading_monomial))),
    begin
        let coeff := max (p.to_fun (p.leading_monomial)) (q.to_fun (q.leading_monomial)),
        let supp := finsupp.zip_with max (max_self 0) p.leading_monomial q.leading_monomial,
        exact monomial supp coeff,
    end
end

end decidable_linear_order
end semilattice

end comm_semiring
end general

end mv_polynomial