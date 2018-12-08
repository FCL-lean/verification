import linear_algebra.multivariate_polynomial
import finsupp
import finset
import fin
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

def lead_monomial_eqz_const {a : mv_polynomial σ α}:
    a.leading_monomial = 0 
    → Σ' (c : α), a = C c :=
λ eqz,
begin 
    sorry
end

lemma support_empty {a : mv_polynomial σ α} : a.support = ∅ → a.leading_monomial = ⊥ :=
λ h, begin
    unfold leading_monomial, rw [h], simp,
end

section finite_s
variable [fins: finite σ]
include fins

def leading_term_le (a b: mv_polynomial σ α): Prop
    := finsupp.leading_term_le a.leading_monomial b.leading_monomial

instance leading_term_le_dec (a b: mv_polynomial σ α): decidable (leading_term_le a b) :=
begin
    sorry
end

lemma zero_of_le_zero {a b : mv_polynomial σ α} : a.leading_monomial = 0
     → leading_term_le b a → b.leading_monomial = 0 := sorry

omit fins
end finite_s

lemma leading_term_ne_zero_coeff {a : mv_polynomial σ α} : 
    a.leading_monomial ≠ 0 → a.leading_coeff ≠ 0 :=
λ neqz eqa, sorry

lemma support_ne_empty_of_leading_term {a b : mv_polynomial σ α} : a.leading_monomial ≠ ⊥ 
    → a.leading_monomial = b.leading_monomial 
    → b.support ≠ ∅ := 
λ ha hab, begin
    rw hab at ha, intro h,
    apply absurd (support_empty h) ha,
end

lemma support_ne_empty_of_leading_term' {a : mv_polynomial σ α} : 
    a.leading_monomial ≠ ⊥
    → a.support ≠ ∅ := 
begin
    intros neqz neqz2,
    apply absurd (support_empty neqz2) neqz,
end

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

lemma const_support_zero {a : α} : (C a : mv_polynomial σ α).support = {0} := sorry

def leading_term_sub' {n} (a b: mv_polynomial (fin n) α) 
    (h: leading_term_le b a) : (fin n) →₀ ℕ
     := finsupp.fin_n.leading_term_sub a.leading_monomial b.leading_monomial
            h

end comm_semiring
end general

namespace fin_n
section div

variables {n : ℕ}

variables [discrete_field α]
variables [lt_wellfounded: @well_founded (fin n →₀ ℕ) (<)]

lemma sub_dec : Π (a b : mv_polynomial (fin n) α),
    a.leading_term = b.leading_term 
    → a.leading_monomial ≠ 0
→ (a - b).leading_monomial < a.leading_monomial :=
begin
    sorry
end

lemma lead_tm_eq {a b : mv_polynomial (fin n) α} (hb : b ≠ 0) (hab : leading_term_le b a) : 
    a.leading_term = leading_term (b * finsupp.single (leading_term_sub' a b hab) 
                (a.leading_coeff / b.leading_coeff)) := sorry

lemma nempty_of_const (a : α) : (a ≠ 0) → ((C a) : mv_polynomial (fin n) α).support ≠ ∅ := sorry

def div_const : Π (a b : mv_polynomial (fin n) α), b ≠ 0 →
                mv_is_const b →
                Σ' (q r : mv_polynomial (fin n) α), b.leading_monomial = r.leading_monomial
                        ∧ a = b * q + r
| a b bneqz bconst :=
begin
    sorry
end

include lt_wellfounded

def div : Π (a b : mv_polynomial (fin n) α),
                ¬ mv_is_const b →
                 Σ'q r, ¬ leading_term_le b r 
                        ∧ a = b * q + r
| a b bnconst :=
begin
    by_cases (leading_term_le b a),
    generalize subeq : leading_term_sub' a b h = sub,
    generalize q'eq : finsupp.single sub (a.leading_coeff / b.leading_coeff) = q',
    generalize h : a - b * q' = r',
    by_cases alt'eqz: a.leading_monomial = 0,
    let atmeqz := lead_monomial_eqz_const alt'eqz, 
    tactic.unfreeze_local_instances, dedup,
    let btmeqz := lead_monomial_eqz_const (zero_of_le_zero alt'eqz h),
    have atmeqzp := atmeqz.snd,
    have btmeqzp := btmeqz.snd,
    apply false.elim, apply ne_mv_is_const bnconst, assumption,
    let tt' : r'.leading_monomial < a.leading_monomial, 
    rw ←h,
    tactic.unfreeze_local_instances, dedup,
    apply sub_dec a (b * q'),
    rw [←q'eq, ←subeq], apply lead_tm_eq sorry h, assumption,
    have result := div r' b bnconst,
    cases result with r_q, cases result_snd with r_r,
    apply psigma.mk (q' + r_q),
    apply psigma.mk r_r,
    apply and.intro,
    exact result_snd_snd.left,
    have prf : a = b * q' + r',
    rw [←h],simp, 
    cases result_snd_snd,
    rw [prf, result_snd_snd_right],
    simp,
    rw left_distrib,
    apply psigma.mk (0 : mv_polynomial (fin n) α),
    apply psigma.mk a,
    apply and.intro, assumption,
    simp,
end
using_well_founded 
{ rel_tac := λ _ _, 
`[exact ⟨_, inv_image.wf psigma.fst (inv_image.wf leading_monomial lt_wellfounded)⟩] 
, dec_tac := tactic.assumption }

omit lt_wellfounded

end div
namespace fin_n

end mv_polynomial