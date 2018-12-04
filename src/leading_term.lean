import data.finset
import linear_algebra.multivariate_polynomial
import ring_theory.ideals
import tactic.find
import finsupp
import finset
import ideal


variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {ι : Type*}
variables [discrete_field α]
variables [decidable_eq α] [decidable_linear_order α]
-- variables [comm_ring (mv_polynomial ℕ α)]

namespace mv_polynomial
    
/-   dite (p.support.sort finsupp.le = list.nil) 
        (λ prf, mv_polynomial.C (p.to_fun 0))
        (λ nprf, let g := list.last (p.support.sort finsupp.le) nprf 
                 in finsupp.single g (p.to_fun g))-/

def leading_term' (p : mv_polynomial ℕ α) : ℕ →₀ ℕ := p.support.sup id

def leading_coeff (p : mv_polynomial ℕ α) : α := p.to_fun p.leading_term'

def leading_term (p : mv_polynomial ℕ α) : mv_polynomial ℕ α := finsupp.single p.leading_term' p.leading_coeff

def leading_term_le_aux : (ℕ →₀ ℕ) → (ℕ →₀ ℕ) → ℕ → Prop
| a b 0 := a 0 ≤ b 0
| a b (nat.succ m) := a (nat.succ m) ≤ b (nat.succ m) ∧ leading_term_le_aux a b m 

def leading_term_le (a b : ℕ →₀ ℕ) : Prop := leading_term_le_aux a b (finsupp.max_ab a b)

def leading_term_le' (a b : mv_polynomial ℕ α) : Prop := leading_term_le a.leading_term' b.leading_term'

/-
lemma le_imp_finsupp_le : ∀ a b : mv_polynomial ℕ α, a ≤ b → a.leading_term' ≤ b.leading_term' :=
λ a b, 
    begin 
        unfold has_le.le preorder.le finsupp.le mv_polynomial.le leading_term_le,
        induction (finsupp.max_ab (leading_term' a) (leading_term' b));
        unfold leading_term_le_aux finsupp.le_aux, simp,
        intro h,
        cases h.left, 
        rw le_iff_lt_or_eq at h,
        left, assumption,
        right, apply and.intro h_1 (ih h.right),
    end
-/

lemma mv_poly_le_refl : ∀ a : mv_polynomial ℕ α, leading_term_le' a a :=
λ a, 
begin 
    unfold leading_term_le' leading_term_le, 
    induction (finsupp.max_ab (leading_term' a) (leading_term' a));
    unfold leading_term_le_aux, 
    apply and.intro,
    refl, assumption,
end

lemma leading_term_le_aux_trans : ∀ (a b c : ℕ →₀ ℕ) (k : ℕ), (leading_term_le_aux a b k) → (leading_term_le_aux b c k) → (leading_term_le_aux a c k) :=
λ a b c k, begin
    induction k;
    unfold leading_term_le_aux,
    apply le_trans,
    intros hab hbc,
    apply and.intro, apply le_trans hab.left hbc.left,
    apply k_ih hab.right hbc.right,
end

lemma leading_term_le_aux_of_ge_max : ∀ (a b : mv_polynomial ℕ α) (i : ℕ), leading_term_le' a b 
    → i ≥ (finsupp.max_ab (leading_term' a) (leading_term' b)) 
    → leading_term_le_aux a.leading_term' b.leading_term' i :=
λ a b i h hi, begin 
    unfold leading_term_le' leading_term_le at h,
    induction i, rw nat.le_zero_iff.1 hi at h, assumption,
    from if hi₁ : nat.succ i_n = (finsupp.max_ab (leading_term' a) (leading_term' b))
    then by rw hi₁; assumption
    else begin
        have hi₂ := ne_iff_lt_or_gt.1 hi₁,
        cases hi₂, apply (absurd hi₂ (not_lt_of_ge hi)),
        unfold leading_term_le_aux,
        have hia := finsupp.gt_sup_eq_zero a.leading_term' (nat.succ i_n) (lt_of_le_of_lt (finsupp.max_ab_ge_max_a a.leading_term' b.leading_term') hi₂),
        have hib := finsupp.gt_sup_eq_zero b.leading_term' (nat.succ i_n) (lt_of_le_of_lt (finsupp.max_ab_ge_max_b a.leading_term' b.leading_term') hi₂),
        rw [hia, hib], apply and.intro, refl, apply i_ih (nat.le_of_lt_succ hi₂),
    end
end

lemma leading_term_le_of_ge_max_aux : ∀ (a b : mv_polynomial ℕ α) (i : ℕ), 
    leading_term_le_aux a.leading_term' b.leading_term' ((finsupp.max_ab (leading_term' a) (leading_term' b)) + i)
    → leading_term_le' a b :=
λ a b i h, begin
    induction i, unfold leading_term_le' leading_term_le, assumption,
    unfold leading_term_le_aux at h,
    apply i_ih h.right,
end

lemma mv_poly_le_trans : ∀ a b c : mv_polynomial ℕ α, leading_term_le' a b → leading_term_le' b c → leading_term_le' a c :=
λ a b c hab hbc, 
begin 
    unfold leading_term_le leading_term_le' at hab hbc,
    generalize hs : [(finsupp.max_ab a.leading_term' b.leading_term'), (finsupp.max_ab b.leading_term' c.leading_term'), (finsupp.max_ab a.leading_term' c.leading_term')] = s,
    generalize hk: s.to_finset.sup id = k, rw [←hs] at hk,
    have hkab : (finsupp.max_ab a.leading_term' b.leading_term') ≤ k, rw ←hk, simp,
    have hkbc : (finsupp.max_ab b.leading_term' c.leading_term') ≤ k, rw ←hk, simp, rw ←lattice.sup_assoc, apply lattice.le_sup_right,
    have hkac : (finsupp.max_ab a.leading_term' c.leading_term') ≤ k, rw ←hk, simp, rw [lattice.sup_comm, lattice.sup_assoc], apply lattice.le_sup_left,
    have hab' := leading_term_le_aux_of_ge_max a b k hab hkab,
    have hbc' := leading_term_le_aux_of_ge_max b c k hbc hkbc,
    have hac' := leading_term_le_aux_trans a.leading_term' b.leading_term' c.leading_term' k hab' hbc',
    apply leading_term_le_of_ge_max_aux a c ((k - (finsupp.max_ab a.leading_term' c.leading_term'))),
    rw nat.add_sub_of_le hkac,
    assumption,
end

instance mv_poly_le_decidable (a b : mv_polynomial ℕ α) : decidable (leading_term_le' a b) := 
begin
    unfold leading_term_le' leading_term_le,
    induction (finsupp.max_ab (leading_term' a) (leading_term' b));
    unfold leading_term_le_aux, apply_instance,
    cases ih,
    begin left, intro h, apply (absurd h.right ih), end,
    from if h: (a.leading_term'.to_fun (nat.succ n) ≤ b.leading_term'.to_fun (nat.succ n))
    then is_true begin apply and.intro; assumption, end
    else is_false begin intro h', apply (absurd h'.left h), end,
end


def leading_term_sub_aux (a b : ℕ →₀ ℕ) 
   : Π (k: ℕ), (leading_term_le_aux b a k) → (ℕ →₀ ℕ) 
| nat.zero le := finsupp.single 0 (a 0 - b 0)
| (nat.succ n) le := begin cases le, exact leading_term_sub_aux n le_right end

def leading_term_sub (a b : ℕ →₀ ℕ) : (leading_term_le b a) → (ℕ →₀ ℕ) 
| le := leading_term_sub_aux a b (finsupp.max_ab b a) le

constant lt_wellfounded : well_founded (@preorder.lt (ℕ →₀ ℕ) _)


lemma support_empty {a : mv_polynomial ℕ α} : a.support = ∅ → a.leading_term' = 0 :=
λ h, begin
    unfold leading_term', rw [h], simp [finset.sort_nil finsupp.le], refl,
end

lemma leading_coeff_not0 {a : mv_polynomial ℕ α} : a.support ≠ ∅ → a.leading_coeff ≠ 0 :=
λ ha halc, begin
    unfold leading_coeff leading_term' at halc,
    have h := finsupp.mem_support_iff.1 (finset.mem_of_sup_id ha),
    apply absurd halc h,
end

lemma support_ne_empty_of_leading_term {a b : mv_polynomial ℕ α} : a.leading_term' ≠ 0 
    → a.leading_term' = b.leading_term' 
    → b.support ≠ ∅ := 
λ ha hab, begin
    rw hab at ha, intro h,
    apply absurd (support_empty h) ha,
end

lemma support_ne_empty_of_leading_term' {a : mv_polynomial ℕ α} : 
    a.leading_term' ≠ 0 
    → a.support ≠ ∅ := 
begin
    intros neqz neqz2,
    apply absurd (support_empty neqz2) neqz,
end
lemma leading_term_ne_zero_coeff {a : mv_polynomial ℕ α} : 
    a.leading_term' ≠ 0 → a.leading_coeff ≠ 0 :=
λ neqz eqa,
begin
    unfold leading_coeff at eqa, unfold leading_term' at neqz,
    have h' : a.support ≠ ∅ := sorry,
    have h := finset.mem_of_sup_id h',
    rw [finsupp.mem_support_iff] at h,
    exact absurd eqa h,
end

end mv_polynomial