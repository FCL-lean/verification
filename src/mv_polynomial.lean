import linear_algebra.multivariate_polynomial
import finsupp
import finset
import fintype
import fin
import noetherian
import seq
import bot_zero
variables {σ : Type*} {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {ι : Type*}

namespace mv_polynomial

section general
variables [decidable_eq σ] [decidable_eq α]

section discrete_field
variable [discrete_field α]

instance HBT : noetherian (mv_polynomial σ α) := sorry

end discrete_field

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

lemma eq_mv_is_const {p : mv_polynomial σ α} :
    mv_is_const p → Σ'a : α, p = C a :=
λ h, begin
    generalize hp_tri : mv_trichotomy p = p_tri,
    unfold mv_is_const at h, rw hp_tri at h,
    cases p_tri, apply psigma.mk (0 : α), assumption,
    cases p_tri, apply psigma.mk p_tri.1, exact p_tri.2.2,
    unfold mv_is_const_aux at h, apply psigma.mk (0 : α), revert h, simp,
end

lemma eq_mv_is_const' {p : mv_polynomial σ α} :
    (Σ' a : α, p = C a) → mv_is_const p :=
λ h, begin
    unfold mv_is_const,
    cases mv_trichotomy p, simp [mv_is_const_aux],
    cases val, simp [mv_is_const_aux],
    simp [mv_is_const_aux], exact val h,
end

lemma ne_mv_is_const {p : mv_polynomial σ α}:
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

lemma nzero_of_ne_mv_is_const {p : mv_polynomial σ α} : 
    ¬ mv_is_const p → p ≠ 0 :=
λ h, begin
    let ne_p := ne_mv_is_const h,
    intro, apply ne_p,
    apply psigma.mk (0 : α), simp [a],
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
variables [bot_zero σ ℕ]
def leading_monomial (a: mv_polynomial σ α): σ →₀ ℕ := a.support.sup id

def leading_coeff (a: mv_polynomial σ α): α := a.to_fun a.leading_monomial

def leading_term (a: mv_polynomial σ α): mv_polynomial σ α 
    := finsupp.single a.leading_monomial a.leading_coeff

section is_total
variables [is_total (σ →₀ ℕ) has_le.le] [@decidable_rel (σ →₀ ℕ) has_le.le]

lemma eq_zero_leading_monomial_not_mem_iff {p : mv_polynomial σ α} : p.to_fun p.leading_monomial = 0 ↔ p = 0 :=
begin
    unfold leading_monomial,
    apply iff.intro; intro h;
    rw [←finsupp.coe_f, ←finsupp.not_mem_support_iff] at *,
    apply finsupp.support_eq_empty.1 (finset.empty_of_sup_id_not_mem h),
    simp [h], apply finsupp.zero_apply,
end

lemma leading_monomial_const_iff {p : mv_polynomial σ α} : 
    mv_is_const p.leading_term ↔ p.leading_monomial = ⊥ :=
begin
    apply iff.intro; intro h,
    rw ←_inst_5.zero_bot,
    have h' := eq_mv_is_const h,
    unfold leading_term C monomial at h', {
        from if hpcz :p.leading_coeff = 0
        then 
            begin 
                simp [leading_coeff, eq_zero_leading_monomial_not_mem_iff] at hpcz, simp [leading_monomial, hpcz, _inst_5.zero_bot], 
                change finset.sup ∅ id = ⊥, exact finset.sup_empty,
            end
        else by apply finsupp.single_inj1 hpcz h'.2
    },
    rw [←_inst_5.zero_bot] at h,
    simp [leading_term, h],
    change mv_is_const (C p.leading_coeff),
    apply eq_mv_is_const',
    apply psigma.mk p.leading_coeff,
    refl,
end

set_option trace.check true
def lead_monomial_eqz_const {a : mv_polynomial σ α}:
    a.leading_monomial = ⊥ → Σ' (c : α), a = C c :=
λ eqz,
begin 
    unfold leading_monomial at eqz,
    have h: a.support = ∅ ∨ a.support = {⊥}, from finset.sup_bot a.support eqz,
    apply psigma.mk (a.to_fun ⊥),
    cases h,
    begin
        rw finsupp.support_eq_empty at h,
        rw [←finsupp.coe_f, h], simpa,
    end,
    begin
        simp [C, monomial, finsupp.single], apply finsupp.ext,
        intro val, simp [finsupp.coe_f],
        by_cases 0 = val; simp [h], rw [←h],
        apply congr_arg, rw _inst_5.zero_bot,
        rw [←finsupp.coe_f, ←finsupp.not_mem_support_iff],
        tactic.unfreeze_local_instances, dedup,
        rw h, simp, rw ←_inst_5.zero_bot,
        intro neq, apply h_1, symmetry, assumption,
    end
end

lemma const_of_support_singleton {p : mv_polynomial σ α} (h : p.support = {0}) : Σ' a : α, p = C a :=
begin
    apply psigma.mk (p.to_fun 0), unfold C monomial finsupp.single,
    apply finsupp.ext, intro a,
    from if ha : a = 0
    then by simp [finsupp.coe_f, ha.symm]
    else begin 
        rw [←ne.def] at ha,
        simp [finsupp.coe_f, ne.symm ha],
        rw [←finsupp.coe_f, ←finsupp.not_mem_support_iff, h],
        apply finset.not_mem_singleton.2 ha,
    end
end


lemma poly_lead_coeff_z {p : mv_polynomial σ α}: 
    p.leading_coeff = 0 → p = 0 :=
λ coeffz,
begin
    unfold leading_coeff leading_monomial at coeffz,
    rw [←finsupp.coe_f, ←finsupp.not_mem_support_iff] at coeffz,
    have h: p.support = ∅,
    by_cases p.support = ∅,
    assumption,
    apply false.elim, apply coeffz,
    apply finset.mem_of_sup_id, assumption,
    rw finsupp.support_eq_empty at h,
    assumption,
end

lemma poly_lead_tm_neqz {p : mv_polynomial σ α}: p ≠ 0 → p.leading_term ≠ 0 :=
λ pneqz eqz,
begin 
    apply pneqz,
    unfold leading_term at eqz,
    have eqz' := finsupp.single_eqz eqz,
    exact poly_lead_coeff_z eqz',
end

lemma const_support_zero {a : α} (h : a ≠ 0) : (C a : mv_polynomial σ α).support = {0} := 
by unfold C monomial finsupp.single; simp [h]

lemma leading_term_nconst_of_nconst 
    {p : mv_polynomial σ α} (h : ¬mv_is_const p): ¬ mv_is_const p.leading_term :=
begin
    intro h',
    have hp := ne_mv_is_const h,
    rw leading_monomial_const_iff at h',
    apply hp (lead_monomial_eqz_const h'),
end

lemma leading_term_ne_zero_coeff {a : mv_polynomial σ α} : 
    a.leading_monomial ≠ 0 → a.leading_coeff ≠ 0 :=
λ neqz eqa, begin
    unfold leading_monomial at neqz,
    unfold leading_coeff at eqa,
    rw [←finsupp.coe_f, ←finsupp.not_mem_support_iff] at eqa,
    apply eqa, apply finset.mem_of_sup_id,
    intro eqe, rw eqe at *,
    simp at neqz,
    apply neqz, rw _inst_5.zero_bot,
end

end is_total

lemma support_empty {a : mv_polynomial σ α} : a.support = ∅ → a.leading_monomial = ⊥ :=
λ h, begin
    unfold leading_monomial, rw [h], simp,
end

section fintype_s
variable [fins: fintype σ]
include fins

def leading_term_le (a b: mv_polynomial σ α): Prop
    := finsupp.leading_term_le a.leading_monomial b.leading_monomial

instance leading_term_le_dec (a b: mv_polynomial σ α): decidable (leading_term_le a b) :=
begin
    unfold leading_term_le finsupp.leading_term_le,
    apply fintype.fintype_fold_dec,
    intro, apply_instance,
end

lemma leading_monomial_zero_of_le_zero {a b : mv_polynomial σ α} : a.leading_monomial = 0
     → leading_term_le b a → b.leading_monomial = 0 := 
λ ha hba, begin
    simp [leading_term_le, finsupp.leading_term_le, ha, fintype.fintype_fold_and_iff] at hba,
    apply finsupp.ext, simp [hba],
end

omit fins
end fintype_s


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

def leading_term_sub' {n} (a b: mv_polynomial (fin n) α) [bot_zero (fin n) ℕ]
    (h: leading_term_le b a) : fin n →₀ ℕ
     := finsupp.fin_n.leading_term_sub a.leading_monomial b.leading_monomial h

end comm_semiring
end general

namespace fin_n
variables {n : ℕ}

variables [discrete_field α]
variables (lt_wellfounded: @well_founded (fin n →₀ ℕ) (<))
variable [bot_zero (fin n) ℕ]

section div
lemma lead_tm_eq_notin_supp
    : Π {a b: mv_polynomial (fin n) α},
    leading_term a = leading_term b
    → a.leading_monomial ≠ 0
    → a.leading_monomial ∉ (a - b).support :=
λ a b eql neq0 insub,
begin
    unfold leading_term at eql,
    have coeff_neq_z := leading_term_ne_zero_coeff neq0,
    have lead_tm_eq := finsupp.single_inj1 coeff_neq_z eql,
    have lead_coeff_eq := finsupp.single_inj2 eql,
    rw finsupp.mem_support_iff at insub,
    apply insub,
    change (a - b).to_fun (leading_monomial a) = 0,
    unfold has_sub.sub algebra.sub,
    rw [←finsupp.coe_f, finsupp.add_apply],
    unfold leading_coeff at lead_coeff_eq,
    rw [←finsupp.coe_f] at lead_coeff_eq,
    rw [lead_coeff_eq, finsupp.coe_f, lead_tm_eq],
    apply add_right_neg,
end

lemma sub_support: Π (a b: mv_polynomial (fin n) α), (a - b).support ⊆ a.support ∪ b.support :=
λ a b,
begin
    unfold has_sub.sub algebra.sub, 
    have m := @finsupp.support_add _ _ _ _ _ a (-b),
    rw finsupp.support_neg at m, assumption,
end

lemma sub_dec : Π (a b : mv_polynomial (fin n) α),
    a.leading_term = b.leading_term 
    → a.leading_monomial ≠ 0
→ (a - b).leading_monomial < a.leading_monomial :=
begin
    intros a b leeq lmneqz,
    unfold leading_term at leeq,
    have coeff_eq := finsupp.single_inj2 leeq,
    have coeff_neqz := leading_term_ne_zero_coeff lmneqz,
    have lm_eq := finsupp.single_inj1 coeff_neqz leeq,
    have a_in_a_sup := finset.mem_of_sup_id (finset.ne_empty_of_sup_ne_bot lmneqz),
    have b_in_b_sup := finset.mem_of_sup_id (support_ne_empty_of_leading_term lmneqz lm_eq),
    unfold leading_monomial at lm_eq,
    rw ←lm_eq at b_in_b_sup,
    have sup_a_u_b : finset.sup (a.support ∪ b.support) id = finset.sup (a.support) id,
        by simp [finset.sup_union, lm_eq, lattice.sup_idem],
    have a_sup_notin_a_sub_b_supp : a.support.sup id ∉ (a - b).support,
        from lead_tm_eq_notin_supp leeq lmneqz,
    unfold leading_monomial,
    rw ←sup_a_u_b,
    have ab_le := finset.sub_sup (sub_support a b),
    rw le_iff_lt_or_eq at ab_le,
    cases ab_le, assumption,
    apply false.elim,
    rw sup_a_u_b at ab_le,
    rw ←ab_le at a_sup_notin_a_sub_b_supp,
    apply a_sup_notin_a_sub_b_supp,
    by_cases (a - b).support = ∅,
    begin
        rw h at *, simp at ab_le,
        unfold leading_coeff leading_monomial at coeff_neqz,
        rw [←ab_le] at coeff_neqz,
        apply lmneqz, exact ab_le.symm,
    end,
    begin
        exact finset.mem_of_sup_id h,
    end,
end

lemma lead_tm_eq {a b : mv_polynomial (fin n) α} (hb : b ≠ 0) (hab : leading_term_le b a) : 
    a.leading_term = leading_term (b * finsupp.single (leading_term_sub' a b hab) 
                (a.leading_coeff / b.leading_coeff)) := sorry

def div_const : Π (a b : mv_polynomial (fin n) α), b ≠ 0 →
                mv_is_const b →
                Σ' (q r : mv_polynomial (fin n) α), b.leading_monomial = r.leading_monomial
                        ∧ a = b * q + r
| a b bneqz bconst :=
begin
    have m := mv_is_const_neqz bconst bneqz,
    apply psigma.mk (a * C (1 / m.fst)),
    apply psigma.mk (0: mv_polynomial (fin n) α),
    apply and.intro,
    rw m.snd.snd,
    unfold leading_monomial C monomial finsupp.single, 
    simp [m.snd.fst], rw [←finset.singleton_eq_singleton, finset.sup_singleton], 
    unfold has_zero.zero, simp, rw [←_inst_2.zero_bot], trivial,
    simp, have n : b = C m.fst,
    exact m.snd.snd, generalize j : C (m.fst)⁻¹ = k,
    rw n, rw ←j, rw mul_comm, rw mul_assoc,
    rw ←C_mul, rw discrete_field.inv_mul_cancel,
    simp, exact m.snd.fst,
end

def reduction (a b : mv_polynomial (fin n) α) (h : leading_term_le b a) := 
a - b * (monomial (leading_term_sub' a b h) (a.leading_coeff / b.leading_coeff))

def reduction_list_aux : (mv_polynomial (fin n) α) → 
    (list (Σ' (p: mv_polynomial (fin n) α), p ≠ 0)) → mv_polynomial (fin n) α
| a [] := a
| a (hd :: tl) := if h: leading_term_le hd.1 a
                  then reduction_list_aux (reduction a hd.1 h) tl
                  else reduction_list_aux a tl


lemma reduction_leading_monomial_le: Π (a b: mv_polynomial (fin n) α),
    (b ≠ 0) → Π (p: leading_term_le b a),
    leading_monomial (reduction a b p) < leading_monomial a :=
begin
    sorry
end


lemma reduction_list_lem : ∀ (a b: mv_polynomial (fin n) α) m l (p: b ≠ 0), 
    leading_monomial (reduction_list_aux (reduction a b m) l) < leading_monomial a :=
begin
    intros a b m l, revert a b m,
    induction l; intros,
    apply reduction_leading_monomial_le; assumption,
    unfold reduction_list_aux,
    by_cases leh : leading_term_le (l_hd.fst) (reduction a b m); simp [leh],
    begin
        apply lt_trans,
        apply l_ih (reduction a b m) l_hd.fst leh l_hd.snd,
        apply reduction_leading_monomial_le _ _ p,
    end,
    begin
        apply l_ih, assumption,
    end
end
lemma reduction_list_aux_neq_lt : 
    Π (a : mv_polynomial (fin n) α) (l: list (Σ' (p: mv_polynomial (fin n) α), p ≠ 0)),
    reduction_list_aux a l ≠ a → (reduction_list_aux a l).leading_monomial < a.leading_monomial :=
begin
    intros a l, revert a,
    induction l; intros, 
    apply false.elim (a_1 rfl),
    unfold reduction_list_aux,
    by_cases m: (leading_term_le (l_hd.fst) a); simp [m],
    swap,
    begin 
        apply l_ih a, 
        intro eq,
        apply a_1, unfold reduction_list_aux; simp [m],
        assumption,
    end,
    begin
        apply reduction_list_lem, 
        exact l_hd.snd,
    end
end

include lt_wellfounded
def reduction_list : Π (a : mv_polynomial (fin n) α) (l : list (Σ' (p: mv_polynomial (fin n) α), p ≠ 0))
   , mv_polynomial (fin n) α
| a l :=
   let r := reduction_list_aux a l
   in if h: r = a
    then r
    else have (reduction_list_aux a l).leading_monomial < a.leading_monomial,
         from reduction_list_aux_neq_lt a l h, 
         reduction_list r l
using_well_founded 
{ rel_tac := λ _ _, `[exact ⟨_, inv_image.wf (λ a, a.1.leading_monomial) lt_wellfounded⟩] 
, dec_tac := tactic.assumption }

end div

section buchberger
variables [decidable_linear_order α]

include lt_wellfounded

def s_poly (p q : mv_polynomial (fin n) α) : 
    p ≠ 0 → q ≠ 0 → mv_polynomial (fin n) α :=
λ p_nz q_nz,
begin
    let fst := div lt_wellfounded (leading_term_lcm p q) p.leading_term (poly_lead_tm_neqz p_nz),
    let snd := div lt_wellfounded (leading_term_lcm p q) q.leading_term (poly_lead_tm_neqz q_nz),
    exact fst.fst * p - snd.fst * q,
end


def buch_pairs (s : list (Σ' (p: mv_polynomial (fin n) α), p ≠ 0)) 
: list (Σ' (p: mv_polynomial (fin n) α × mv_polynomial (fin n) α), 
                pprod (p.1 ≠ 0) (p.2 ≠ 0)) :=
    do  x ← s,
        y ← s,
        if x = y
        then []
        else [⟨(x.fst, y.fst), ⟨x.snd, y.snd⟩⟩]

def buch_s_polys (pairs : list (Σ' (p: mv_polynomial (fin n) α × mv_polynomial (fin n) α), 
                pprod (p.1 ≠ 0) (p.2 ≠ 0))) : list (mv_polynomial (fin n) α) 
    := pairs.map (λ a, s_poly lt_wellfounded a.fst.fst a.fst.snd a.snd.fst a.snd.snd)

def buch_div_result (s s_polys: list (Σ' (p: mv_polynomial (fin n) α), p ≠ 0))
    := (list.foldl (λ a b, 
    let div_result := reduction_list lt_wellfounded (b: (Σ' (p: mv_polynomial (fin n) α), p ≠ 0)).fst a
    in if div_result ∉ list.map psigma.fst a 
        then (if h: div_result = 0 then a else ⟨div_result, h⟩ :: a ) else a) s s_polys)
omit lt_wellfounded
def filter_non_zero : list (mv_polynomial (fin n) α) →
    list (Σ' (p: mv_polynomial (fin n) α), p ≠ 0)
| [] := []
| (x :: xs) := if h: x = 0 then filter_non_zero xs else ⟨x, h⟩ :: filter_non_zero xs
def non_zero_poly_to_ideal : list (Σ' (p: mv_polynomial (fin n) α), p ≠ 0) → ideal (mv_polynomial (fin n) α) :=
    λ s, ideal.span $ finset.to_set $ list.to_finset $ s.map (λ (a : (Σ' (p: mv_polynomial (fin n) α), p ≠ 0)), a.1.leading_term)

include lt_wellfounded

def buchberger : list (Σ' (p: mv_polynomial (fin n) α), p ≠ 0) → 
    list (Σ' (p: mv_polynomial (fin n) α), p ≠ 0)
| s :=
    let result := buch_div_result lt_wellfounded s 
        $ filter_non_zero
        $ buch_s_polys lt_wellfounded
        $ buch_pairs lt_wellfounded s
        in if s = result then s else 
            have non_zero_poly_to_ideal s < non_zero_poly_to_ideal result := sorry,
            buchberger result
using_well_founded 
{ rel_tac := λ _ _, 
`[exact ⟨_, inv_image.wf non_zero_poly_to_ideal seqR.ideal_wf⟩] 
, dec_tac := tactic.assumption }

end buchberger
end fin_n

end mv_polynomial