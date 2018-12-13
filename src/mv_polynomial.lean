import linear_algebra.multivariate_polynomial
import finsupp
import finset
import fin
import bot_zero
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

lemma empty_of_leading_monomial_not_mem {p : mv_polynomial σ α} : p.to_fun p.leading_monomial = 0 ↔ p = 0 :=
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
                simp [leading_coeff, empty_of_leading_monomial_not_mem] at hpcz, simp [leading_monomial, hpcz, _inst_5.zero_bot], 
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

section finite_s
variable [fins: finite σ]
include fins

def leading_term_le (a b: mv_polynomial σ α): Prop
    := finsupp.leading_term_le a.leading_monomial b.leading_monomial

instance leading_term_le_dec (a b: mv_polynomial σ α): decidable (leading_term_le a b) :=
begin
    unfold leading_term_le finsupp.leading_term_le,
    apply finite.finite_fold_dec,
    intro, apply_instance,
end

lemma zero_of_le_zero {a b : mv_polynomial σ α} : a.leading_monomial = 0
     → leading_term_le b a → b.leading_monomial = 0 := sorry

omit fins
end finite_s


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
variables [lt_wellfounded: @well_founded (fin n →₀ ℕ) (<)]
variable [bot_zero (fin n) ℕ]

section div

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

section buchberger
variables [decidable_linear_order α]

include lt_wellfounded

def s_poly (p q : mv_polynomial (fin n) α) : 
    ¬ mv_is_const p → ¬ mv_is_const q → mv_polynomial (fin n) α :=
λ p_nconst q_nconst,
begin
    let fst := @div _ _ _ lt_wellfounded _ (leading_term_lcm p q) p.leading_term (leading_term_nconst_of_nconst p_nconst),
    let snd := @div _ _ _ lt_wellfounded _ (leading_term_lcm p q) q.leading_term (leading_term_nconst_of_nconst q_nconst),
    exact fst.fst * p - snd.fst * q,
end

def div_list : (mv_polynomial (fin n) α) → 
    (list (Σ' (p: mv_polynomial (fin n) α), ¬ mv_is_const p)) → mv_polynomial (fin n) α
| a [] := a
| a (hd :: tl) := div_list (@div _ _ _ lt_wellfounded _ a hd.fst hd.snd).snd.fst tl

def buch_pairs (s : list (Σ' (p: mv_polynomial (fin n) α), ¬ mv_is_const p)) 
: list (Σ' (p: mv_polynomial (fin n) α × mv_polynomial (fin n) α), 
                pprod (¬ mv_is_const p.1) (¬ mv_is_const p.2)) :=
    do  x ← s,
        y ← s,
        if x = y
        then []
        else [⟨(x.fst, y.fst), ⟨x.snd, y.snd⟩⟩]

def buch_s_polys (pairs : list (Σ' (p: mv_polynomial (fin n) α × mv_polynomial (fin n) α), 
                pprod (¬ mv_is_const p.1) (¬ mv_is_const p.2))) : list (mv_polynomial (fin n) α) 
    := pairs.map (λ a, @s_poly _ _ _ lt_wellfounded _ _ a.fst.fst a.fst.snd a.snd.fst a.snd.snd)

def buch_div_result (s s_polys: list (Σ' (p: mv_polynomial (fin n) α), ¬ mv_is_const p))
    := (list.foldl (λ a b, 
    let div_result := @div_list _ _ _ lt_wellfounded _ _ (b: (Σ' (p: mv_polynomial (fin n) α), ¬ mv_is_const p)).fst a
    in if div_result ∉ list.map psigma.fst a 
        then (if h: ¬ mv_is_const div_result then ⟨div_result, h⟩ :: a else a) else a) s s_polys)

def filter_non_const : list (mv_polynomial (fin n) α) →
    list (Σ' (p: mv_polynomial (fin n) α), ¬ mv_is_const p)
| [] := []
| (x :: xs) := if h: mv_is_const x then filter_non_const xs else ⟨x, h⟩ :: filter_non_const xs

def buchberger : list (Σ' (p: mv_polynomial (fin n) α), ¬ mv_is_const p) → 
    list (Σ' (p: mv_polynomial (fin n) α), ¬ mv_is_const p)
| s :=
    let result := @buch_div_result _ _ _ lt_wellfounded _ _ s 
        $ @filter_non_const _ _ _ lt_wellfounded _ _ 
        $ @buch_s_polys _ _ _ lt_wellfounded _ _
        $ @buch_pairs _ _ _ lt_wellfounded _ _ s
        in if s = result then s else 
                begin
                    exact buchberger result
                end

end buchberger
end fin_n

end mv_polynomial