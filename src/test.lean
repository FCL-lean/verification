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

def leading_term (p : mv_polynomial ℕ α) : mv_polynomial ℕ α := 
   dite (p.support.sort finsupp.le = list.nil) 
        (λ prf, mv_polynomial.C (p.to_fun 0))
        (λ nprf, let g := list.last (p.support.sort finsupp.le) nprf 
                 in finsupp.single g (p.to_fun g))

def leading_term' (p : mv_polynomial ℕ α) : ℕ →₀ ℕ := 
   dite (p.support.sort finsupp.le = list.nil) 
        (λ prf, 0)
        (λ nprf, list.last (p.support.sort finsupp.le) nprf)

def leading_coeff (p : mv_polynomial ℕ α) : α := 
   dite (p.support.sort finsupp.le = list.nil) 
        (λ prf, p.to_fun 0)
        (λ nprf, let g := list.last (p.support.sort finsupp.le) nprf 
                 in p.to_fun g)

def leading_term_le_aux : (ℕ →₀ ℕ) → (ℕ →₀ ℕ) → ℕ → Prop
| a b 0 := a 0 ≤ b 0
| a b (nat.succ m) := a (nat.succ m) ≤ b (nat.succ m) ∧ leading_term_le_aux a b m 

def leading_term_le (a b : ℕ →₀ ℕ) : Prop := leading_term_le_aux a b (finsupp.finsupp_max_ab a b)

def leading_term_le' (a b : mv_polynomial ℕ α) : Prop := leading_term_le a.leading_term' b.leading_term'

/-
lemma le_imp_finsupp_le : ∀ a b : mv_polynomial ℕ α, a ≤ b → a.leading_term' ≤ b.leading_term' :=
λ a b, 
    begin 
        unfold has_le.le preorder.le finsupp.le mv_polynomial.le leading_term_le,
        induction (finsupp.finsupp_max_ab (leading_term' a) (leading_term' b));
        unfold leading_term_le_aux finsupp.le_aux, simp,
        intro h,
        cases h.left, 
        rw le_iff_lt_or_eq at h,
        left, assumption,
        right, apply and.intro h_1 (ih h.right),
    end
-/

lemma le_refl : ∀ a : mv_polynomial ℕ α, leading_term_le' a a :=
λ a, 
begin 
    unfold leading_term_le' leading_term_le, 
    induction (finsupp.finsupp_max_ab (leading_term' a) (leading_term' a));
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
    → i ≥ (finsupp.finsupp_max_ab (leading_term' a) (leading_term' b)) 
    → leading_term_le_aux a.leading_term' b.leading_term' i :=
λ a b i h hi, begin 
    unfold leading_term_le' leading_term_le at h,
    induction i, rw nat.le_zero_iff.1 hi at h, assumption,
    from if hi₁ : nat.succ i_n = (finsupp.finsupp_max_ab (leading_term' a) (leading_term' b))
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
    leading_term_le_aux a.leading_term' b.leading_term' ((finsupp.finsupp_max_ab (leading_term' a) (leading_term' b)) + i)
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
    generalize hs : [(finsupp.finsupp_max_ab a.leading_term' b.leading_term'), (finsupp.finsupp_max_ab b.leading_term' c.leading_term'), (finsupp.finsupp_max_ab a.leading_term' c.leading_term')] = s,
    generalize hk: s.to_finset.sup id = k, rw [←hs] at hk,
    have hkab : (finsupp.finsupp_max_ab a.leading_term' b.leading_term') ≤ k, rw ←hk, simp,
    have hkbc : (finsupp.finsupp_max_ab b.leading_term' c.leading_term') ≤ k, rw ←hk, simp, rw ←lattice.sup_assoc, apply lattice.le_sup_right,
    have hkac : (finsupp.finsupp_max_ab a.leading_term' c.leading_term') ≤ k, rw ←hk, simp, rw [lattice.sup_comm, lattice.sup_assoc], apply lattice.le_sup_left,
    have hab' := leading_term_le_aux_of_ge_max a b k hab hkab,
    have hbc' := leading_term_le_aux_of_ge_max b c k hbc hkbc,
    have hac' := leading_term_le_aux_trans a.leading_term' b.leading_term' c.leading_term' k hab' hbc',
    apply leading_term_le_of_ge_max_aux a c ((k - (finsupp.finsupp_max_ab a.leading_term' c.leading_term'))),
    rw nat.add_sub_of_le hkac,
    assumption,
end

instance le_decidable (a b : mv_polynomial ℕ α) : decidable (leading_term_le' a b) := 
begin
    unfold leading_term_le' leading_term_le,
    induction (finsupp.finsupp_max_ab (leading_term' a) (leading_term' b));
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
| le := leading_term_sub_aux a b (finsupp.finsupp_max_ab b a) le

constant lt_wellfounded : well_founded (@preorder.lt (ℕ →₀ ℕ) _)


lemma finset_sort_singleton : Π (b : ℕ →₀ ℕ),
    finset.sort finsupp.le (finset.singleton b) = [b] :=
begin
    intros,
    unfold finset.sort multiset.sort, unfold quot.lift_on,
    apply quot.lift_beta id, intros, assumption,
end

lemma finset_last_sort_singleton : Π (b : ℕ →₀ ℕ) h,
    list.last (finset.sort finsupp.le (finset.singleton b)) h = b :=
begin
    intro b,
    rw finset_sort_singleton,
    intros, simp,
end

lemma insert_le : ∀ a s h h', a < list.last (finset.sort finsupp.le s) h
    → list.last (finset.sort finsupp.le (insert a s)) h' =
        list.last (finset.sort finsupp.le s) h :=
begin
    intro a, intros,
    apply finset.induction_on s,

end


lemma finset_erase_last_lt : Π (a : finset (ℕ →₀ ℕ)), Π (b c : ℕ →₀ ℕ),
    c > b → (∀ k ∈ a, b > k) →
    list.last (finset.sort finsupp.le (insert b a)) sorry <
            list.last (finset.sort finsupp.le (insert b (insert c a))) sorry :=
begin
    intro a, intros,
    revert a_2,
    apply finset.induction_on a,
    intros, 
    sorry, intros,
    have ih := a_4 _,
    have b_gt : b > a_2,
    apply a_2_1, simp,
    swap, intros,
    apply a_2_1, simp, right, assumption,
    rw finset.insert.comm b a_2,
    rw finset.insert.comm c a_2,
    rw finset.insert.comm b a_2,
end

lemma finset_sorted_support:  Π (a : mv_polynomial ℕ α) b, 
    b ∈ finset.sort finsupp.le (a.support) →
    b ∈ a.support :=
begin
    intro a,
    apply @finset.induction_on _ 
        (λ sup, ∀ (b : ℕ →₀ ℕ), b ∈ finset.sort finsupp.le sup
                    → b ∈ sup) _ a.support,
    intros, simp at a_1, apply false.elim, assumption,
    intros, simp, simp at a_4, cases a_4,
    left, assumption,
    right, assumption,
end

lemma last_mem (α : Sort*): Π (l : list α) (h : l ≠ list.nil),  
        l.last h ∈ l :=
begin
    intro l,
    induction l;
    intros, apply false.elim, apply h, trivial,
    simp, cases l_tl,
    left, simp,
    right, simp,
    apply l_ih,
end

lemma sub_eq_eq_zero : Π (a b : mv_polynomial ℕ α) (n : ℕ →₀ ℕ),
    a.to_fun n = b.to_fun n → 
    (a - b).to_fun n = 0 :=
begin
    intros a b n,
    intros, simp,
    rw ←finsupp.coe_f at *,
    rw ←finsupp.coe_f at *,
    rw finsupp.add_apply,
    rw a_1, simp,
end
lemma sub_dec : Π (a b : mv_polynomial ℕ α),
    a.leading_term = b.leading_term 
    → a.leading_term' ≠ 0
    → (a - b).leading_term' < a.leading_term' :=
begin
    intros a b eql neq0,
    unfold leading_term' at *,
    by_cases finset.sort finsupp.le (a.support) = list.nil,
    rw logic.dite_true' h at neq0,
    apply false.elim, apply neq0, trivial,
    rw logic.dite_false' h,
    by_cases finset.sort finsupp.le ((a - b).support) = list.nil,
    tactic.unfreeze_local_instances,
    dedup,
    rw logic.dite_true' h_1,
    rw logic.dite_false' h at neq0,
    generalize n : list.last (finset.sort finsupp.le (a.support)) h = x,
    rw n at *,
    apply finsupp.neq_zero_gt_zero, assumption, tactic.unfreeze_local_instances,
    dedup,
    rw logic.dite_false' h_1,
    unfold leading_term at *,
    rw logic.dite_false' h at neq0 eql,
    by_cases finset.sort finsupp.le (b.support) = list.nil,
    rw logic.dite_true' h at eql, simp at eql,
    unfold C monomial at eql,
    apply false.elim, apply neq0,
    apply finsupp.single_inj1 
        (list.last (finset.sort finsupp.le (a.support)) (by assumption)) (0 : ℕ →₀ ℕ)
            (a.to_fun (list.last (finset.sort finsupp.le (a.support)) (by assumption)))
            (b.to_fun 0),
    dedup,
    have q : list.last (finset.sort finsupp.le (a.support)) h ∈ a.support ↔
        a.to_fun (list.last (finset.sort finsupp.le (a.support)) h) ≠ 0:= @finsupp.mem_support_iff _ _ _
                    a (list.last (finset.sort finsupp.le (a.support)) h),
    rw [←q],
    apply finset_sorted_support,
    apply last_mem, assumption,
    simp at eql, rw logic.dite_false' h at eql,

    


    /-
    def largest_elem a = list.last (finset.sort finsupp.le a) ??
    largest_elem (a - b) < largest_elem a = largest_elem b
    1. list.last (finset.sort finsupp.le (a.support)) h ∉ finset.sort finsupp.le ((a - b).support)
    1. list.last (finset.sort finsupp.le (b.support)) h ∉ finset.sort finsupp.le ((a - b).support)
    2. finset.sort finsupp.le ((a - b).support)
         ⊂ finset.sort finsupp.le a.support ++ finset.sort finsupp.le b.support
    3.
    list.last (finset.sort finsupp.le ((a - b).support)) h_1 ≤ 
    list.last (finset.sort finsupp.le ((a + b).support.erase last_elem)) h_1
    < last_elem
    -/

end

def div : Π (a b : mv_polynomial ℕ α),
                 Σ'q r, (¬ leading_term_le' b r) ∧ a = b * q + r
| a b :=
begin
    by_cases (leading_term_le' b a),
    let sub := leading_term_sub a.leading_term' b.leading_term' h,
    let q' := (finsupp.single sub (a.leading_coeff / b.leading_coeff)),
    generalize h : a - b * q' = r',
    let tt' : r'.leading_term' < a.leading_term', sorry,
    have result := div r' b,
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
    apply psigma.mk (0 : mv_polynomial ℕ α),
    apply psigma.mk a,
    apply and.intro, assumption,
    simp,
end
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, inv_image.wf psigma.fst (inv_image.wf leading_term' lt_wellfounded)⟩] 
                   , dec_tac := tactic.assumption }
def mv_trichotomy (p : mv_polynomial ℕ α) : psum (p = mv_polynomial.C 0) 
            (psum (Σ'a : α, p = mv_polynomial.C a) ((Σ'a : α, p = mv_polynomial.C a) → false)):= 
if h₀ : p.support = ∅ 
    then
    begin
        left, 
        unfold C monomial finsupp.single,
        simp,
        apply finsupp.ext, intro,
        rw iff.elim_left finsupp.support_eq_empty h₀,
        refl,
    end
else if h₁ : p.support = {0} 
        then 
        begin
            right, left,
            unfold C monomial,
            apply (psigma.mk (p.to_fun 0)),
            apply finsupp.ext, intro,
            change p.to_fun a = (finsupp.single 0 (p.to_fun 0)).to_fun a,
            unfold finsupp.single, simp,
            by_cases 0 = a,
            simp [h],
            rw if_neg h,
            have ha : a ∉ p.support,
            rw [h₁, finset.insert_empty_eq_singleton, finset.mem_singleton], 
            apply ne.symm, assumption,
            apply finsupp.not_mem_support_iff.elim_left ha,
        end
    else
    begin
        right, right,
        intro h,
        unfold C monomial finsupp.single at h,
        cases h,
        by_cases h_fst = 0,
        rw h at *, simp [h_snd] at *, assumption, 
        simp [h_snd] at *,
        rw (if_neg h) at h₁,
        apply (ne_self_iff_false (finset.singleton 0)).mp h₁,
    end


def leading_term_lcm (p q : mv_polynomial ℕ α) : mv_polynomial ℕ α := 
begin
    have hp := mv_trichotomy p,
    have hq := mv_trichotomy q,
    cases hp, exact mv_polynomial.C 0,
    cases hq, exact mv_polynomial.C 0,
    cases hp, all_goals {cases hq},
    begin
        cases hp, cases hq,
        exact mv_polynomial.C (max hp_fst hq_fst),
    end,
    begin
        cases hp,
        let coeff := max hp_fst (q.to_fun (q.leading_term')),
        exact monomial q.leading_term' coeff,
    end,
    begin
        cases hq,
        let coeff := max hq_fst (p.to_fun (p.leading_term')),
        exact monomial p.leading_term' coeff,
    end,
    begin
        let coeff := max (p.to_fun (p.leading_term')) (q.to_fun (q.leading_term')),
        let supp := finsupp.zip_with max (max_self 0) p.leading_term' q.leading_term',
        exact monomial supp coeff,
    end
end

def s_poly (p q : mv_polynomial ℕ α) : mv_polynomial ℕ α :=
begin
    let fst := div (leading_term_lcm p q) p.leading_term,
    let snd := div (leading_term_lcm p q) q.leading_term,
    exact fst.fst * p - snd.fst * q,
end

def div_list : (mv_polynomial ℕ α) → (list (mv_polynomial ℕ α)) → mv_polynomial ℕ α
| a list.nil := a
| a (list.cons x xs) := div_list (div a x).snd.fst xs

def buch_pairs (s : list (mv_polynomial ℕ α)) : list (mv_polynomial ℕ α × mv_polynomial ℕ α) :=
    do  x ← s,
        y ← s,
        if x = y
        then list.nil
        else [(x, y)]

def buch_s_polys (pairs : list (mv_polynomial ℕ α × mv_polynomial ℕ α)) : list (mv_polynomial ℕ α) := pairs.map (λ a, s_poly a.fst a.snd)

def buch_div_result (s s_polys: list (mv_polynomial ℕ α)) := (list.foldl (λ a b, 
                let div_result := div_list (b : mv_polynomial ℕ α) a 
                in if div_result ∉ a then div_result :: a else a) s s_polys)

def buchberger : list (mv_polynomial ℕ α) → list (mv_polynomial ℕ α)
| s :=
    let result := buch_div_result s $ buch_s_polys $ buch_pairs s
        in if s = result then s else buchberger result

def buchberger_correct₂ (l l': list (mv_polynomial ℕ α)) (h: list.perm l l') 
    (d : mv_polynomial ℕ α): div_list d l = div_list d l' := sorry

lemma div_mem_span {a b : mv_polynomial ℕ α} {s : set (mv_polynomial ℕ α)}: a ∈ ideal.span s → b ∈ ideal.span s → (div a b).snd.fst ∈ ideal.span s := 
λ ha hb, begin
    have h := (div a b).snd.snd.right, revert h,
    generalize hr : (div a b).snd.fst = r,
    generalize hq : (div a b).fst = q,
    intro h,
    have h' : a - b * q = r, rw add_comm at h, exact sub_eq_of_eq_add h,
    simp at h', rw ←h',
    apply ideal.add_mem (ideal.span s) ha,
    rw [mul_comm, neg_mul_eq_neg_mul q b],
    apply ideal.mul_mem_left (ideal.span s) hb,
end

set_option trace.simplify.rewrite true
lemma div_list_mem_span {s : set (mv_polynomial ℕ α)}: 
    ∀ (a : mv_polynomial ℕ α) (l : list (mv_polynomial ℕ α)), a ∈ ideal.span s → (l.to_finset.to_set ⊆ ↑(ideal.span s)) → div_list a l ∈ ideal.span s
| a [] := λ ha hb, by unfold div_list; assumption
| a (hd :: tl) := λ ha hb, begin
    rw ideal.list_subset at hb,
    unfold div_list,
    have hhd : hd ∈ ideal.span s, 
        apply hb hd, simp,
    have hdiv : (div a hd).snd.fst ∈ ideal.span s, 
        exact div_mem_span ha hhd,
    have hb' : tl.to_finset.to_set ⊆ ↑(ideal.span s), 
        intros b hbtl, rw ←list.mem_to_set at hbtl, exact hb b (list.mem_cons_of_mem hd hbtl),
    apply div_list_mem_span (div a hd).snd.fst tl hdiv hb',
end

lemma s_poly_mem_span {a b : mv_polynomial ℕ α} {s : set (mv_polynomial ℕ α)} : a ∈ s → b ∈ s → s_poly a b ∈ (ideal.span s) := 
λ ha hb, begin
    unfold s_poly, simp,
    generalize hx : (div (leading_term_lcm a b) (leading_term a)).fst = x,
    generalize hy : (div (leading_term_lcm a b) (leading_term b)).fst = y,
    rw neg_mul_eq_neg_mul y b,
    exact ideal.linear_combine_mem x (-y) ha hb,
end

set_option trace.simplify.rewrite true
lemma buch_s_poly_subset_span (s : list (mv_polynomial ℕ α)) : (buch_s_polys (buch_pairs s)).to_finset.to_set ⊆ ↑(ideal.span s.to_finset.to_set) :=
begin
    rw ideal.list_subset,
    intros x hx,
    unfold buch_s_polys buch_pairs at hx,
    simp at hx,
    cases hx with a, cases hx_h with b,
    cases hx_h_h.left with a', cases h.right with b',
    from if hab : a' = b'
    then begin 
        simp [hab] at h_1,
        revert h_1, 
        simp only [false_implies_iff],
    end
    else begin
        simp [hab] at h_1,
        rw [list.mem_to_set] at h h_1,
        rw [←hx_h_h.right, h_1.right.right, h_1.right.left],
        apply s_poly_mem_span h.left h_1.left,
    end
end

lemma buch_div_subset_span : ∀ {s s' s_polys : list (mv_polynomial ℕ α)},
    (s'.to_finset.to_set ⊆ ↑(ideal.span s.to_finset.to_set))
    → (s_polys.to_finset.to_set ⊆ ↑(ideal.span s.to_finset.to_set))
    → (buch_div_result s' s_polys).to_finset.to_set ⊆ ↑(ideal.span (s.to_finset.to_set))
|s s' [] := λ hs' hsp, by unfold buch_div_result; simp; assumption
|s s' (hd :: tl) := λ hs' hsp, begin
    unfold buch_div_result, simp,
    have hsp' : (tl.to_finset.to_set ⊆ ↑(ideal.span s.to_finset.to_set)),
        intros a ha, rw ←list.mem_to_set at ha, apply (ideal.list_subset.1 hsp) a (list.mem_cons_of_mem hd ha),
    from if h : div_list hd s' ∈ s'
    then begin
        simp [h], 
        apply buch_div_subset_span hs' hsp',
    end
    else begin
        simp [h], 
        have hs'_ : (list.cons (div_list hd s') s').to_finset.to_set ⊆ ↑(ideal.span (s.to_finset.to_set)),
            intros a ha, rw [←list.mem_to_set, list.mem_cons_iff] at ha,
            cases ha, rw ha,
            have hhd : hd ∈ ideal.span (finset.to_set (list.to_finset s)), apply (ideal.list_subset.1 hsp) hd, simp,
            apply div_list_mem_span hd s' hhd hs', exact (ideal.list_subset.1 hs') a ha,
        apply buch_div_subset_span hs'_ hsp',
    end
end

--set_option trace.class_instances true
set_option trace.simp_lemmas true
lemma buch_subset_span : ∀ {s : list (mv_polynomial ℕ α)}, (buchberger s).to_finset.to_set ⊆ ↑(ideal.span (s.to_finset.to_set))
| s := begin
    unfold buchberger, simp,
    have h :  (buch_div_result s (buch_s_polys (buch_pairs s))).to_finset.to_set ⊆ ↑(ideal.span (s.to_finset.to_set)),
    apply buch_div_subset_span, apply ideal.subset_span, apply buch_s_poly_subset_span s,
    generalize hs : buch_div_result s (buch_s_polys (buch_pairs s)) = s', rw hs at h,
    from if hss' : s = s' 
    then begin
        simp [hss'], exact ideal.subset_span,
    end
    else begin
        simp [hss'], apply ideal.span_le.1 (le_trans (ideal.span_le.2 (@buch_subset_span s')) (ideal.span_le.2 h)),
    end
    
end

lemma buch_div_contain : ∀ {s s' s_poly : list (mv_polynomial ℕ α)}, 
    s.to_finset.to_set ⊆ s'.to_finset.to_set
    → s.to_finset.to_set ⊆ (buch_div_result s' s_poly).to_finset.to_set
| s s' [] := begin unfold buch_div_result, simp, end
| s s' (hd :: tl) := λ hs, begin
    unfold buch_div_result, simp,
    from if h : div_list hd s' ∈ s'
    then begin
        simp [h], exact buch_div_contain hs,
    end
    else begin
        simp [h], 
        have hs' : s' ⊆ (div_list hd s' :: s'), simp, rw list.subset_to_set at hs',
        exact buch_div_contain (set.subset.trans hs hs'),
    end
end

lemma buch_contain : ∀ {s : list (mv_polynomial ℕ α)}, s.to_finset.to_set ⊆ (buchberger s).to_finset.to_set
| s := begin
    unfold buchberger, simp,
    generalize hs : buch_div_result s (buch_s_polys (buch_pairs s)) = s',
    have hs' : s ⊆ s', rw [list.subset_to_set, ←hs], apply buch_div_contain, refl,
    from if h : s = s'
    then by simp [h]
    else begin
        simp [h],
        apply set.subset.trans (list.subset_to_set.1 hs') (@buch_contain s'),
    end
end

theorem buchberger_correct : ∀ s : list (mv_polynomial ℕ α), ideal.span s.to_finset.to_set = ideal.span (buchberger s).to_finset.to_set := 
λ s, begin
    have h₁ : ideal.span s.to_finset.to_set ≤ ideal.span (buchberger s).to_finset.to_set,
        exact ideal.span_mono buch_contain,
    have h₂ : ideal.span (buchberger s).to_finset.to_set ≤ ideal.span s.to_finset.to_set,
        exact ideal.span_le.2 buch_subset_span,
    apply le_antisymm h₁ h₂,
end

end mv_polynomial