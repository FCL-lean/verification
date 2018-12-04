import data.finset
import linear_algebra.multivariate_polynomial
import ring_theory.ideals
import tactic.find
import finsupp
import finset
import ideal
import leading_term


variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {ι : Type*}
variables [discrete_field α]
variables [decidable_eq α] [decidable_linear_order α]
-- variables [comm_ring (mv_polynomial ℕ α)]

namespace mv_polynomial

lemma finset_insert_neq_nil : Π (b : ℕ →₀ ℕ) (s : finset (ℕ →₀ ℕ)), finset.sort finsupp.le (insert b s) ≠ list.nil :=
λ b s, begin
    rw finset.insert_eq,
    intro h,
    have h' : b ∈ {b} ∪ s, simp,
    rw [←finset.mem_sort finsupp.le, h] at h',
    cases h',
end

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
lemma sort_empty_eq_nil : finset.sort finsupp.le ∅ = [] :=
begin
    apply quot.lift_beta id, intros, assumption,
end
#print sort_empty_eq_nil

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

lemma lead_tm_eq_notin_supp
    : Π {a b: mv_polynomial ℕ α},
    leading_term a = leading_term b
    → a.leading_term' ≠ 0
    → a.leading_term' ∉ (a - b).support :=
λ a b eql neq0 insub,
begin
    unfold leading_term at eql,
    have coeff_neq_z := leading_term_ne_zero_coeff neq0,
    have lead_tm_eq := finsupp.single_inj1 coeff_neq_z eql,
    have lead_coeff_eq := finsupp.single_inj2 eql,
    rw finsupp.mem_support_iff at insub,
    apply insub,
    change (a - b).to_fun (leading_term' a) = 0,
    unfold has_sub.sub algebra.sub,
    rw [←finsupp.coe_f, finsupp.add_apply],
    simp, unfold leading_coeff at lead_coeff_eq,
    rw [←finsupp.coe_f] at lead_coeff_eq,
    rw [lead_coeff_eq, finsupp.coe_f, lead_tm_eq],
    apply add_right_neg,
end
lemma sub_support: Π (a b: mv_polynomial ℕ α), (a - b).support ⊆ a.support ∪ b.support :=
λ a b,
begin
    unfold has_sub.sub algebra.sub, 
    have m := @finsupp.support_add _ _ _ _ _ a (-b),
    rw finsupp.support_neg at m, assumption,
end

lemma sub_sup: Π (a b : finset (ℕ →₀ ℕ)), a ⊆ b → a.sup id ≤ b.sup id :=
λ a b asubb,
begin
    --revert a,
    --apply finset.induction_on b; intros,
    --sorry, simp,
    unfold has_subset.subset at asubb,
end


lemma sub_dec : Π (a b : mv_polynomial ℕ α),
    a.leading_term = b.leading_term 
    → a.leading_term' ≠ 0
    → (a - b).leading_term' < a.leading_term' :=
begin
    intros a b eql neq0,
    unfold leading_term',
    unfold leading_term at eql,
    have coeff_neq_z := leading_term_ne_zero_coeff neq0,
    have lead_tm_eq := finsupp.single_inj1 coeff_neq_z eql,
    have lead_coeff_eq := finsupp.single_inj2 eql,
    have a_sup_in_a := finset.mem_of_sup_id (support_ne_empty_of_leading_term' neq0),
    have a_sup_in_b := finset.mem_of_sup_id (support_ne_empty_of_leading_term neq0 lead_tm_eq),
    unfold leading_term' at lead_tm_eq,
    rw ←lead_tm_eq at a_sup_in_b,
    have sup_a_u_b : finset.sup (a.support ∪ b.support) id = finset.sup (a.support) id,
    rw [finset.sup_union, ←lead_tm_eq, lattice.sup_idem],
    have a_sub_b_in_a_u_b := sub_support a b,
    have not_in_a_sub_b := lead_tm_eq_notin_supp eql neq0,
    have ab_le := sub_sup _ _ a_sub_b_in_a_u_b,
    rw le_iff_lt_or_eq at ab_le, cases ab_le,
    rw ←sup_a_u_b, assumption,
    unfold leading_term' at not_in_a_sub_b,
    rw ←sup_a_u_b at not_in_a_sub_b,
    rw ←ab_le at not_in_a_sub_b,
    by_cases (a - b).support = ∅,
    swap,
    apply absurd (finset.mem_of_sup_id h) not_in_a_sub_b,
    rw h at *, simp at *,
    apply finsupp.neq_zero_gt_zero,
    assumption,
    /-
        finset.sup (a.support) id ∈ a.support
        finset.sup (a.support) id ∈ b.support
        finset.sup (a.support ∪ b.support) id 
                = finset.sup (a.support) id
        finset.sup (a.support) id ∉ (a - b).support
        (a - b).support ⊆ (a.support ∪ b.support)
            → finset.sup (a - b).support id ≤ 
                finset.sup (a.support ∪ b.support) id
        
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


constant buch_lt : rel (list (mv_polynomial ℕ α))
constant buch_lt_wf : @well_founded (list (mv_polynomial ℕ α)) buch_lt
constant buch_lt_lt : Π (s : list (mv_polynomial ℕ α)), 
    (buch_div_result s $ buch_s_polys $ buch_pairs s) ≠ s
    → buch_lt (buch_div_result s $ buch_s_polys $ buch_pairs s) s

def buchberger : list (mv_polynomial ℕ α) → list (mv_polynomial ℕ α)
| s :=
    let result := buch_div_result s $ buch_s_polys $ buch_pairs s
        in if s = result then s else 
                begin
                    let h : buch_lt result s := buch_lt_lt s sorry,
                    exact buchberger result
                end
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, buch_lt_wf⟩] 
                   , dec_tac := tactic.assumption }



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