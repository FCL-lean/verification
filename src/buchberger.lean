import mv_polynomial

variables {σ : Type*} {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {ι : Type*}

namespace mv_polynomial
namespace fin_n
variables {n : ℕ}

variables [discrete_field α] (lt_wellfounded: @well_founded (fin n →₀ ℕ) (<)) [bot_zero (fin n) ℕ]

section reduction

def reduction (a b : mv_polynomial (fin n) α) (h : leading_term_le b a) := 
    if mv_is_const b
    then 0
    else a - b * (monomial (leading_term_sub' a b h) (a.leading_coeff / b.leading_coeff))

lemma reduction_const (a : mv_polynomial (fin n) α) (b : α) : ∀ m, reduction a (C b) m = 0 :=
begin
    intros, unfold reduction, 
    simp [const_mv_is_const],
end

lemma reduction_zero (a : mv_polynomial (fin n) α) : ∀ m,
    reduction 0 a m = 0 :=
begin
    intro m, unfold reduction,
    have : a.leading_monomial = 0 := finsupp.fin_n.leading_term_le_antisymm m (finsupp.fin_n.leading_term_le_zero _),
    have eqzconst := leading_monomial_eqz_const this,
    cases eqzconst, by_cases mv_is_const a; simp [h],
    apply false.elim, apply h, rw eqzconst_snd, simp,
end

def reduction_list_aux : (mv_polynomial (fin n) α) → 
    (list (Σ' (p: mv_polynomial (fin n) α), p ≠ 0)) → mv_polynomial (fin n) α
| a [] := a
| a (hd :: tl) := if h: leading_term_le hd.1 a
                  then reduction_list_aux (reduction a hd.1 h) tl
                  else reduction_list_aux a tl

lemma reduction_list_zero : 
    Π (s: list (Σ' (p: mv_polynomial (fin n) α), p ≠ 0)) (p: s ≠ []),
    reduction_list_aux (C 0) s = 0 :=
begin
    intros s,
    cases s,
    begin
        intros, trivial,
    end,
    begin
        induction s_tl; intros,
        begin
            unfold reduction_list_aux,
            by_cases leading_term_le (s_hd.fst) (C 0); simp [h],
            unfold reduction,
            by_cases h': mv_is_const (s_hd.fst); simp [h'],
            rw [←(congr_arg leading_coeff C_0), leading_coeff_C],
            rw C_0 at h, simp, unfold monomial,
            rw [finsupp.single_zero],
            apply ring.mul_zero, 
        end,
        begin
            unfold reduction_list_aux,
            have lem : reduction_list_aux (C 0) (s_hd :: s_tl_tl) = 0 := s_tl_ih (by simp),
            unfold reduction_list_aux at lem,
            rw C_0 at *,
            by_cases h: leading_term_le (s_hd.fst) 0,
            by_cases h': leading_term_le (s_tl_hd.fst) (reduction 0 (s_hd.fst) h), simp [h, h'] at *,
            revert h,
            change ∀ (h : leading_term_le (s_hd.fst) 0) (h' : leading_term_le (s_tl_hd.fst) (reduction 0 (s_hd.fst) h)),
                        reduction_list_aux (reduction 0 (s_hd.fst) h) s_tl_tl = 0 →
                            reduction_list_aux (reduction (reduction 0 (s_hd.fst) h) (s_tl_hd.fst) h') s_tl_tl = 0,
            intro h, rw reduction_zero, intros h' p, rw reduction_zero, assumption,
            simp [h, h'] at *, assumption,
            simp [h] at *, 
            by_cases h': leading_term_le (s_tl_hd.fst) 0, simp [h'],
            rw reduction_zero, assumption, simp [h'], assumption,
        end,
    end
end


lemma reduction_leading_monomial_le: Π (a b: mv_polynomial (fin n) α),
    (b ≠ 0) → (a.leading_monomial ≠ 0) → Π (p: leading_term_le b a),
    leading_monomial (reduction a b p) < leading_monomial a :=
begin
    intros, unfold reduction, 
    by_cases mv_is_const b; simp [h],
    begin
        apply lt_of_le_of_ne, exact finsupp.fin_n.zero_le a.leading_monomial,
        exact a_2.symm, 
    end,
    begin
        apply sub_dec, apply leading_term_eq,
        have := leading_monomial_ne_zero_coeff a_2,
        exact not_zero_iff_leading_coeff_not_zero.1 this, 
        all_goals {assumption},
    end
end


lemma reduction_list_aux_lem : ∀ (a b: mv_polynomial (fin n) α) m l (p: b ≠ 0) (p2: a.leading_monomial ≠ 0), 
    leading_monomial (reduction_list_aux (reduction a b m) l) < leading_monomial a :=
begin
    intros a b m l, revert a b m,
    induction l; intros,
    apply reduction_leading_monomial_le; assumption,
    unfold reduction_list_aux,
    by_cases leh : leading_term_le (l_hd.fst) (reduction a b m); simp [leh],
    begin
        by_cases eqz: leading_monomial (reduction a b m) = 0,
        begin
            have eq0 := leading_monomial_zero_of_le_zero eqz leh,
            have isconst := leading_monomial_eqz_const eq0,
            cases isconst,
            revert leh, rw [isconst_snd], intro leh, 
            rw [reduction_const, ←C_0], 
            cases l_tl,
            begin
                simp [leading_monomial, reduction_list_aux],
                apply lt_of_le_of_ne, exact finsupp.fin_n.zero_le a.leading_monomial,
                exact p2.symm,
            end,
            begin
                rw [reduction_list_zero],
                apply lt_of_le_of_ne, exact finsupp.fin_n.zero_le a.leading_monomial,
                exact p2.symm, simp,
            end,
        end,
        begin
            apply lt_trans,
            apply l_ih (reduction a b m) l_hd.fst leh l_hd.snd eqz,
            apply reduction_leading_monomial_le _ _ p p2,
        end
    end,
    begin
        apply l_ih; assumption,
    end
end

set_option trace.simplify.rewrite true
lemma reduction_list_aux_neq_lt : 
    Π (a : mv_polynomial (fin n) α) (l: list (Σ' (p: mv_polynomial (fin n) α), p ≠ 0)),
    a.leading_monomial ≠ 0 →
    reduction_list_aux a l ≠ a → (reduction_list_aux a l).leading_monomial < a.leading_monomial :=
begin
    intros a l, revert a,
    induction l; intros, 
    apply false.elim (a_2 rfl),
    unfold reduction_list_aux,
    by_cases m: (leading_term_le (l_hd.fst) a); simp [m],
    swap,
    begin 
        apply l_ih a a_1, 
        intro eq,
        apply a_2, unfold reduction_list_aux; simp [m],
        assumption,
    end,
    begin
        apply reduction_list_aux_lem, 
        exact l_hd.snd,
        assumption
    end
end

include lt_wellfounded

def reduction_list : Π (a : mv_polynomial (fin n) α) (l : list (Σ' (p: mv_polynomial (fin n) α), p ≠ 0))
   , mv_polynomial (fin n) α
| a l :=
   let r := reduction_list_aux a l
   in if h: r = a
    then r
    else if h': a.leading_monomial = 0 
         then 0
         else have (reduction_list_aux a l).leading_monomial < a.leading_monomial,
         from reduction_list_aux_neq_lt a l h' h, 
         reduction_list r l
using_well_founded 
{ rel_tac := λ _ _, `[exact ⟨_, inv_image.wf (λ a, a.1.leading_monomial) lt_wellfounded⟩] 
, dec_tac := tactic.assumption }

lemma reduction_list_lem_aux : Π (a : mv_polynomial (fin n) α) 
    (l : list (Σ' (p: mv_polynomial (fin n) α), p ≠ 0))
    (b : (Σ' (p: mv_polynomial (fin n) α), p ≠ 0)) 
    (b_ne_const: ¬ mv_is_const b.1), b ∈ l → 
    reduction_list_aux a l = a → ¬ leading_term_le b.1 a :=
λ a l, begin
    induction l, finish, intros,
    cases a_1; unfold reduction_list_aux at a_2;
    by_cases leading_term_le (l_hd.fst) a; simp [h] at a_2,
    {
        by_cases h': a.leading_monomial = 0,
        {
            have eqz := leading_monomial_zero_of_le_zero h' h,
            have neqz : l_hd.1.leading_monomial ≠ 0, rw [←a_1], apply leading_monomial_nez_of_ne_const b_ne_const, 
            apply absurd eqz neqz,
        },
        {
            have r_lt := reduction_list_aux_lem a l_hd.1 h l_tl l_hd.2 h',
            rw a_2 at r_lt, intro, 
            exact lt_irrefl _ r_lt,
        }
    },
    finish, 
    { 
        by_cases h': a.leading_monomial = 0,
        {
            intro,
            have eqz := leading_monomial_zero_of_le_zero h' a_3,
            have neqz : b.1.leading_monomial ≠ 0,
                 apply leading_monomial_nez_of_ne_const b_ne_const, 
            apply absurd eqz neqz,
        },
        {
            have r_lt := reduction_list_aux_lem a l_hd.1 h l_tl l_hd.2 h',
            rw a_2 at r_lt, intro, 
            exact lt_irrefl _ r_lt,
        }
    },
    apply l_ih b b_ne_const a_1 a_2,
end

lemma reduction_list_lem : 
    Π (a : mv_polynomial (fin n) α) 
    (l : list (Σ' (p: mv_polynomial (fin n) α), p ≠ 0)),
    ∀ (b : (Σ' (p: mv_polynomial (fin n) α), p ≠ 0))
    (in_l : b ∈ l), ¬ mv_is_const b.1 → 
        ¬ leading_term_le b.1 (reduction_list lt_wellfounded a l)
| a l b in_l b_ne_const :=
begin
    intros, unfold reduction_list,
    by_cases reduction_list_aux a l = a; simp [h],
    begin
        apply reduction_list_lem_aux lt_wellfounded a l b b_ne_const in_l h,
    end,
    begin
        by_cases h': leading_monomial a = 0; simp [h'],
        begin
            intro ltle,
            have : b.1.leading_monomial ≠ 0,
                apply leading_monomial_nez_of_ne_const b_ne_const, 
            have this' : b.1.leading_monomial = 0,
            from finsupp.fin_n.leading_term_le_antisymm ltle (finsupp.fin_n.leading_term_le_zero b.1.leading_monomial),
            exact this this',
        end,
        begin
            let : (reduction_list_aux a l).leading_monomial < a.leading_monomial,
            from reduction_list_aux_neq_lt a l h' h, 
            exact reduction_list_lem (reduction_list_aux a l) l b in_l b_ne_const,
        end,
    end,
end
using_well_founded 
{ rel_tac := λ _ _, `[exact ⟨_, inv_image.wf (λ a, a.1.leading_monomial) lt_wellfounded⟩] 
, dec_tac := tactic.assumption }

lemma reduction_list_empty (a : (mv_polynomial (fin n) α)) : reduction_list lt_wellfounded a [] = a :=
begin
    unfold reduction_list, 
    have h : reduction_list_aux a [] = a, simp [reduction_list_aux],
    simp [h],
end

lemma zero_reduction_list_aux : ∀ (l : list (Σ' (p: mv_polynomial (fin n) α), p ≠ 0)), reduction_list_aux 0 l = 0
| [] := by simp [reduction_list_aux]
| (hd :: tl) := begin
    by_cases h : leading_term_le (hd.fst) 0;
    simp [h, reduction_list_aux, reduction],
    by_cases h_hd : mv_is_const hd.fst;
    simp [h_hd], swap, 
    have h_0 : leading_coeff (0 : mv_polynomial (fin n) α) = 0, apply zero_iff_leading_coeff_zero.2, refl, repeat {apply_instance},
    have h_hdc : hd.fst.leading_coeff ≠ 0, apply not_zero_iff_leading_coeff_not_zero.2 (nzero_of_ne_mv_is_const h_hd),
    simp [(div_eq_zero_iff h_hdc).2 h_0, monomial],
    generalize hk : -(hd.fst * 0) = k, simp at hk,
    rw ←hk, all_goals {apply zero_reduction_list_aux tl},
end

lemma zero_reduction_list : ∀ (l : list (Σ' (p: mv_polynomial (fin n) α), p ≠ 0)), reduction_list lt_wellfounded 0 l = 0
| [] := by unfold reduction_list; simp [reduction_list_aux]
| (hd :: tl) := begin
    unfold reduction_list, simp [zero_reduction_list_aux lt_wellfounded (list.cons hd tl)],
end

lemma reduction_list_aux_exists_const : ∀ (l : list (Σ' (p: mv_polynomial (fin n) α), p ≠ 0)) (a : mv_polynomial (fin n) α),
    l ≠ [] → (∃ x : (Σ' (p: mv_polynomial (fin n) α), p ≠ 0), x ∈ l ∧ mv_is_const x.1) 
    → reduction_list_aux a l = 0 :=
λ l, begin
    induction l, finish,
    intros a _ hl,
    simp [reduction_list_aux],
    rcases hl with ⟨x, ⟨⟨hxl, hxl⟩, hx⟩⟩,
    have h_le : leading_term_le (l_hd.fst) a,
        have hx' := eq_mv_is_const hx, cases hx' with x' hx',
        simp [hx', leading_term_le, finsupp.leading_term_le, const_leading_monomial, fintype.fintype_fold_and_iff],
    simp [h_le, reduction, hx],
    apply zero_reduction_list_aux lt_wellfounded,
    by_cases h_le : leading_term_le (l_hd.fst) a;
    simp [h_le]; apply l_ih _ (list.ne_nil_of_mem hl_h_left);
    refine ⟨x, ⟨hl_h_left, hx⟩⟩,
end

lemma reduction_list_exists_const : ∀ (l : list (Σ' (p: mv_polynomial (fin n) α), p ≠ 0)) (a : mv_polynomial (fin n) α),
    (∃ x : (Σ' (p: mv_polynomial (fin n) α), p ≠ 0), x ∈ l ∧ mv_is_const x.1) 
    → reduction_list lt_wellfounded a l = 0
| [] := by simp
| (hd :: tl) := λ a hl, begin
    unfold reduction_list, 
    simp [reduction_list_aux_exists_const lt_wellfounded (list.cons hd tl) a (by simp) hl],
    by_cases ha' : 0 = a; simp [ha'],
    by_cases hla : leading_monomial a = 0; simp [hla],
    apply zero_reduction_list,
end

end reduction

section buchberger
variables [decidable_linear_order α]

def s_poly (p q : mv_polynomial (fin n) α) : 
    p ≠ 0 → q ≠ 0 → mv_polynomial (fin n) α :=
λ p_nz q_nz,
    let fst := leading_term_sub' (leading_term_lcm p q p_nz q_nz) p.leading_term (leading_term_le_of_lcm_left p q p_nz q_nz) in
    let snd := leading_term_sub' (leading_term_lcm p q p_nz q_nz) q.leading_term (leading_term_le_of_lcm_right p q p_nz q_nz) in
    (monomial fst 1) * p - (monomial snd 1) * q

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
    := pairs.map (λ a, s_poly a.fst.fst a.fst.snd a.snd.fst a.snd.snd)

def buch_div_result (s s_polys: list (Σ' (p: mv_polynomial (fin n) α), p ≠ 0))
    := (list.foldl (λ a b, 
    let div_result := reduction_list lt_wellfounded (b: (Σ' (p: mv_polynomial (fin n) α), p ≠ 0)).fst a
    in if div_result ∉ list.map psigma.fst a 
        then (if h: div_result = 0 then a else ⟨div_result, h⟩ :: a ) else a) s s_polys)

def filter_non_zero : list (mv_polynomial (fin n) α) →
    list (Σ' (p: mv_polynomial (fin n) α), p ≠ 0)
| [] := []
| (x :: xs) := if h: x = 0 then filter_non_zero xs else ⟨x, h⟩ :: filter_non_zero xs

def non_zero_poly_to_ideal : list (Σ' (p: mv_polynomial (fin n) α), p ≠ 0) → ideal (mv_polynomial (fin n) α) :=
    λ s, ideal.span $ finset.to_set $ list.to_finset $ s.map (λ (a : (Σ' (p: mv_polynomial (fin n) α), p ≠ 0)), a.1.leading_term)

lemma mem_nez : ∀ (s : list (Σ' (p: mv_polynomial (fin n) α), p ≠ 0)) (p : mv_polynomial (fin n) α),
    p ∈ (s.map (λ (a : (Σ' (p: mv_polynomial (fin n) α), p ≠ 0)), a.1.leading_term)).to_finset → 
    (p ≠ 0 ∧ ∃ (ps : fin n →₀ ℕ) (pa : α), monomial ps pa = p)
| [] := by simp
| (hd :: tl) := λ p hp, begin
    simp [leading_term] at hp,
    cases hp,
    simp [hp], split,
    apply monomial_ne_zero_lem, apply not_zero_iff_leading_coeff_not_zero.2, exact hd.snd,
    repeat {apply_instance}, 
    apply exists.intro hd.fst.leading_monomial, apply exists.intro hd.fst.leading_coeff, refl,
    rcases hp with ⟨a, ⟨ha, hp⟩⟩,
    simp [hp.symm], split,
    apply monomial_ne_zero_lem, apply not_zero_iff_leading_coeff_not_zero.2, exact a.snd,
    repeat {apply_instance}, 
    apply exists.intro a.fst.leading_monomial, apply exists.intro a.fst.leading_coeff, refl,
end

include lt_wellfounded

def buch_one_step (s : list (Σ' (p: mv_polynomial (fin n) α), p ≠ 0)) := 
    buch_div_result lt_wellfounded s $ filter_non_zero $ buch_s_polys $ buch_pairs s

lemma subset_of_buch_div_result : ∀ (s_poly s : list (Σ' (p: mv_polynomial (fin n) α), p ≠ 0)), 
    s ⊆ buch_div_result lt_wellfounded s s_poly :=
λ s_poly, begin
    induction s_poly, simp [buch_div_result],
    intro s,
    by_cases h : reduction_list lt_wellfounded (s_poly_hd.fst) s ∉ list.map psigma.fst s;
    simp [buch_div_result, h, -list.mem_map, -list.map.equations._eqn_2, -list.cons_subset] at s_poly_ih ⊢,
    by_cases h' : reduction_list lt_wellfounded (s_poly_hd.fst) s = 0;
    simp [h', -list.cons_subset] at s_poly_ih ⊢, 
    any_goals {exact s_poly_ih s},
    have h_sub : s ⊆ (((⟨reduction_list lt_wellfounded s_poly_hd.fst s, h'⟩) : (Σ' (p: mv_polynomial (fin n) α), p ≠ 0)) :: s), simp,
    apply list.subset.trans h_sub,
    apply s_poly_ih,
end

set_option trace.simplify.rewrite true
lemma buch_one_step_not_mem_span : ∀ (s_poly s : list (Σ' (p: mv_polynomial (fin n) α), p ≠ 0))
(h : buch_div_result lt_wellfounded s s_poly ≠ s) 
(hs : ∀ a : (Σ' (p: mv_polynomial (fin n) α), p ≠ 0), a ∈ s → ¬ mv_is_const a.1),
∃ a : (Σ' (p: mv_polynomial (fin n) α), p ≠ 0),
    a ∈ buch_div_result lt_wellfounded s s_poly ∧ a.fst.leading_term ∉ non_zero_poly_to_ideal s :=
λ s_poly, begin
    induction s_poly, finish, 
    intros s h hs,
    by_cases H : reduction_list lt_wellfounded s_poly_hd.fst s ∉ list.map psigma.fst s;
    simp [buch_div_result, list.foldl_cons, -list.mem_map, -list.map.equations._eqn_2, H, -list.forall_mem_cons'] at h ⊢ s_poly_ih,
    by_cases h_red : reduction_list lt_wellfounded (s_poly_hd.fst) s = 0;
    simp [h_red, -list.mem_map, -list.forall_mem_cons'] at h ⊢ s_poly_ih, any_goals {apply s_poly_ih s h hs}, 
    use ⟨reduction_list lt_wellfounded (s_poly_hd.fst) s, h_red⟩,
    split, { 
        have h_ := subset_of_buch_div_result lt_wellfounded s_poly_tl ((⟨reduction_list lt_wellfounded (s_poly_hd.fst) s, h_red⟩ : (Σ' (p : mv_polynomial (fin n) α), p ≠ 0)) :: s),
        simp [buch_div_result, -list.mem_map, -list.forall_mem_cons'] at h_,
        apply h_.left,
    },
    have h₁ := λ a ha, reduction_list_lem lt_wellfounded s_poly_hd.fst s a ha (hs a ha),
    simp [leading_term_le, finsupp.leading_term_le, fintype.fintype_fold_and_iff,
        -list.mem_cons_iff, -list.ball_cons] at h₁,
    have h₁' : ∀ a : mv_polynomial (fin n) α, 
        a ∈ (s.map (λ (x : Σ' (p : mv_polynomial (fin n) α), p ≠ 0), leading_term (x.fst))).to_finset 
        → (¬∀ x, (a.leading_monomial x ≤ (leading_monomial (reduction_list lt_wellfounded s_poly_hd.fst s)) x)),
        simp, intros a a' ha' haa',
        rwcs [←haa', leading_term, ←(leading_monomial_eq a'.fst.leading_monomial (not_zero_iff_leading_coeff_not_zero.2 a'.snd))],
        apply h₁ a' ha',
    cases s, {
        simp [non_zero_poly_to_ideal, buch_pairs, buch_s_polys, buch_div_result, filter_non_zero, leading_term, ideal.span],
        apply monomial_ne_zero_lem (leading_monomial (reduction_list lt_wellfounded s_poly_hd.fst [])),
        apply not_zero_iff_leading_coeff_not_zero.2 h_red,
    },
    intro h_mem,
    letI := @finsupp.fin_n.decidable_monomial_order n,
    have inst : is_monomial_order ((fin n) →₀ ℕ) (≤),
        constructor, apply _inst.mono_order,
    have h' := monomial_mem_ideal ((list.cons s_hd s_tl).map (λ (a : (Σ' (p: mv_polynomial (fin n) α), p ≠ 0)), a.1.leading_term)).to_finset
        (by simp) _ _ h_mem _,
    rcases h' with ⟨q, ⟨hq, h⟩⟩,
    have h_ := leading_monomial_eq (⟨reduction_list lt_wellfounded s_poly_hd.fst (list.cons s_hd s_tl), h_red⟩ : (Σ' (p : mv_polynomial (fin n) α), p ≠ 0)).fst.leading_monomial
        (not_zero_iff_leading_coeff_not_zero.2 (⟨reduction_list lt_wellfounded s_poly_hd.fst (list.cons s_hd s_tl), h_red⟩ : (Σ' (p : mv_polynomial (fin n) α), p ≠ 0)).snd),
    rwcs [leading_term, ←h_] at h,
    apply (h₁' q hq) h,
    {
        intros p hp, simp at hp, cases hp,
        simp [hp, leading_term],
        refine ⟨monomial_ne_zero_lem _ (not_zero_iff_leading_coeff_not_zero.2 s_hd.2), ⟨s_hd.fst.leading_monomial, ⟨s_hd.fst.leading_coeff, rfl⟩⟩⟩,
        rcases hp with ⟨p', ⟨hp', hp⟩⟩,
        simp [hp.symm, leading_term],
        refine ⟨monomial_ne_zero_lem _ (not_zero_iff_leading_coeff_not_zero.2 p'.2), ⟨p'.fst.leading_monomial, ⟨p'.fst.leading_coeff, rfl⟩⟩⟩,
    }, 
    simp [leading_term],
    refine ⟨monomial_ne_zero_lem (leading_monomial (reduction_list lt_wellfounded s_poly_hd.fst (list.cons s_hd s_tl))) (not_zero_iff_leading_coeff_not_zero.2 h_red), 
            ⟨(leading_monomial (reduction_list lt_wellfounded s_poly_hd.fst (list.cons s_hd s_tl))),
                ⟨(leading_coeff (reduction_list lt_wellfounded s_poly_hd.fst (list.cons s_hd s_tl))), rfl⟩⟩⟩,
end

lemma buch_div_result_eq_of_exists_const : ∀ (s s_poly : list (Σ' (p: mv_polynomial (fin n) α), p ≠ 0)),
    (∃ x : (Σ' (p: mv_polynomial (fin n) α), p ≠ 0), x ∈ s ∧ mv_is_const x.1) 
    → buch_div_result lt_wellfounded s s_poly = s :=
λ s s_poly hs, begin
    induction s_poly, simp [buch_div_result],
    by_cases h : reduction_list lt_wellfounded (s_poly_hd.fst) s ∉ list.map psigma.fst s;
    simp [buch_div_result, h, -list.mem_map, reduction_list_exists_const lt_wellfounded s s_poly_hd.fst hs] at s_poly_ih ⊢;
    assumption,
end

lemma ideal_increase (s : list (Σ' (p: mv_polynomial (fin n) α), p ≠ 0)) (h : buch_one_step lt_wellfounded s ≠ s) :
    non_zero_poly_to_ideal s < non_zero_poly_to_ideal (buch_one_step lt_wellfounded s) :=
begin
    simp [buch_one_step, lt_iff_le_and_ne] at h ⊢, split,
    simp [non_zero_poly_to_ideal], 
    apply ideal.span_mono, simp [list.subset_to_finset.symm], apply list.map_subset, 
    apply subset_of_buch_div_result lt_wellfounded (filter_non_zero (buch_s_polys (buch_pairs s))) s,

    have H := buch_one_step_not_mem_span lt_wellfounded (filter_non_zero (buch_s_polys (buch_pairs s))) s h _,
    intro h_eq,
    rcases H with ⟨a, ⟨ha₁, ha₂⟩⟩, rw h_eq at ha₂,
    have ha₂' : a.fst.leading_term ∈ 
        (buch_div_result lt_wellfounded s (filter_non_zero (buch_s_polys (buch_pairs s)))).map 
            (λ (a : Σ' (p : mv_polynomial (fin n) α), p ≠ 0), leading_term (a.fst)) := list.mem_map_of_mem _ ha₁,
    rw [list.mem_to_set] at ha₂',
    apply ha₂ (ideal.mem_set ha₂'),

    intros a ha₁ ha₂, apply h,
    apply buch_div_result_eq_of_exists_const lt_wellfounded s (filter_non_zero (buch_s_polys (buch_pairs s))),
    finish,
end

def buchberger : list (Σ' (p: mv_polynomial (fin n) α), p ≠ 0) → 
    list (Σ' (p: mv_polynomial (fin n) α), p ≠ 0)
| s :=
    let result := buch_div_result lt_wellfounded s 
        $ filter_non_zero
        $ buch_s_polys
        $ buch_pairs s
        in if h : s = result then s else  
            have non_zero_poly_to_ideal s < non_zero_poly_to_ideal result := ideal_increase lt_wellfounded s (ne.symm h),
            buchberger result
using_well_founded 
{ rel_tac := λ _ _, 
`[exact ⟨_, inv_image.wf non_zero_poly_to_ideal seqR.ideal_wf⟩] 
, dec_tac := tactic.assumption }

end buchberger
end fin_n
end mv_polynomial