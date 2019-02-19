import order_mv_polynomial discrete_field

open mv_polynomial
open finsupp

namespace buch
variables {σ : Type*} {α : Type*} [decidable_eq σ] [decidable_eq α] [discrete_field α] [fintype σ]
variables [decidable_linear_order (σ →₀ ℕ)]

section reduction

def reduction (a b : mv_polynomial σ α) := 
    a - b * (monomial (a.lm - b.lm) (a.lc / b.lc))

def red_one_step (S : finset (mv_polynomial σ α)) : mv_polynomial σ α → mv_polynomial σ α → Prop :=
    λ p q, ∃ (r : mv_polynomial σ α) (h₁ : r ∈ S) (h₂ : r.lm ∣ p.lm ), reduction p r = q

def red_plus (S : finset (mv_polynomial σ α)) : mv_polynomial σ α → mv_polynomial σ α → Prop := tc (red_one_step S)

def red_star (S : finset (mv_polynomial σ α)) : mv_polynomial σ α → mv_polynomial σ α → Prop := rtc (red_one_step S)

notation a `→[` S `]` b := red_one_step S a b

notation a `→[` S `]⁺` b := red_plus S a b

notation a `→[` S `]⋆` b := red_star S a b

def red_list_aux : mv_polynomial σ α → list (mv_polynomial σ α) → mv_polynomial σ α
| a [] := a
| a (hd :: tl) := if h : hd.lm ∣ a.lm  then red_list_aux (reduction a hd) tl else red_list_aux a tl

lemma reduction_C_C {a b : α} (hb : b ≠ 0) : reduction ((C a) : mv_polynomial σ α) (C b) = 0 := begin
    simp [reduction, C, monomial_mul_monomial, hb, mul_div_cancel' _ hb],
end

section fin
variables {n : ℕ}
lemma reduction_of_lm_eqz {p q : mv_polynomial (fin n) α} (hp : p.lm = 0) (hq : q.lm = 0) (hq' : q ≠ 0) : reduction p q = 0 :=
begin
    rw [eqC_of_lm_eqz.1 hp, eqC_of_lm_eqz.1 hq, reduction_C_C _],
    rw [←mem_support_iff, singleton_of_lm_eqz.1 ⟨hq', hq⟩], simp,
end

lemma zero_red_list_aux : ∀ (l : list (mv_polynomial (fin n) α)), red_list_aux 0 l = 0
| [] := by simp [red_list_aux]
| (q :: l') := begin
    by_cases q.lm ∣ (0 : mv_polynomial (fin n) α).lm;
    simp [red_list_aux, h, reduction];
    exact zero_red_list_aux l',
end

lemma reduction_lm_lt {a b : mv_polynomial (fin n) α} (hba : b.lm ∣ a.lm) (ha : a.lm ≠ 0) (hb : b ≠ 0) : (reduction a b).lm < a.lm := begin
    simp [reduction],
    apply sub_lm_lt,
    rw [lm_of_mul hb (div_ne_zero _ (lc_nez_iff.1 hb)), add_sub_cancel' hba],
    apply lc_nez_of_lm_nez ha,
    simp [lc_of_mul hb, mul_div_cancel' _ (lc_nez_iff.1 hb)],
    assumption,
end

lemma red_list_aux_lm_lt : ∀ (l : list (mv_polynomial (fin n) α)) {p q : mv_polynomial (fin n) α} (hqp : q.lm ∣ p.lm) (hp : p.lm ≠ 0) (hq : q ≠ 0),
(red_list_aux (reduction p q) l).lm < p.lm 
| [] := by simp [red_list_aux]; apply reduction_lm_lt
| (r :: l') := 
λ p q hqp hp hq, begin 
    by_cases h_dvd : r.lm ∣ (reduction p q).lm;
    simp [red_list_aux, h_dvd],
    {
        by_cases hr : r = 0,
        {simp [reduction, hr], apply red_list_aux_lm_lt, assumption'},
        by_cases h_r : (reduction p q).lm = 0,
        simp [h_r] at h_dvd,
        {
            rw [reduction_of_lm_eqz h_r h_dvd hr, zero_red_list_aux],
            simpa [finsupp.fin.zero_lt_iff_ne_zero] using hp,
        },
        {apply lt_trans (red_list_aux_lm_lt l' h_dvd h_r hr) (reduction_lm_lt hqp hp hq)},
    },
    {apply red_list_aux_lm_lt; assumption},
end

lemma red_list_aux_lm_lt' : ∀ (l : list (mv_polynomial (fin n) α)) (p : mv_polynomial (fin n) α) (hp : p.lm ≠ 0) 
(h_red : red_list_aux p l ≠ p), (red_list_aux p l).lm < p.lm 
| [] := by simp [red_list_aux] 
| (r :: l') := λ p hp h_red, begin
    by_cases hr : r = 0,
    simp [red_list_aux , reduction, hr] at h_red ⊢,
    apply red_list_aux_lm_lt', assumption',
    by_cases hrp : r.lm ∣ p.lm;
    simp [red_list_aux, hrp] at h_red ⊢, 
    apply red_list_aux_lm_lt l' hrp hp hr,
    apply red_list_aux_lm_lt', assumption',
end

def red_list : mv_polynomial (fin n) α → list (mv_polynomial (fin n) α) → mv_polynomial (fin n) α
| a l := 
    let r := red_list_aux a l in
    if h₁ : r = a
    then r
    else if h₂ : a.lm = 0
        then 0
        else have r.lm < a.lm := red_list_aux_lm_lt' _ _ h₂ h₁,
            red_list r l
using_well_founded 
{ rel_tac := λ _ _, `[exact ⟨_, inv_image.wf (λ a, a.1.lm) fin.lt_wf⟩] 
, dec_tac := tactic.assumption }

lemma zero_red_list : ∀ (l : list (mv_polynomial (fin n) α)), red_list 0 l = 0
| [] := by unfold red_list; simp [red_list_aux]
| (hd :: tl) := begin
    unfold red_list, simp [zero_red_list_aux],
end

lemma eqz_of_red_list_aux_eq : ∀ (l : list (mv_polynomial (fin n) α)) (p : mv_polynomial (fin n) α), 
(red_list_aux p l = p) → (∃ q : mv_polynomial (fin n) α, q ∈ l ∧ q.support = {0}) → p = 0 
| [] := by simp
| (r :: l') := λ p, begin
    simp_intros hp₁ hl [red_list_aux, -finset.insert_empty_eq_singleton],
    rcases hl with ⟨q, ⟨hq | hq, hq'⟩⟩,
    {
        rw [hq, ←singleton_of_lm_eqz] at hq',
        simp [hq'.right] at hp₁,
        by_cases hp₂ : p.lm = 0,
        {rw [reduction_of_lm_eqz hp₂ hq'.right hq'.left, zero_red_list_aux] at hp₁, exact hp₁.symm},
        {
            have h := @red_list_aux_lm_lt _ _ _ _ l' p r (by simp [hq'.right]) hp₂ hq'.left,
            rw hp₁ at h,
            apply absurd h (lt_irrefl _),
        },
    },
    by_cases hrp : r.lm ∣ p.lm;
    simp [hrp] at hp₁,
    {
        by_cases hr : r = 0, 
        {
            simp [hr, reduction] at hp₁,
            apply eqz_of_red_list_aux_eq l' _ hp₁,
            refine ⟨q, ⟨hq, hq'⟩⟩,
        },
        {
            by_cases hp₂ : p.lm = 0,
            {
                simp [hp₂] at hrp,
                rw [reduction_of_lm_eqz hp₂ hrp hr, zero_red_list_aux] at hp₁, exact hp₁.symm,
            },
            {
                have h := red_list_aux_lm_lt l' hrp hp₂ hr,
                rw hp₁ at h,
                apply absurd h (lt_irrefl _),
            },
        },
    },
    {apply eqz_of_red_list_aux_eq l' _ hp₁, refine ⟨q, ⟨hq, hq'⟩⟩,},
end

lemma red_list_eqz_of_const : ∀ (p : mv_polynomial (fin n) α) (l : list (mv_polynomial (fin n) α)), 
(∃ q : mv_polynomial (fin n) α, q ∈ l ∧ q.support = {0}) → red_list p l = 0 
| p l := λ h, begin 
    unfold red_list, 
    by_cases hp₁ : red_list_aux p l = p;
    simp [hp₁], 
    {apply eqz_of_red_list_aux_eq l _ hp₁ h},
    by_cases hp₂ : p.lm = 0;
    simp [hp₂],
    let : (red_list_aux p l).lm < p.lm, from red_list_aux_lm_lt' l p hp₂ hp₁,
    apply red_list_eqz_of_const, assumption,
end
using_well_founded 
{ rel_tac := λ _ _, `[exact ⟨_, inv_image.wf (λ a, a.1.lm) fin.lt_wf⟩] 
, dec_tac := tactic.assumption }


lemma red_list_nez_no_const : ∀ (l : list (mv_polynomial (fin n) α)) (p : mv_polynomial (fin n) α) (h : red_list p l ≠ 0) 
(q : mv_polynomial (fin n) α) (hq : q ∈ l), q.support ≠ {0} :=
λ l p h q hq₁ hq₂, begin
    apply h, apply red_list_eqz_of_const,
    refine ⟨q, ⟨hq₁, hq₂⟩⟩,
end


lemma red_list_aux_not_div : ∀ (l : list (mv_polynomial (fin n) α)) (p : mv_polynomial (fin n) α) (h : red_list_aux p l = p)
    (q : mv_polynomial (fin n) α) (hq₁ : q ∈ l) (hq₂ : q ≠ 0 ∧ q.support ≠ {0}), q.lm ∤ p.lm
| [] := by simp
| (r :: l') := begin 
    simp_intros p hp₁ q hq₁ hq₂ [red_list_aux, -finset.insert_empty_eq_singleton], cases hq₁;
    by_cases hrp : r.lm ∣ p.lm; simp [hrp] at hp₁,
    {
        by_cases hp : p.lm = 0,
        {
            rw [hq₁, not_const_iff] at hq₂,
            simp [hp] at hrp,
            apply absurd hrp hq₂,
        },
        {
            rw hq₁ at hq₂,
            have h_r := red_list_aux_lm_lt l' hrp hp hq₂.left,
            rw [hp₁] at h_r, apply absurd h_r (lt_irrefl _),
        },
    },
    {rwa hq₁,},
    {
        by_cases hr : r = 0,
        {simp [reduction, hr] at hp₁, apply red_list_aux_not_div l', assumption',},
        {
            by_cases hp : p.lm = 0,
            {
                simp [hp]at hrp,
                simp [reduction_of_lm_eqz hp hrp hr, zero_red_list_aux] at hp₁,
                simp [hp₁.symm],
                rwa not_const_iff at hq₂,
            },
            {
                have h_r := red_list_aux_lm_lt l' hrp hp hr,
                rw [hp₁] at h_r, apply absurd h_r (lt_irrefl _),
            },
        },
    },
    {apply red_list_aux_not_div l', assumption'},
end


lemma red_list_not_div : ∀ (p : mv_polynomial (fin n) α) (l : list (mv_polynomial (fin n) α)) (h : red_list p l ≠ 0)
    (q : mv_polynomial (fin n) α) (hq₁ : q ∈ l) (hq₂ : q ≠ 0), q.lm ∤ (red_list p l).lm
| p l := λ h q hq₁ hq₂, begin
    have hq₃ := red_list_nez_no_const l p h _ hq₁,
    unfold red_list, 
    by_cases hp₁ : red_list_aux p l = p; simp [hp₁],
    apply red_list_aux_not_div _ _ hp₁ _ hq₁ ⟨hq₂, hq₃⟩,
    by_cases hp₂ : p.lm = 0; simp [hp₂],
    apply not_const_iff.1 ⟨hq₂, hq₃⟩,
    let : (red_list_aux p l).lm < p.lm, from red_list_aux_lm_lt' l p hp₂ hp₁,
    apply red_list_not_div, unfold red_list at h, simp [hp₁, hp₂] at h,
    assumption',
end
using_well_founded 
{ rel_tac := λ _ _, `[exact ⟨_, inv_image.wf (λ a, a.1.lm) fin.lt_wf⟩] 
, dec_tac := tactic.assumption }

end fin

end reduction

def s_poly (p q : mv_polynomial σ α) : mv_polynomial σ α := 
    let X := m_lcm (lm p) (lm q) in
    let Xc := lcm (lc p) (lc q) in
    monomial (X - p.lm) (Xc / (lc p)) * p - monomial (X - q.lm) (Xc / (lc q)) * q

/-
def s_polys (S : list (mv_polynomial σ α)) : list (mv_polynomial σ α) :=
do
    a ← S, 
    b ← S, 
        if a = b 
        then []
        else [s_poly a b]
-/
def s_polyL : mv_polynomial σ α → list (mv_polynomial σ α) → list (mv_polynomial σ α) → list (mv_polynomial σ α)
| p l₁ [] := l₁
| p l₁ (q :: l₂) := s_poly p q :: s_polyL p l₁ l₂
        
def nfL (S : list (mv_polynomial σ α)) : list (mv_polynomial σ α) := 
    list.filter (λ a, a ≠ 0) S

section fin
variables {n : ℕ}

lemma red_list_not_mem_span : ∀ (l : list (mv_polynomial (fin n) α)) (p : mv_polynomial (fin n) α) (h : red_list p l ≠ 0),
    monomial (red_list p l).lm (red_list p l).lc ∉ monomial_ideal l :=
λ l p h h_mem, begin
    have h_nd := red_list_not_div p l h,
    rcases monomial_mem_ideal _ l h_mem with ⟨q, ⟨⟨hq₁, hq₂⟩, hq₃⟩⟩, 
    apply h_nd; assumption, rwa ←lc_nez_iff,
end

lemma ideal_increase (l : list (mv_polynomial (fin n) α)) (p : mv_polynomial (fin n) α) (h : red_list p l ≠ 0) :
    monomial_ideal l < monomial_ideal (list.cons (red_list p l) l) := 
begin
    simp [lt_iff_le_and_ne], split,
    apply ideal.span_mono, simp, 
    intro H,
    apply red_list_not_mem_span l p h, rw H,
    simp [monomial_ideal, ideal.mem_span_insert], 
    refine ⟨1, ⟨0, ⟨by simp, by simp⟩⟩⟩, 
end

set_option trace.simplify.rewrite true
def buchberger : (list (mv_polynomial (fin n) α) × list (mv_polynomial (fin n) α)) → list (mv_polynomial (fin n) α)
| ⟨l₁, []⟩ := l₁
| ⟨l₁, (p :: l₂)⟩ :=
    let lex := prod.lex ((>) : ideal (mv_polynomial (fin n) α) → ideal (mv_polynomial (fin n) α) → Prop) nat.lt in
    let a := red_list p l₁ in
    if h : a = 0 
    then 
        have lex ⟨monomial_ideal l₁, l₂.length⟩ ⟨monomial_ideal l₁, (list.cons p l₂).length⟩ := 
            by right; rw [list.length_cons]; apply nat.lt_succ_self,
        buchberger ⟨l₁, l₂⟩
    else 
        have lex ⟨monomial_ideal (list.cons a l₁), (s_polyL a l₂ l₁).length⟩ ⟨monomial_ideal l₁, (list.cons p l₂).length⟩ := 
            by left; exact ideal_increase l₁ p h,
        buchberger ⟨a :: l₁, s_polyL a l₂ l₁⟩
using_well_founded 
{ rel_tac := λ _ _, 
`[exact ⟨_, inv_image.wf (λ ⟨l₁, l₂⟩, prod.mk (monomial_ideal l₁) l₂.length) (prod.lex_wf ideal_wf nat.lt_wf)⟩ ] 
, dec_tac := tactic.assumption }

end fin

end buch