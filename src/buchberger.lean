import mv_polynomial order_finsupp lex_order util

open mv_polynomial
open finsupp

namespace buch
variables {σ : Type*} {α : Type*} [decidable_eq σ] [decidable_eq α] [discrete_field α] [fintype σ]
variables [decidable_linear_order (σ →₀ ℕ)]

section reduction

def reduction (a b : mv_polynomial σ α) := 
    if is_const b then 0
    else a - b * (monomial (a.hd - b.hd) (a.hd_val / b.hd_val))

def red_one_step (S : finset (mv_polynomial σ α)) : mv_polynomial σ α → mv_polynomial σ α → Prop :=
    λ p q, ∃ (r : mv_polynomial σ α) (h₁ : r ∈ S) (h₂ : r.hd ∣ p.hd ), reduction p r = q

def red_plus (S : finset (mv_polynomial σ α)) : mv_polynomial σ α → mv_polynomial σ α → Prop := tc (red_one_step S)

def red_star (S : finset (mv_polynomial σ α)) : mv_polynomial σ α → mv_polynomial σ α → Prop := rtc (red_one_step S)

notation a `→[` S `]` b := red_one_step S a b

notation a `→[` S `]⁺` b := red_plus S a b

notation a `→[` S `]⋆` b := red_star S a b

def red_list_aux : mv_polynomial σ α → list (mv_polynomial σ α) → mv_polynomial σ α
| a [] := a
| a (hd :: tl) := if h : hd.hd ∣ a.hd  then red_list_aux (reduction a hd) tl else red_list_aux a tl


section fin
variables {n : ℕ}
lemma reduction_hd_lt {a b : mv_polynomial (fin n) α} (ha : a.hd ≠ 0) (hba : b.hd ∣ a.hd) : (reduction a b).hd < a.hd := begin
    by_cases is_const b; simp [reduction, h],
    apply lt_of_le_of_ne (finsupp.fin.zero_le a.hd) (ne.symm ha),
    apply sub_hd_lt,
    rw [hd_of_mul (nez_of_not_const h) (div_ne_zero _ (lc_nez_of_not_const h)), add_sub_cancel' hba],
    apply lc_nez_of_not_const (not_const_of_div h hba),
    simp [hd_val_of_mul (nez_of_not_const h), mul_div_cancel' _ (lc_nez_of_not_const h)],
    assumption,
end

lemma red_list_aux_hd_lt (l : list (mv_polynomial (fin n) α)) (p q : mv_polynomial (fin n) α) (hp : p.hd ≠ 0) : 
(red_list_aux (reduction p q) l).hd < p.hd := 
begin
end

lemma red_list_aux_hd_lt' (l : list (mv_polynomial (fin n) α)) (p : mv_polynomial (fin n) α) (hp : p.hd ≠ 0) 
(h_red : red_list_aux p l ≠ p) : 
(red_list_aux p l).hd < p.hd := 
begin
end

def red_list : mv_polynomial (fin n) α → list (mv_polynomial (fin n) α) → mv_polynomial (fin n) α
| a l := 
    let r := red_list_aux a l in
    if h₁ : r = a
    then r
    else if h₂ : a.hd = 0
        then 0
        else have r.hd < a.hd := red_list_aux_hd_lt' _ _ h₂ h₁,
            red_list r l
using_well_founded 
{ rel_tac := λ _ _, `[exact ⟨_, inv_image.wf (λ a, a.1.hd) fin.lt_wf⟩] 
, dec_tac := tactic.assumption }

lemma zero_red_list_aux : ∀ (l : list (mv_polynomial (fin n) α)), red_list_aux 0 l = 0
| [] := by simp [red_list_aux]
| (q :: l') := begin
    by_cases q.hd ∣ (0 : mv_polynomial (fin n) α).hd;
    simp [red_list_aux, h, reduction], 
    {
        by_cases hq : is_const q;
        simp [hq],
        exact zero_red_list_aux l',
        simp [monomial], 
        generalize hq : -(q * 0) = q', simp at hq,
        simp [hq.symm],
        exact zero_red_list_aux l',
    },
    exact zero_red_list_aux l',
end

lemma zero_red_list : ∀ (l : list (mv_polynomial (fin n) α)), red_list 0 l = 0
| [] := by unfold red_list; simp [red_list_aux]
| (hd :: tl) := begin
    unfold red_list, simp [zero_red_list_aux],
end

lemma red_list_aux_eqz_of_const : ∀ (l : list (mv_polynomial (fin n) α)) (p : mv_polynomial (fin n) α), (∃ q ∈ l, is_const q) → red_list_aux p l = 0
| [] := by simp
| (q :: l') := λ p, begin 
    simp [red_list_aux],
    split, 
    intro hhd, simp [const_hd_dvd hhd, reduction, hhd],
    apply zero_red_list_aux,
    intros x hx₁ hx₂,
    by_cases hq : q.hd ∣ p.hd; simp [hq];
    apply red_list_aux_eqz_of_const;
    refine ⟨x, ⟨hx₁, hx₂⟩⟩, 
end

lemma red_list_eqz_of_const : ∀ (l : list (mv_polynomial (fin n) α)) (p : mv_polynomial (fin n) α), (∃ q ∈ l, is_const q) → red_list p l = 0 :=
λ l p h, begin 
    unfold red_list, 
    by_cases hp : 0 = p;
    by_cases hp': hd p = 0;
    simp [red_list_aux_eqz_of_const l p h, hp, hp'],
    apply zero_red_list,
end

lemma red_list_nez_no_const : ∀ (l : list (mv_polynomial (fin n) α)) (p : mv_polynomial (fin n) α) (h : red_list p l ≠ 0) (q ∈ l), ¬is_const q :=
λ l p h q hq₁ hq₂, begin
    apply h, apply red_list_eqz_of_const,
    refine ⟨q, ⟨hq₁, hq₂⟩⟩,
end


lemma red_list_aux_not_div : ∀ (l : list (mv_polynomial (fin n) α)) (p : mv_polynomial (fin n) α) (h : red_list_aux p l = p) 
    (q : mv_polynomial (fin n) α) (hq₁ : q ∈ l) (hq₂ : ¬ is_const q), q.hd ∤ p.hd
| [] := by simp
| (r :: l') := begin 
    simp_intros [red_list_aux], cases hq₁;
    by_cases hrp : hd r ∣ hd p; simp [hrp] at h,
    {
        have h_r := red_list_aux_hd_lt l' p r (not_const_iff_lm_nez.1 (not_const_of_div hq₂ a)),
        simp [red_list_aux, h, hq₁, hrp] at h_r,
        apply lt_irrefl _ h_r,
    },
    {apply hrp, rwa ←hq₁,},
    {
        by_cases hr : is_const r,
        simp [reduction, hr, zero_red_list_aux] at h,
        apply not_const_of_div hq₂ a,
        left, exact h.symm,
        have h_r := red_list_aux_hd_lt l' p r (not_const_iff_lm_nez.1 (not_const_of_div hr hrp)),
        simp [red_list_aux, h, hrp] at h_r,
        apply lt_irrefl _ h_r,
    },
    apply red_list_aux_not_div; assumption,
end


lemma red_list_not_div : ∀ (p : mv_polynomial (fin n) α) (l : list (mv_polynomial (fin n) α)) (h : red_list p l ≠ 0)
    (q : mv_polynomial (fin n) α) (hq₁ : q ∈ l), q.hd ∤ (red_list p l).hd
| p l := λ h q hq₁, begin
    have hq₂ := red_list_nez_no_const l p h _ hq₁,
    unfold red_list, 
    by_cases hp₁ : red_list_aux p l = p; simp [hp₁],
    apply red_list_aux_not_div; assumption,
    by_cases hp₂ : p.hd = 0; simp [hp₂],
    intro hq₃, apply hq₂, rwa [eq_zero_of_div_zero, ←is_const_of_lm_eqz] at hq₃,
    let : (red_list_aux p l).hd < p.hd, from red_list_aux_hd_lt' l p hp₂ hp₁,
    apply red_list_not_div, unfold red_list at h, simp [hp₁, hp₂] at h,
    assumption',
end
using_well_founded 
{ rel_tac := λ _ _, `[exact ⟨_, inv_image.wf (λ a, a.1.hd) fin.lt_wf⟩] 
, dec_tac := tactic.assumption }

end fin

end reduction

def s_poly (p q : mv_polynomial σ α) : mv_polynomial σ α := 
    let X := m_lcm (hd p) (hd q) in
    let Xc := lcm (hd_val p) (hd_val q) in
    monomial (X - p.hd) (Xc / (hd_val p)) * p - monomial (X - q.hd) (Xc / (hd_val q)) * q

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
    monomial (red_list p l).hd (red_list p l).hd_val ∉ monomial_ideal l :=
λ l p h h_mem, begin
    have h_nd := red_list_not_div p l h,
    rcases monomial_mem_ideal _ l h_mem with ⟨q, ⟨hq₁, hq₂⟩⟩, 
    apply h_nd; assumption, rwa ←hd_val_nez_iff,
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