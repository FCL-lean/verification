import order_mv_polynomial noetherian

open mv_polynomial
open finsupp

namespace buch
variables {σ : Type*} {α : Type*} [decidable_eq σ] [decidable_eq α] [discrete_field α] [fintype σ]
variables [decidable_linear_order (σ →₀ ℕ)] [is_well_founded (σ →₀ ℕ) (<)] [is_monomial_order (σ →₀ ℕ) (≤)] 

section reduction

def reduction (a b : mv_polynomial σ α) := 
    a - b * (monomial (a.LM - b.LM) (a.LC / b.LC))

def red_list_aux : mv_polynomial σ α → list (mv_polynomial σ α) → mv_polynomial σ α
| a [] := a
| a (hd :: tl) := if h : hd.LM ∣ a.LM  then red_list_aux (reduction a hd) tl else red_list_aux a tl

lemma reduction_C_C {a b : α} (hb : b ≠ 0) : reduction ((C a) : mv_polynomial σ α) (C b) = 0 := begin
    simp [reduction, C, monomial_mul_monomial, hb, mul_div_cancel' _ hb],
end

lemma reduction_of_LM_eqz {p q : mv_polynomial σ α} (hp : p.LM = 0) (hq : q.LM = 0) (hq' : q ≠ 0) : reduction p q = 0 :=
by rw [eqC_of_LM_eqz.1 hp, eqC_of_LM_eqz.1 hq, reduction_C_C (LC_nez_iff.1 hq')]

lemma zero_red_list_aux : ∀ (l : list (mv_polynomial σ α)), red_list_aux 0 l = 0
| [] := by simp [red_list_aux]
| (q :: l') := begin
    by_cases q.LM ∣ (0 : mv_polynomial (σ) α).LM;
    simp [red_list_aux, h, reduction];
    exact zero_red_list_aux l',
end

theorem reduction_LM_lt {a b : mv_polynomial σ α} (hba : b.LM ∣ a.LM) (ha : a.LM ≠ 0) (hb : b ≠ 0) : (reduction a b).LM < a.LM := begin
    simp [reduction],
    apply sub_LM_lt,
    rw [LM_of_mul_m hb (div_ne_zero _ (LC_nez_iff.1 hb)), add_sub_cancel' hba],
    apply LC_nez_of_LM_nez ha,
    simp [LC_of_mul_m hb, mul_div_cancel' _ (LC_nez_iff.1 hb)],
    assumption,
end

lemma red_list_aux_red_LM_lt : ∀ (l : list (mv_polynomial σ α)) {p q : mv_polynomial σ α} (hqp : q.LM ∣ p.LM) (hp : p.LM ≠ 0) (hq : q ≠ 0),
(red_list_aux (reduction p q) l).LM < p.LM 
| [] := by simp [red_list_aux]; apply reduction_LM_lt
| (r :: l') := 
λ p q hqp hp hq, begin 
    by_cases h_dvd : r.LM ∣ (reduction p q).LM;
    simp [red_list_aux, h_dvd],
    {
        by_cases hr : r = 0,
        {simp [reduction, hr], apply red_list_aux_red_LM_lt, assumption'},
        by_cases h_r : (reduction p q).LM = 0,
        simp [h_r] at h_dvd,
        {
            rw [reduction_of_LM_eqz h_r h_dvd hr, zero_red_list_aux],
            simpa [finsupp.zero_lt_iff_ne_zero] using hp,
        },
        {apply lt_trans (red_list_aux_red_LM_lt l' h_dvd h_r hr) (reduction_LM_lt hqp hp hq)},
    },
    {apply red_list_aux_red_LM_lt; assumption},
end

theorem red_list_aux_LM_lt : ∀ (l : list (mv_polynomial σ α)) (p : mv_polynomial σ α) (hp : p.LM ≠ 0) 
(h_red : red_list_aux p l ≠ p), (red_list_aux p l).LM < p.LM 
| [] := by simp [red_list_aux] 
| (r :: l') := λ p hp h_red, begin
    by_cases hr : r = 0,
    simp [red_list_aux , reduction, hr] at h_red ⊢,
    apply red_list_aux_LM_lt, assumption',
    by_cases hrp : r.LM ∣ p.LM;
    simp [red_list_aux, hrp] at h_red ⊢, 
    apply red_list_aux_red_LM_lt l' hrp hp hr,
    apply red_list_aux_LM_lt, assumption',
end

def red_list : mv_polynomial σ α → list (mv_polynomial σ α) → mv_polynomial σ α
| a l := 
    let r := red_list_aux a l in
    if h₁ : r = a
    then r
    else if h₂ : a.LM = 0
        then 0
        else have r.LM < a.LM := red_list_aux_LM_lt _ _ h₂ h₁,
            red_list r l
using_well_founded 
{ rel_tac := λ _ _, `[exact ⟨_, inv_image.wf (λ a, a.1.LM) _inst_6.wf⟩] 
, dec_tac := tactic.assumption }

lemma zero_red_list : ∀ (l : list (mv_polynomial σ α)), red_list 0 l = 0
| [] := by unfold red_list; simp [red_list_aux]
| (hd :: tl) := begin
    unfold red_list, simp [zero_red_list_aux],
end

lemma eqz_of_red_list_aux_eq : ∀ (l : list (mv_polynomial σ α)) (p : mv_polynomial σ α), 
(red_list_aux p l = p) → (∃ (q : mv_polynomial σ α) (hq₁ : q ∈ l) (hq₂ : q ≠ 0), q.LM = 0) → p = 0 
| [] := by simp
| (r :: l') := λ p, begin
    simp_intros hp₁ hl [red_list_aux, -finset.insert_empty_eq_singleton],
    rcases hl with ⟨q, ⟨hq | hq, hq'₁, hq'₂⟩⟩,
    {
        rw hq at hq'₁ hq'₂,
        simp [hq'₂] at hp₁,
        by_cases hp₂ : p.LM = 0,
        {rw [reduction_of_LM_eqz hp₂ hq'₂ hq'₁, zero_red_list_aux] at hp₁, exact hp₁.symm},
        {
            have h := @red_list_aux_red_LM_lt _ _ _ _ _ _ _ _ _ l' p r (by simp [hq'₂]) hp₂ hq'₁,
            rw hp₁ at h,
            apply absurd h (lt_irrefl _),
        },
    },
    by_cases hrp : r.LM ∣ p.LM;
    simp [hrp] at hp₁,
    {
        by_cases hr : r = 0, 
        {
            simp [hr, reduction] at hp₁,
            apply eqz_of_red_list_aux_eq l' _ hp₁,
            refine ⟨q, hq, hq'₁, hq'₂⟩,
        },
        {
            by_cases hp₂ : p.LM = 0,
            {
                simp [hp₂] at hrp,
                rw [reduction_of_LM_eqz hp₂ hrp hr, zero_red_list_aux] at hp₁, exact hp₁.symm,
            },
            {
                have h := red_list_aux_red_LM_lt l' hrp hp₂ hr,
                rw hp₁ at h,
                apply absurd h (lt_irrefl _),
            },
        },
    },
    {apply eqz_of_red_list_aux_eq l' _ hp₁, refine ⟨q, hq, hq'₁, hq'₂⟩},
end

lemma red_list_eqz_of_const : ∀ (p : mv_polynomial σ α) (l : list (mv_polynomial σ α)), 
(∃ (q : mv_polynomial σ α) (hq₁ : q ∈ l) (hq₂ : q ≠ 0), q.LM = 0) → red_list p l = 0 
| p l := λ h, begin 
    unfold red_list, 
    by_cases hp₁ : red_list_aux p l = p;
    by_cases hp₂ : p.LM = 0;
    simp [hp₁, hp₂], 
    repeat {apply eqz_of_red_list_aux_eq l _ hp₁ h},
    {
        let : (red_list_aux p l).LM < p.LM, from red_list_aux_LM_lt l p hp₂ hp₁,
        apply red_list_eqz_of_const, assumption,
    }
end
using_well_founded 
{ rel_tac := λ _ _, `[exact ⟨_, inv_image.wf (λ a, a.1.LM) _inst_6.wf⟩] 
, dec_tac := tactic.assumption }


lemma red_list_nez_no_const : ∀ (l : list (mv_polynomial σ α)) (p : mv_polynomial σ α) (h : red_list p l ≠ 0) 
(q : mv_polynomial σ α) (hq₁ : q ∈ l) (hq₂ : q ≠ 0), q.LM ≠ 0 :=
λ l p h q hq₁ hq₂ hq₃, h (red_list_eqz_of_const _ _ ⟨q, hq₁, hq₂, hq₃⟩)


lemma red_list_aux_not_div : ∀ (l : list (mv_polynomial σ α)) (p : mv_polynomial σ α) (h : red_list_aux p l = p)
    (q : mv_polynomial σ α) (hq₁ : q ∈ l) (hq₂ : q.LM ≠ 0), q.LM ∤ p.LM
| [] := by simp
| (r :: l') := begin 
    simp_intros p hp₁ q hq₁ hq₂ [red_list_aux, -finset.insert_empty_eq_singleton], cases hq₁;
    by_cases hrp : r.LM ∣ p.LM; simp [hrp] at hp₁,
    {
        by_cases hp : p.LM = 0,
        {
            rw hq₁ at hq₂,
            simp [hp] at hrp,
            apply absurd hrp hq₂,
        },
        {
            rw hq₁ at hq₂,
            have h_r := red_list_aux_red_LM_lt l' hrp hp (nez_of_LM_nez hq₂),
            rw [hp₁] at h_r, apply absurd h_r (lt_irrefl _),
        },
    },
    {rwa hq₁,},
    {
        by_cases hr : r = 0,
        {simp [reduction, hr] at hp₁, apply red_list_aux_not_div l', assumption',},
        {
            by_cases hp : p.LM = 0,
            {
                simp [hp]at hrp,
                simp [reduction_of_LM_eqz hp hrp hr, zero_red_list_aux] at hp₁,
                simpa [hp₁.symm] using hq₂,
            },
            {
                have h_r := red_list_aux_red_LM_lt l' hrp hp hr,
                rw [hp₁] at h_r, apply absurd h_r (lt_irrefl _),
            },
        },
    },
    {apply red_list_aux_not_div l', assumption'},
end


theorem red_list_not_div : ∀ (p : mv_polynomial σ α) (l : list (mv_polynomial σ α)) (h : red_list p l ≠ 0)
    (q : mv_polynomial σ α) (hq₁ : q ∈ l) (hq₂ : q ≠ 0), q.LM ∤ (red_list p l).LM
| p l := λ h q hq₁ hq₂, begin
    have hq₃ := red_list_nez_no_const l p h _ hq₁ hq₂,
    unfold red_list at ⊢ h, 
    by_cases hp₁ : red_list_aux p l = p; 
    by_cases hp₂ : p.LM = 0; 
    simp [hp₁, hp₂], assumption',
    {apply red_list_aux_not_div _ _ hp₁ _ hq₁ hq₃},
    {
        let : (red_list_aux p l).LM < p.LM, from red_list_aux_LM_lt l p hp₂ hp₁,
        apply red_list_not_div, simp [hp₁, hp₂] at h,
        assumption',
    }
end
using_well_founded 
{ rel_tac := λ _ _, `[exact ⟨_, inv_image.wf (λ a, a.1.LM) _inst_6.wf⟩] 
, dec_tac := tactic.assumption }

end reduction

def s_poly (p q : mv_polynomial σ α) : mv_polynomial σ α := 
    let X := m_lcm (LM p) (LM q) in
    --let Xc := lcm (LC p) (LC q) in
    monomial (X - p.LM) (1 / (LC p)) * p - monomial (X - q.LM) (1 / (LC q)) * q

def s_polyL : mv_polynomial σ α → list (mv_polynomial σ α) → list (mv_polynomial σ α)
| p [] := []
| p (q :: l₁) := s_poly p q :: s_polyL p l₁

def s_polys : list (mv_polynomial σ α) → list (mv_polynomial σ α)
| [] := []
| (a :: l) := s_polyL a l ++ (s_polys l)

lemma mem_s_polyL {p q : mv_polynomial σ α} : ∀ {l : list (mv_polynomial σ α)},
q ∈ l → s_poly p q ∈ s_polyL p l
| [] := by simp
| (hd :: tl) := begin
    simp_intros hq [s_polyL],
    cases hq,
    {simp [hq]},
    {simp [mem_s_polyL hq]}
end

lemma s_poly_comm {p q : mv_polynomial σ α} : s_poly p q = -(s_poly q p) :=
by simp [s_poly, m_lcm_comm]

set_option class.instance_max_depth 50
theorem red_list_not_mem_span (l : list (mv_polynomial σ α)) (p : mv_polynomial σ α) (h : red_list p l ≠ 0) :
    monomial (red_list p l).LM (red_list p l).LC ∉ monomial_ideal l :=
λ h_mem, begin
    have h_nd := red_list_not_div p l h,
    rcases monomial_mem_ideal _ l h_mem with ⟨q, ⟨hq₁, hq₂⟩, hq₃⟩, 
    apply h_nd; assumption, rwa ←LC_nez_iff,
end

theorem ideal_increase (l : list (mv_polynomial σ α)) (p : mv_polynomial σ α) (h : red_list p l ≠ 0) :
    monomial_ideal l < monomial_ideal (list.cons (red_list p l) l) := 
begin
    simp [lt_iff_le_and_ne], split,
    apply ideal.span_mono, simp, 
    intro H,
    apply red_list_not_mem_span l p h, rw H,
    simp [monomial_ideal, ideal.mem_span_insert], 
    refine ⟨1, 0, by simp, by simp⟩, 
end

def buchberger : (list (mv_polynomial σ α) × list (mv_polynomial σ α)) → list (mv_polynomial σ α)
| ⟨l₁, []⟩ := l₁
| ⟨l₁, (p :: l₂)⟩ :=
    let lex := prod.lex ((>) : ideal (mv_polynomial σ α) → ideal (mv_polynomial σ α) → Prop) nat.lt in
    let a := red_list p l₁ in
    if h : a = 0 
    then 
        have lex ⟨monomial_ideal l₁, l₂.length⟩ ⟨monomial_ideal l₁, (list.cons p l₂).length⟩ := 
            by right; rw [list.length_cons]; apply nat.lt_succ_self,
        buchberger ⟨l₁, l₂⟩
    else 
        have lex ⟨monomial_ideal (list.cons a l₁), (s_polyL a l₁ ++ l₂).length⟩ ⟨monomial_ideal l₁, (list.cons p l₂).length⟩ := 
            by left; exact ideal_increase l₁ p h,
        buchberger ⟨a :: l₁, s_polyL a l₁ ++ l₂⟩
using_well_founded 
{ rel_tac := λ _ _, 
`[exact ⟨_, inv_image.wf (λ ⟨l₁, l₂⟩, prod.mk (monomial_ideal l₁) l₂.length) (prod.lex_wf ideal_wf nat.lt_wf)⟩ ] 
, dec_tac := tactic.assumption }

end buch