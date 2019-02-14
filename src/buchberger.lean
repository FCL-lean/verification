import mv_polynomial order_finsupp lex_order util ideal_list

open mv_polynomial
open finsupp

namespace buch
variables {σ : Type*} {α : Type*} [decidable_eq σ] [decidable_eq α] [discrete_field α]
variables [decidable_linear_order (σ →₀ ℕ)]

section reduction

def reduction (a b : mv_polynomial σ α) := a - b * (monomial (a.hd /ₘ b.hd) (a.hd_val / b.hd_val))

def red_one_step (S : finset (mv_polynomial σ α)) : mv_polynomial σ α → mv_polynomial σ α → Prop :=
    λ p q, ∃ (r : mv_polynomial σ α) (h₁ : r ∈ S) (h₂ : r.hd |ₘ  p.hd ), reduction p r = q

def red_plus (S : finset (mv_polynomial σ α)) : mv_polynomial σ α → mv_polynomial σ α → Prop := tc (red_one_step S)

def red_star (S : finset (mv_polynomial σ α)) : mv_polynomial σ α → mv_polynomial σ α → Prop := rtc (red_one_step S)

notation a `→[` S `]` b := red_one_step S a b

notation a `→[` S `]⁺` b := red_plus S a b

notation a `→[` S `]⋆` b := red_star S a b

def red_list_aux : mv_polynomial σ α → list (mv_polynomial σ α) → mv_polynomial σ α
| a [] := a
| a (hd :: tl) := if h : hd.hd |ₘ a.hd  then red_list_aux (reduction a hd) tl else red_list_aux a tl

section fin
variables {n : ℕ}

def red_list : mv_polynomial (fin n) α → list (mv_polynomial (fin n) α) → mv_polynomial (fin n) α
| a l := 
    let r := red_list_aux a l in
    if h : r = a
    then r
    else if a.hd = 0
        then 0
        else have r.hd < a.hd, from sorry,
            red_list r l
using_well_founded 
{ rel_tac := λ _ _, `[exact ⟨_, inv_image.wf (λ a, a.1.hd) fin.lt_wf⟩] 
, dec_tac := tactic.assumption }

end fin

end reduction

def s_poly (p q : mv_polynomial σ α) : mv_polynomial σ α := 
    let X := m_lcm (hd p) (hd q) in
    let Xc := lcm (hd_val p) (hd_val q) in
    monomial (X /ₘ p.hd) (Xc / (hd_val p)) * p - monomial (X /ₘ q.hd) (Xc / (hd_val q)) * q

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

lemma red_list_not_mem_span : ∀ (S : list (mv_polynomial (fin n) α)) (p : mv_polynomial (fin n) α) (h : red_list p S ≠ 0),
    red_list p S ∉ S.to_ideal :=
begin
end

lemma ideal_increase (S : list (mv_polynomial (fin n) α)) (p : mv_polynomial (fin n) α) (h : red_list p S ≠ 0) :
    S.to_ideal < (list.cons (red_list p S) S).to_ideal := 
begin
    simp [lt_iff_le_and_ne], split,
    apply ideal.span_mono, simp [list.to_finset_cons], 
    intro H,
    apply red_list_not_mem_span S p h, rw H,
    simp [list.to_ideal, ideal.mem_span_insert], 
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
        have lex ⟨l₁.to_ideal, l₂.length⟩ ⟨l₁.to_ideal, (list.cons p l₂).length⟩ := 
            by right; rw [list.length_cons]; apply nat.lt_succ_self,
        buchberger ⟨l₁, l₂⟩
    else 
        have lex ⟨(list.cons a l₁).to_ideal, (s_polyL a l₂ l₁).length⟩ ⟨l₁.to_ideal, (list.cons p l₂).length⟩ := 
            by left; exact ideal_increase l₁ p h,
        buchberger ⟨a :: l₁, s_polyL a l₂ l₁⟩
using_well_founded 
{ rel_tac := λ _ _, 
`[exact ⟨_, inv_image.wf (λ ⟨l₁, l₂⟩, prod.mk l₁.to_ideal l₂.length) (prod.lex_wf ideal_wf' nat.lt_wf)⟩ ] 
, dec_tac := tactic.assumption }

end fin

end buch
--ideal_increase l₁ p h