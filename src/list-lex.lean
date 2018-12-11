import data.list.basic
import util
variables {α : Type*} {β : Type*}

namespace list
namespace fin_n
section general
variables [has_lt α]
inductive lex : list α → list α → Prop
| nil {a₁ a₂ l₁ l₂} (h₁ : list.length l₁ = list.length l₂) (h₃ : a₁ < a₂) : lex (a₁ :: l₁) (a₂ :: l₂)
| rel {a l₁ l₂} (h₁ : lex l₁ l₂) : lex (a :: l₁) (a :: l₂)

lemma acc_nil : acc (@lex α _) [] := acc.intro [] (λ a ha, by cases ha)

def acc_list_aux : (Σ' (l : list ℕ) (a : ℕ), acc lex l) → ℕ := begin intro, exact a.2.1 end

lemma wf_zero_cons : ∀ l : list ℕ, acc lex l → acc lex (0 :: l) :=
λ l h, begin
    apply acc.rec_on h, intros,
    apply acc.intro, intros l' hl',
    cases hl', cases hl'_h₃,
    apply ih hl'_l₁ hl'_h₁,
end

def wf_aux (l : list ℕ) : ℕ × ℕ := ⟨l.length, l.head⟩

/-
lemma wf : ∀ (a : list ℕ), acc lex a
| a :=
begin
    cases ha : a,
    apply acc_nil,
    let H : prod.lex has_lt.lt has_lt.lt (wf_aux tl) (wf_aux a),
    left, simp [ha], constructor,
    apply acc.rec_on (wf tl), intros,
    apply acc.intro, intros b hb,
    cases hhb : hb,
    swap, apply ih l₁ h₁,
    --let H : prod.lex has_lt.lt has_lt.lt (wf_aux (a₁ :: l₁)) (wf_aux a),
    --rw [ha], unfold wf_aux, simp, 
    apply wf (a₁ :: l₁),
end 
using_well_founded 
{ rel_tac := λ _ _, `[exact ⟨inv_image (prod.lex (<) (<)) wf_aux, 
                                    @inv_image.wf _ _ _ wf_aux (prod.lex_wf nat.lt_wf nat.lt_wf)⟩] 
, dec_tac := `[unfold has_well_founded.r inv_image, assumption] }
-/
end general

end fin_n
end list