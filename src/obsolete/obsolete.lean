import data.finset
import linear_algebra.multivariate_polynomial
import ring_theory.ideals
import tactic.find
import finsupp
import test
open mv_polynomial
variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {ι : Type*}
variables [discrete_field α]
variables [decidable_eq α] [decidable_linear_order α]
variables [comm_ring (mv_polynomial ℕ α)]

def leading_term_lt_aux : (ℕ →₀ ℕ) → (ℕ →₀ ℕ) → ℕ → Prop
| a b 0 := a 0 < b 0
| a b (nat.succ m) := (a (nat.succ m) < b (nat.succ m) ∧ leading_term_le_aux a b m)
                    ∨ (a (nat.succ m) ≤ b (nat.succ m) ∧ leading_term_lt_aux a b m)

protected def lt (a b : mv_polynomial ℕ α) : Prop 
    := leading_term_lt_aux a.leading_term' b.leading_term' (finsupp.max_ab a.leading_term' b.leading_term') 
instance : has_lt (mv_polynomial ℕ α) := ⟨lt⟩ 

lemma aux_le_of_eq {a b : ℕ →₀ ℕ} (h : a = b) : ∀ n : ℕ, leading_term_le_aux a b n := 
begin
    intro n,
    induction n;
    unfold leading_term_le_aux;
    rw h at *, apply and.intro, refl, assumption,
end

lemma not_aux_lt_of_eq {a b : ℕ →₀ ℕ} (h : a = b) : ∀ n : ℕ, ¬leading_term_lt_aux a b n := 
begin
    intros n hab,
    rw h at hab,
    induction n;
    unfold leading_term_lt_aux at hab,
    apply nat.lt_irrefl (b.to_fun 0), assumption,
    cases hab,
    apply nat.lt_irrefl (b.to_fun (nat.succ n_n)), apply hab.left,
    apply n_ih hab.right,
end

def mv_lt_leading_term_lt : Π (x y : mv_polynomial ℕ α), x < y → x.leading_term' < y.leading_term'
| x y lt := sorry

protected def wf_lt : well_founded (@lt α _ _ _ _) :=
begin
    apply @subrelation.wf _ 
        (λ a b : mv_polynomial ℕ α, prod.lex nat.lt nat.lt 
          (finsupp.max a.leading_term', a.leading_term' (finsupp.max a.leading_term'))
          (finsupp.max b.leading_term', b.leading_term' (finsupp.max b.leading_term'))), 
    swap,
    constructor, intros,
    have inv := @inv_image.accessible _ _ (prod.lex nat.lt nat.lt)
        (λ (a : mv_polynomial ℕ α), 
           (finsupp.max a.leading_term', a.leading_term' (finsupp.max a.leading_term'))) a,
    apply inv,
    apply prod.lex_accessible;
    have lt_wf := nat.lt_wf; cases lt_wf,
    apply lt_wf, apply lt_wf, intro, intros, apply lex_mon_order_imp_lt_lex_order,
    apply mv_lt_leading_term_lt, assumption,
end

instance : has_well_founded (mv_polynomial ℕ α) :=
⟨lt, wf_lt⟩