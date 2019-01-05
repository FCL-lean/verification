import ring_theory.ideals
import linear_algebra.multivariate_polynomial
import data.finsupp
import finset
import util
variables {σ : Type*} {α : Type*} 

namespace ideal
variables [comm_ring α] [decidable_eq α]

lemma linear_combination (s : finset α) : 
∀ a ∈ span (↑s : set α), ∃ c : α →₀ α, c.support ⊆ s ∧ a = s.fold (+) 0 (λ x, c.to_fun x * x) :=
begin
    apply finset.induction_on s, 
    {simp [span], apply exists.intro (0 : α →₀ α), simp,},
    intros a s' has' ih x hx,
    simp [finset.coe_insert, mem_span_insert] at hx,
    rcases hx with ⟨ca, ⟨z, ⟨hz, hx⟩⟩⟩,
    rcases (ih z hz) with ⟨c, ⟨hc, hz'⟩⟩,
    apply exists.intro (c + finsupp.single a ca), split,
    apply finset.subset.trans finsupp.support_add (finset.union_subset'_symm hc finsupp.support_single_subset),
    simp [finset.fold_insert has', hx, hz'],
    have hzc : ∀ x ∈ s', (c + finsupp.single a ca) x * x= c x * x,
        intros i hi, simp [finsupp.single_apply],
        by_cases a = i; finish,
    have hfc : s'.fold has_add.add 0 (λ x, (c + finsupp.single a ca).to_fun x * x) = 
        s'.fold has_add.add 0 (λ x, c.to_fun x * x) := finset.fold_congr hzc,
    have hca : (c + finsupp.single a ca) a  * a = ca * a,
        have hca' : c a = 0, rw [←finsupp.not_mem_support_iff], intro ha,
        apply absurd (hc ha) has',
        simp [finsupp.single_apply, add_mul, hca'],
    rw [hfc, ←hca], refl,
end

def is_linear_combination (a : α) (c : α →₀ α) (s : finset α) := c.support ⊆ s ∧ a = s.fold (+) 0 (λ x, c.to_fun x * x)

/-
lemma f_in_list {β : Type*} (hd : β) (tl : list β) : ∀ (f : β → β → β), (∀ a b, f a b = a ∨ f a b = b) → tl.foldl f hd ∈ (list.cons hd tl) :=
λ f hf, begin
    revert hd,
    induction tl, finish,
    intro hd,
    cases hf hd tl_hd; cases tl_ih hd;
    finish [h, tl_ih], 
end
-/

set_option pp.proofs true
lemma linear_combination' (s : finset α) :
∀ a ∈ span (↑s : set α), 
    ∃ c : α →₀ α, c.support ⊆ s ∧ a = s.fold (+) 0 (λ x, c.to_fun x * x) ∧ 
    (∀ c' : α →₀ α, (c'.support ⊆ s ∧ a = s.fold (+) 0 (λ x, c'.to_fun x * x)) → c'.support.card ≥ c.support.card) :=
λ a has, begin
    apply classical.by_contradiction,
    rw [not_exists],
    intro h,
    simp [not_and_distrib] at h,
    have h' :   ∀ (x : α →₀ α),
        (¬x.support ⊆ s) ∨
        (¬a = finset.fold has_add.add 0 (λ (x_1 : α), x.to_fun x_1 * x_1) s) ∨
        (∃ (c' : α →₀ α), is_linear_combination a c' s ∧ ¬ c'.support.card ≥ x.support.card),
        intro x,
        cases h x, finish,
        cases h_1, finish, 
        right, right, apply classical.by_contradiction, intro,
        apply h_1, intros c' hc' hac',
        simp [not_exists, not_and] at a_1, apply a_1 c' (and.intro hc' hac'),
    generalize haa : a = a',
    --cases linear_combination s a has with c₁ hc₁, rw haa at hc₁,
    let hc₁ := linear_combination s a has, rw haa at hc₁,
    have f : ∀ c : (α →₀ α),  is_linear_combination a' c s → 
        (∃ (c' : α →₀ α), is_linear_combination a' c' s 
            ∧ (¬c'.support.card ≥ c.support.card)), 
        --:= λ c hc, Exists.dcases_on ((or.rec (λ hx, )) )
        intros c hc,
        simp [is_linear_combination, haa] at *,
        cases h' c, apply absurd hc.left h_1,
        cases h_1, apply absurd hc.right h_1,
        cases h_1 with c' hc', apply exists.intro c', assumption, 

    let f'sub : ∀ c : α →₀ α, is_linear_combination a' c s → {c' : α →₀ α // is_linear_combination a' c' s}
        := λ c hc, let st := classical.indefinite_description _ (f c hc) 
                   in subtype.mk st.1 st.2.1,
    let hnf' : ℕ → (α →₀ α) := λ n, ((nat.rec_on n (classical.indefinite_description _ hc₁) (λ n cn, (f'sub cn.1 cn.2))) : {c : α →₀ α // is_linear_combination a' c s}).1,
    have h_hnf' : ∀ n, (hnf' n).support.card > (hnf' (n + 1)).support.card,
        intro n, 
        have is_linear : ∀ n, is_linear_combination a' (hnf' n) s,
            intro n', induction n',
            exact (classical.indefinite_description _ hc₁).2,
            exact (f'sub (hnf' n'_n) n'_ih).2,
        apply lt_of_not_ge,
        exact (classical.indefinite_description _ (f (hnf' n) (is_linear n))).2.2,            

    /-
        f : ℕ → (α →₀ α)
        ∀ x, (f x).support.card > (f (x + 1)).support.card,
                    generalize : 
                classical.indefinite_description (λ (c' : α →₀ α), is_linear_combination a' c' s)
                    (Exists.dcases_on (f c₁ hc₁) (λ c' hc', exists.intro c' hc'.left)) = c0,
    -/



/-
    have hs : ∃ sc : list (α →₀ α), sc ≠ [] ∧ ∀ c ∈ sc, (c : α →₀ α).support ⊆ s ∧ a = s.fold (+) 0 (λ x, c.to_fun x * x),
        cases linear_combination s a has with c hc,
        apply exists.intro [c], split, 
        simp, 
        intros c' hc', simp at hc', simp [hc'], assumption,
    rcases hs with ⟨sc, ⟨hsc₁, hsc₂⟩⟩,
    let f := (λ a b: α →₀ α, ite (b.support.card < a.support.card) b a),
    have hf : ∀ a b, f a b = a ∨ f a b = b,
        intros a b, by_cases b.support.card < a.support.card; simp [f]; simp [h],
    let c := sc.tail.foldl (λ a b: α →₀ α, ite (b.support.card < a.support.card) b a) sc.head,
    have hc : c ∈ sc,
        rw [←list.cons_head_tail hsc₁], apply f_in_list sc.head sc.tail f hf,    
    apply exists.intro c,
    split, exact (hsc₂ c hc).left, 
    split, exact (hsc₂ c hc).right,
    intros c' hc',-/
end

end ideal

namespace mv_polynomial
variables [comm_ring α] [decidable_eq σ] [decidable_eq α]

lemma monomial_linear_combination (s : finset (mv_polynomial σ α)) 
(hs₁ : s ≠ ∅) (hs₂ : ∀ p ∈ s, ∃ ps pa, monomial ps pa = p) :
∀ p ∈ ideal.span (↑s : set (mv_polynomial σ α)),  ∃ ps pa, pa ≠ 0 ∧ monomial ps pa = p 
    → ∃ c, ideal.is_linear_combination p c s ∧ 
        (∀ c', ideal.is_linear_combination p c' s → c'.support.card ≥ c.support.card) :=
begin

end

end mv_polynomial