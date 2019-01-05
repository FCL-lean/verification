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
    let hc₁ := linear_combination s a has, rw haa at hc₁,
    have f : ∀ c : (α →₀ α),  is_linear_combination a' c s → 
        (∃ (c' : α →₀ α), is_linear_combination a' c' s 
            ∧ (¬c'.support.card ≥ c.support.card)), 
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
    have hnf'_gt_of_lt : ∀ {n m}, n < m → (hnf' n).support.card > (hnf' m).support.card,
        intros n m hnm, rw ←nat.add_sub_of_le (nat.succ_le_of_lt hnm),
        induction (m - (n + 1)), apply h_hnf',
        rw nat.add_succ (n + 1) n_1,
        apply gt_trans ih (h_hnf' ((n + 1) + n_1)),
    have hnf'_ge_of_le : ∀ {n m}, n ≤ m → (hnf' n).support.card ≥ (hnf' m).support.card,
        intros n m hnm, rw le_iff_eq_or_lt at hnm, cases hnm, finish, apply le_of_lt (hnf'_gt_of_lt hnm),
    have lt_of_hnf'_gt : ∀ {n m}, (hnf' n).support.card > (hnf' m).support.card → n < m,
        intros n m h_nm, apply lt_of_not_ge, intro h_nm',
        apply absurd h_nm (not_lt_of_le (hnf'_ge_of_le  h_nm')),
    have le_of_hnf'_ge : ∀ {n m}, (hnf' n).support.card ≥ (hnf' m).support.card → n ≤ m,
        intros n m h_nm, apply le_of_not_lt, intro hnm,
        apply absurd h_nm (not_le_of_lt (hnf'_gt_of_lt hnm)),

    have inj_hnf' : function.injective (λ n, (hnf' n).support.card),
        unfold function.injective, intros a₁ a₂ ha₁₂,
        apply antisymm (le_of_hnf'_ge (ge_of_eq ha₁₂)) (le_of_hnf'_ge (le_of_eq ha₁₂)),
    have inf_chain : nonempty (((>) : ℕ → ℕ → Prop) ≼o ((<) : ℕ → ℕ → Prop)),
        constructor,
        apply order_embedding.mk (function.embedding.mk (λ n, (hnf' n).support.card) inj_hnf'),
        intros a b, simp, split, apply hnf'_gt_of_lt,
        apply lt_of_hnf'_gt,
    apply (order_embedding.well_founded_iff_no_descending_seq.1 nat.lt_wf) inf_chain,
end

end ideal