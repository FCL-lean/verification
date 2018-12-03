import data.finset
import util

namespace finset

lemma sup_max : Π (a : finset ℕ), a ≠ ∅ → some (a.sup id) = a.max
| a :=
begin
    apply finset.induction_on a,
    intros, apply false.elim, apply a_1; trivial,
    intros, intros, by_cases (s = ∅),
    rw h, simp, unfold option.lift_or_get,
    let ih := a_3 h, simp, rw ←ih, unfold option.lift_or_get,
    constructor, 
end

lemma sup_id_insert : Π (a : finset ℕ) (b : ℕ), a.sup id ∈ a
    → (insert b a).sup id ∈ insert b a :=
begin
    intros,
    apply finset.induction_on a,
    simp,
    intros,
    rw finset.insert.comm,
    rw finset.sup_insert,
    unfold id,
    have h := nat.sup_ab_eq_a_or_b a_2 (finset.sup (insert b s) id),
    cases h; rw h,
    simp, apply finset.mem_insert_of_mem, assumption
end

lemma mem_of_sup_id : Π (a : finset ℕ), a ≠ ∅ → a.sup id ∈ a
| a' := finset.induction_on a' (λ a, false.elim (a (refl _)))
    (λ a b notin ih notempty, 
        dite (b = ∅) (λ emp, begin rw emp, simp, end) 
            (λ not_emp, sup_id_insert _ _ (ih not_emp)))

lemma union_sup_in_a_or_b : Π (a b : finset ℕ),
    b ≠ ∅ →
    (a ∪ b).sup id ∈ a
    ∨ (a ∪ b).sup id ∈ b
| a :=
begin
    apply finset.induction_on a,
    intros, right, simp,
    apply mem_of_sup_id, assumption,
    intros c s notin ih b notemp,
    have iha := ih b notemp,
    cases iha;
    rw finset.insert_union;
    have m := sup_id_insert (s ∪ b) c _,
    rw [←finset.mem_union, finset.insert_union], assumption,
    rw [finset.mem_union], left, assumption,
    rw [←finset.mem_union, finset.insert_union], assumption,
    rw [finset.mem_union], right, assumption,
end

section 
parameters {α : Type*}

lemma ne_empty_iff_exists_mem {s : finset α} : s ≠ ∅ ↔ ∃ x, x ∈ s :=
begin
    simp [eq_empty_iff_forall_not_mem],
    apply @not_forall_not _ _ (classical.dec _),
end

end

variables {α : Type*}
variables [decidable_eq α]
variables (r : α → α → Prop) [decidable_rel r] [is_trans α r] [is_antisymm α r] [is_total α r]

lemma sort_nil : sort r ∅ = [] := by apply quot.lift_beta id; intros; assumption

lemma sort_empty_nil {s : finset α} : sort r s = [] ↔ s = ∅ :=
begin
    apply iff.intro; intro h,
    from if hs : s = ∅ 
    then by assumption
    else begin      
        rw [←ne.def, ne_empty_iff_exists_mem] at hs,
        cases hs, rw [←finset.mem_sort r, h] at hs_h,
        cases hs_h,
    end,
    rw h, apply sort_nil,
end

lemma sort_ne_empty_ne_nil {s : finset α} : s ≠ ∅ → sort r s ≠ [] :=
λ hs hss, begin
    rw sort_empty_nil at hss,
    apply absurd hss hs,
end

end finset