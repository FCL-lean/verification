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

end finset