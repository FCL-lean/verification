import data.finset
import data.finsupp
import util

namespace finset

namespace nat

/-
lemma max_le (a b : finset ℕ) : finset.sup a id ≤ finset.sup (a ∪ b) id :=
begin
    rw finset.sup_union,
    apply lattice.le_sup_left,
end
-/

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

/-
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
-/

end nat

section general
parameters {α : Type*}

@[simp] lemma coe_to_set {s : finset α} : s.to_set = ↑s := rfl

lemma ne_empty_iff_exists_mem {s : finset α} : s ≠ ∅ ↔ ∃ x, x ∈ s :=
begin
    simp [eq_empty_iff_forall_not_mem],
    apply @not_forall_not _ _ (classical.dec _),
end

lemma ne_empty_union [decidable_eq α] {s₁ s₂ : finset α} : ¬ (s₁ = ∅ ∧ s₂ = ∅) ↔ s₁ ∪ s₂ ≠ ∅ :=
⟨λ h, begin 
    by_cases h₁ : s₁ = ∅; by_cases h₂ : s₂ = ∅,
    apply absurd (and.intro h₁ h₂) h,
    any_goals {simp [h₁, h₂]},
    rw [←ne.def, ne_empty_iff_exists_mem] at *, finish,
end,
λ h h', begin
    simp [h'.left, h'.right] at h, assumption,
end⟩

lemma singleton_non_mem_inter_empty [decidable_eq α] {s₁ : finset α} {a : α}:
    a ∉ s₁ → s₁ ⊓ {a} = ∅ := sorry

lemma singleton_non_mem_inter_empty' [decidable_eq α] {s₁ : finset α} {a : α}:
    a ∉ s₁ → {a} ⊓ s₁ = ∅ := sorry

section min 
section decidable_linear_order
variables [decidable_linear_order α]

lemma lt_min'_not_mem (s : finset α) (hs : s ≠ ∅) : ∀ x < s.min' hs, x ∉ s :=
λ x h h', by apply absurd h (not_lt_of_le $ s.min'_le hs x h')

lemma union_min (s₁ s₂ : finset α) : (s₁ ∪ s₂).min = option.lift_or_get min (s₁.min) (s₂.min) :=
begin
    by_cases h₁ : s₁ = ∅; by_cases h₂ : s₂ = ∅,
    any_goals {
        try {simp [h₁, h₂, option.lift_or_get]}, 
        try {
            try {
                cases (finset.min_of_ne_empty h₂) with x₂ h₂', 
                simp at h₂', rw [h₂'],
            },
            try {
                cases (finset.min_of_ne_empty h₁) with x₁ h₁', 
                simp at h₁', rw [h₁'],
            }
        },
    }, all_goals {unfold option.lift_or_get},
    cases (finset.min_of_ne_empty (ne_empty_union.1 (not_and_of_not_left (s₂ = ∅) h₁))) with x h',
    simp at h', rw h', simp,
    rw [←option.mem_def] at *,
    unfold min,
    have h_m := mem_union.1 (mem_of_min h'),
    have h_m₁ := le_min_of_mem (mem_union.2 (or.inl (mem_of_min h₁'))) h',
    have h_m₂ := le_min_of_mem (mem_union.2 (or.inr (mem_of_min h₂'))) h',
    cases h_m,
    finish [antisymm h_m₁ (le_min_of_mem h_m h₁'), h_m₂],
    rw antisymm h_m₂ (le_min_of_mem h_m h₂') at *,  rw le_iff_lt_or_eq at h_m₁, 
    cases h_m₁, finish [not_le_of_lt h_m₁], finish,
end

lemma union_min' {s₁ s₂ : finset α} (hs₁ : s₁ ≠ ∅) (hs₂ : s₂ ≠ ∅) :
(s₁ ∪ s₂).min' (ne_empty_union.1 (not_and_of_not_left (s₂ = ∅) hs₁)) = min (s₁.min' hs₁) (s₂.min' hs₂) :=
begin
    have h := union_min s₁ s₂,
    have h₁ := min_of_ne_empty hs₁, cases h₁ with x₁ h₁,
    have h₂ := min_of_ne_empty hs₂, cases h₂ with x₂ h₂,
    have h₃ := min_of_ne_empty (ne_empty_union.1 (not_and_of_not_left (s₂ = ∅) hs₁)), cases h₃ with x₃ h₃,
    simp at h₁ h₂ h₃, simp [h₁, h₂, h₃, option.lift_or_get] at h,
    simp [min', option.get_of_mem _ h₁, option.get_of_mem _ h₂, option.get_of_mem _ h₃, h],
end

end decidable_linear_order
end min

section semilattice
variables [lattice.semilattice_sup_bot α]

lemma ne_empty_of_sup_ne_bot {s : finset α} : s.sup id ≠ ⊥ → s ≠ ∅ := λ h₀ h₁, by simp [h₁, sup_empty] at h₀; exact h₀

section decidable_eq
variables [decidable_eq α]

lemma max_le (a b : finset α) : finset.sup a id ≤ finset.sup (a ∪ b) id :=
begin
    rw finset.sup_union,
    apply lattice.le_sup_left,
end

lemma le_sup_id {b : α} {s : finset α} (hb : b ∈ s) : b ≤ s.sup id := finset.le_sup hb

end decidable_eq

section decidable_linear_order
variables [decidable_rel ((≤) : α → α → Prop)] [is_total α (≤)] [decidable_eq α]

instance : decidable_linear_order α := 
    { decidable_le := _inst_2,
      decidable_eq := _inst_4,
      le_total := is_total.total (≤),
    .. _inst_1 }

lemma mem_of_sup_id : ∀ {a : finset α}, a ≠ ∅ → a.sup id ∈ a
| a := finset.induction_on a (λ a, false.elim (a (refl _)))
    (λ x y notin ih notempty, begin 
        rw [finset.insert_eq, finset.sup_union, finset.mem_union, finset.sup_singleton],
        simp,
        from if h₁ : y = ∅ 
        then begin
            left,
            rw [h₁, finset.sup_empty, lattice.sup_bot_eq],
        end
        else begin
            from if h₂ : x < y.sup id
            then begin
                right, 
                rw [lattice.sup_of_le_right (le_of_lt h₂)],
                apply ih h₁,
            end
            else begin
                left,
                rw [lattice.sup_of_le_left (le_of_not_lt h₂)],
            end
        end
    end)

lemma empty_of_sup_id_not_mem : ∀ {a : finset α}, a.sup id ∉ a → a = ∅:=
λ a, by apply not_imp_comm.1 (@mem_of_sup_id _ _ _ _ _ a)

lemma sup_id_insert : Π (a : finset α) (b : α), a.sup id ∈ a
    → (insert b a).sup id ∈ insert b a :=
λ a b ha, begin
    rw [insert_eq, sup_union, mem_union],
    from if h : sup {b} id ≥ sup a id
    then begin
        left, simp [lattice.sup_of_le_left h], apply sup_singleton,
    end
    else begin
        right,
        letI : linear_order α := { le_total := is_total.total (≤), .. _inst_1 },
        simp [lattice.sup_of_le_right (le_of_not_le h)],
        apply mem_of_sup_id,
        from if h' : a = ∅ 
        then by rw h' at ha; cases ha
        else by assumption
    end
end

lemma sup_bot : Π (a : finset α), a.sup id = ⊥ → a = ∅ ∨ a = {⊥} :=
λ a, begin
    apply finset.induction_on a; intros,
    left, refl,
    right, simp at a_4, cases a_4,
    have h: s = ∅ ∨ s = {⊥}, from a_3 a_4_right,
    cases h; rw [a_4_left, h]; simp [insert_eq],
end

lemma union_sup_in_a_or_b : Π (a b : finset α),
    b ≠ ∅ →
    (a ∪ b).sup id ∈ a
    ∨ (a ∪ b).sup id ∈ b := 
λ a b bne, begin
    rw [sup_union],
    from if h₁ : a = ∅
    then begin
        right, simp [h₁, sup_empty], exact mem_of_sup_id bne,
    end
    else begin
        from if h : sup a id ≥ sup b id
        then begin 
            left, simp [lattice.sup_of_le_left h], exact mem_of_sup_id h₁,
        end
        else begin
            right, 
            letI : linear_order α := { le_total := is_total.total (≤), .. _inst_1 },
            simp [lattice.sup_of_le_right (le_of_not_le h)], exact mem_of_sup_id bne,
        end
    end
end



lemma sub_sup': Π (a b : finset α), 
    a.sup id ∈ b → a.sup id ≤ b.sup id :=
λ a b ha,
begin
    revert ha,
    apply finset.induction_on b; intros,
    cases ha,
    simp at ha, simp,
    cases ha, rw ha,
    simp,
    apply lattice.le_sup_right_of_le,
    exact a_3 ha,    
end

lemma sub_sup: Π {a b : finset α}, a ⊆ b → a.sup id ≤ b.sup id :=
λ a b asubb,
begin
    unfold has_subset.subset at asubb,
    by_cases a = ∅, rw h, simp,
    have sup_a_in_b := asubb (finset.mem_of_sup_id h),
    apply sub_sup' _ _ sup_a_in_b,
end

end decidable_linear_order
end semilattice


section sort

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

end sort

end general
section nat

/-
lemma union_sup_in_a_or_b : Π (a b : finset ℕ),
    b ≠ ∅ →
    (a ∪ b).sup id ∈ a
    ∨ (a ∪ b).sup id ∈ b
| a :=
begin
    apply finset.induction_on a,
    intros, right, simp,
    apply finset.mem_of_sup_id, assumption,
    intros c s notin ih b notemp,
    have iha := ih b notemp,
    cases iha;
    rw finset.insert_union;
    have m := finset.sup_id_insert (s ∪ b) c _,
    rw [←finset.mem_union, finset.insert_union], assumption,
    rw [finset.mem_union], left, assumption,
    rw [←finset.mem_union, finset.insert_union], assumption,
    rw [finset.mem_union], right, assumption,
end
-/

end nat

end finset