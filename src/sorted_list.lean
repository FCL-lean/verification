import data.list data.list.sort

namespace list
section sorted
variables {α : Type*} (r : α → α → Prop)

lemma sorted_tail {l : list α} (h : sorted r l) : sorted r l.tail := begin
    cases l; simp,
    exact sorted_of_sorted_cons h,
end 

lemma sorted_nodup_ext [is_antisymm _ r] :
∀ {l₁ l₂ : list α}, sorted r l₁ → sorted r l₂ → (nodup l₁) → (nodup l₂) 
    → (∀ a, a ∈ l₁ ↔ a ∈ l₂) → l₁ = l₂
|[] [] := by intros; refl
|[] (hd :: tl) := begin simp, intros _ _ _ _ h, apply h hd, simp, end
| (hd :: tl) [] := begin simp, intros _ _ _ _ h, apply h hd, simp, end
|(hd₁ :: tl₁) (hd₂ :: tl₂) := begin
    simp, intros hs₁ hs₁' hs₂ hs₂' hhd₁ nl₁ hhd₂ nl₂ h, 
    have h₁ := h hd₁, simp at h₁,
    have h₂ := h hd₂, simp at h₂,
    cases h₁; cases h₂,
    any_goals {
        try {apply and.intro h₁}, try {apply and.intro h₂}, try {apply and.intro h₂.symm}, 
        try {
            have h₃ := antisymm (hs₁ hd₂ h₂) (hs₂ hd₁ h₁),
            apply and.intro h₃,
            clear h₁ h₂, rename h₃ h₁,
        },
        apply sorted_nodup_ext hs₁' hs₂' nl₁ nl₂, 
        intro a, split,
    },
    all_goals {
        intro ha,
        have ha₁ : a ≠ hd₁, 
            intro hahd, rw hahd at ha, {rw h₁ at ha, exact hhd₂ ha} <|> {rw ←h₂ at ha, exact hhd₂ ha} <|> {exact hhd₁ ha},
        have ha₂ : a ≠ hd₂,
            intro hahd, rw hahd at ha, {rw h₂ at ha, exact hhd₁ ha} <|> {rw ←h₁ at ha, exact hhd₁ ha} <|> {exact hhd₂ ha},
        let ha' := h a, 
        simpa [ha₁, ha₂, ha] using ha',
    },
end

lemma sorted_filter (l : list α) (h : l.sorted r) (p : α → Prop) [decidable_pred p] : 
(l.filter p).sorted r := begin 
    induction l, simp,
    by_cases hp : p l_hd;
    simp [hp] at ⊢ h,
    refine ⟨λ b hb _, h.left b hb, l_ih h.right⟩,
    exact l_ih h.right,
end

@[simp] lemma merge_nil_left [decidable_rel r] (l : list α) : merge r [] l = l := by induction l; simp [merge]
@[simp] lemma merge_nil_right [decidable_rel r] (l : list α) : merge r l [] = l := by induction l; simp [merge]

@[simp] lemma mem_merge [decidable_rel r] : ∀ (l₁ l₂ : list α) (a), a ∈ merge r l₁ l₂ ↔ a ∈ l₁ ∨ a ∈ l₂ 
| [] _ := by simp
| _ [] := by simp
| (hd₁ :: tl₁) (hd₂ :: tl₂) := begin
    by_cases h : r hd₁ hd₂; simp [merge, h]; intro a; split; intro h';
    try {simp [mem_merge tl₁ (hd₂ :: tl₂)] at *}; try{simp [mem_merge (hd₁ :: tl₁) tl₂] at *},
    simp [or_assoc], assumption, 
    simp [or_assoc] at h', assumption, 
    simp [or_assoc], rw [or.left_comm, or_assoc] at h', assumption,
    simp [or_assoc (a = hd₁), @or.left_comm (a = hd₂)], rw [or_assoc] at h', assumption,
end

lemma sorted_of_sorted_erase_dup [decidable_eq α] (l : list α) (h : l.sorted r) : l.erase_dup.sorted r :=
begin
    induction l, simp,
    simp at h,
    by_cases hed : l_hd ∈ erase_dup l_tl,
    rw [erase_dup_cons_of_mem' hed], exact l_ih h.right,
    rw [erase_dup_cons_of_not_mem' hed], simp, exact ⟨h.left, l_ih h.right⟩,
end

end sorted

end list