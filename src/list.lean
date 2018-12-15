
universes u v


def fold' : Π {α : Type u}(C : list α → Sort v) 
    (l: list α), 
    C [] → 
    (Π (elem: α) (l₂: list α), elem ∈ l → l₂ ⊆ l → C l₂ → C (elem :: l₂)) → 
    C l
| α C [] d ih := d
| α C (x :: xs) d ih := 
    have xs.length < 1 + xs.length := by rw [add_comm]; constructor,
    ih x xs (by simp) (by simp) 
        (fold' C xs d (λ elem l₂ inxs inxs2 Cl2, 
            (ih elem l₂ (by right; assumption) 
                (list.subset_cons_of_subset _ inxs2) Cl2)))
using_well_founded {
    rel_tac :=
    λ _ _, `[exact ⟨_, measure_wf (λ k, list.length k.2.2.1)⟩],
    dec_tac := `[unfold has_well_founded.r inv_image measure, simp, assumption]   
}