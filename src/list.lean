
universes u v


def fold' : Π {α : Type u}(C : list α → Sort v) 
    (l: list α), 
    C [] → 
    (Π (elem: α) (l₂: list α), elem ∈ l → l₂ ⊆ l → C l₂ → C (elem :: l₂)) → 
    C l
| α C [] := λ d ih, d
| α C (x :: xs) := λ d ih,
    ih x xs (by simp) (by simp) 
        (fold' C xs d (λ elem l₂ inxs inxs2 Cl2, 
            (ih elem l₂ (by right; assumption) 
                (list.subset_cons_of_subset _ inxs2) Cl2)))
