import data.finset
import data.fintype

namespace fintype
variables [α : Type*] [decidable_eq α]
variable [fina: fintype α]
lemma fintype_fold_and: Π {P : α → Prop},
    fina.elems.fold (∧) true P → Π (x : α), P x :=
begin
    have m: (∀ {P : α → Prop} (t : finset α), finset.fold and true P t →
                ∀ x ∈ t, P x),
    intros P t,
    apply finset.induction_on t,
    intros, cases H,
    intros, simp at *,
    cases H; cases a_3,
    rw H at *, assumption,
    apply a_2; assumption,
    intros,
    have in_elems := fina.complete,
    exact m fina.elems a x (in_elems x),
end

lemma fintype_fold_and': Π {P : α → Prop},
    (Π (x : α), P x) → fina.elems.fold (∧) true P :=
begin
    intros P all,
    have m: (∀ (t : finset α), finset.fold and true P t),
    intro t, apply finset.induction_on t,
    simp,
    intros, simp,
    apply and.intro (all a) a_2,
    apply m,
end

lemma fintype_fold_and_iff : Π {P : α → Prop},
    fina.elems.fold (∧) true P ↔ Π (x : α), P x 
        := λ P, iff.intro (@fintype_fold_and α _ _ P) 
                          (@fintype_fold_and' α _ _ P)

def fintype_fold_dec : Π {P : α → Prop}, (∀ x : α, decidable (P x))
    → decidable (fina.elems.fold (∧) true P) :=
λ P, begin
    rw fintype_fold_and_iff,
    introI,
    apply decidable_of_iff (∀ a ∈ fina.elems, P a),
    apply iff.intro; intros,
    begin
        apply a_1, apply fina.complete,
    end,
    begin
        apply a_1,
    end,
end

end fintype