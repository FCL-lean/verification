import data.finset
class finite (α : Sort*) :=
(val: finset α)
(is_finite: ∀ (x : α), x ∈ val)

namespace finite
variables [α : Type*] [decidable_eq α]
variable [fina: finite α]
lemma finite_fold_and: Π {P : α → Prop},
    fina.val.fold (∧) true P → Π (x : α), P x :=
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
    have in_val := fina.is_finite,
    exact m fina.val a x (in_val x),
end

lemma finite_fold_and': Π {P : α → Prop},
    (Π (x : α), P x) → fina.val.fold (∧) true P :=
begin
    intros P all,
    have m: (∀ (t : finset α), finset.fold and true P t),
    intro t, apply finset.induction_on t,
    simp,
    intros, simp,
    apply and.intro (all a) a_2,
    apply m,
end

lemma finite_fold_add_iff : Π {P : α → Prop},
    fina.val.fold (∧) true P ↔ Π (x : α), P x 
        := λ P, iff.intro (@finite_fold_and α _ _ P) 
                          (@finite_fold_and' α _ _ P)

end finite