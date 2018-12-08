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

end finite