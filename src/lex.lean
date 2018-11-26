inductive lex : list ℕ → list ℕ → Prop
| nil {} {a l} : lex [] (a :: l)
| cons {a l₁ l₂} (h : lex l₁ l₂) : lex (a :: l₁) (a :: l₂)
| rel {a₁ l₁ a₂ l₂} (h : a₁ < a₂) : lex (a₁ :: l₁) (a₂ :: l₂)

lemma lex_acc_aux: Π (a b: list ℕ) (m: ℕ), lex a (m :: b) → acc lex a
| [] b m lex.nil := acc.intro _ (λ y le, by cases le)
| (.(m) :: b2) b m (lex.cons h) := acc.intro _ (λ y le, lex_acc_aux y b2 m le)
| (a :: b1) b m (lex.rel h) := acc.intro _ (λ y le, lex_acc_aux y b1 a le)

lemma lex_acc: Π (a b: list ℕ), lex a b → acc lex a
| [] (a :: as) lex.nil := acc.intro _ (λ y le, by cases le)
| (a :: as) (.(a) :: bs) (lex.cons h) := acc.intro _ (λ y le, lex_acc_aux y as a le)
| (a :: as) (.(a) :: bs) (lex.rel h) := acc.intro _ (λ y le, lex_acc_aux y as a le)


lemma lex_well_founded: well_founded lex
    := well_founded.intro (λ x, acc.intro _ (λ y le, lex_acc y x le))