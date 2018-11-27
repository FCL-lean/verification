import data.list.basic
inductive lex : list ℕ → list ℕ → Prop
| nil {a} : lex [a] [nat.succ a]
| cons {a l₁ l₂} (h : lex l₁ l₂) : lex (a :: l₁) (a :: l₂)
| cons' {a a₁ l₁ l₂} (h : lex (a :: l₁) (a₁ :: l₂)) 
            : lex (a :: l₁) (nat.succ a₁ :: l₂)
| cons'' {a : ℕ}{l₁ l₂: list ℕ} : l₁.length = l₂.length 
            → lex (a :: l₁) (nat.succ a :: l₂)

def list_h (a : list ℕ) : ℕ :=
match a with
| [] := nat.zero
| (x :: xs) := x
end

def lex_length : ∀ a b, lex a b → a.length = b.length
| a b l := begin end

def lex_trans : ∀ a b c, lex a b → lex b c → lex a c
| a b c le1 (@lex.nil a') 
    := begin 
            have l := lex_length a [a'] le1, simp at *, 
            rw list.length_eq_one at l, 
            cases l, rw l_h at *,
            apply lex.cons'; assumption,
        end
| a b c le1 (@lex.cons a' l1 l2 h) :=
begin
    
end
| list.nil b c le1 (@lex.cons' a' b' l1 l2 h) := by cases le1
| (list.cons _ a) b c le1 (@lex.cons' a' b' l1 l2 h) :=
    lex.cons' (lex_trans _ _ _ le1 h)
| a b c le1 (@lex.cons'' a' l1 l2 p) :=
begin

end


def lex_acc_aux: (Σ' a b: list ℕ, lex a b) → ℕ × ℕ
| ⟨a, b, c⟩ := ⟨b.length, list_h b⟩

lemma lex_acc: Π (a b: list ℕ), lex a b → acc lex a
| [a] [.(nat.succ a)] lex.nil 
    :=  let n := @prod.lex.right ℕ ℕ (nat.lt) (nat.lt)
                        [nat.succ a].length a
                            (nat.succ a) (nat.less_than_or_equal.refl _)
        in acc.intro _ (λ y le, lex_acc y [a] le)
| (a :: as) (.(a) :: bs) (lex.cons h) 
    := 
        let n := @prod.lex.left ℕ ℕ (nat.lt) (nat.lt) bs.length 
                        (list_h bs) (a :: bs).length a
                        (nat.less_than_or_equal.refl _)
        in acc.intro _ (λ y le, lex_acc y bs (begin end))
| (a :: as) ((nat.succ b) :: bs) (lex.cons' h) 
    :=
        let n := @prod.lex.right ℕ ℕ (nat.lt) (nat.lt)
                        (nat.succ b :: bs).length b
                            (nat.succ b) (nat.less_than_or_equal.refl _)
        in acc.intro _ (λ y le, lex_acc y (b :: bs) (begin end))
| (a :: as) (.(nat.succ a) :: bs) (lex.cons'' p)
    :=  let n := @prod.lex.right ℕ ℕ (nat.lt) (nat.lt)
                        (nat.succ a :: bs).length a
                            (nat.succ a) (nat.less_than_or_equal.refl _)
        in begin 
            simp at n, 
            let n' := @eq.subst _ (λ x, prod.lex nat.lt nat.lt (1 + x, a) 
                                   (1 + list.length bs, nat.succ a)) _ _ 
                                    (eq.symm p) n,
            exact acc.intro _ (λ y le, lex_acc y (a :: as) le) end
using_well_founded 
{ rel_tac := λ _ _, `[exact ⟨inv_image (prod.lex (<) (<)) lex_acc_aux, 
                                    @inv_image.wf _ _ _ lex_acc_aux 
                                   (prod.lex_wf nat.lt_wf nat.lt_wf)⟩] 
, dec_tac := `[simp, unfold inv_image, try {assumption}, 
                try {simp at *, unfold lex_acc_aux list_h, simp, assumption} ] }

lemma lex_well_founded: well_founded lex
    := well_founded.intro (λ x, acc.intro _ (λ y le, lex_acc y x le))