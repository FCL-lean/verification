section relation

inductive rtc {α : Sort*} (r : α → α → Prop) : α → α → Prop
| refl  : ∀ a, rtc a a
| base  : ∀ a b, r a b → rtc a b
| trans : ∀ a b c, rtc a b → rtc b c → rtc a c

section
variables {α : Sort*} {r : α → α → Prop} {a b c : α} 
lemma rtc.refl' : rtc r a a := rtc.refl _ _

lemma rtc.base' (h : r a b) : rtc r a b := rtc.base _ _ h

lemma rtc.trans' (h₁ : rtc r a b) (h₂ : rtc r b c) : rtc r a c := rtc.trans _ _ _ h₁ h₂

lemma rtc.base_trans (h₁ : r a b) (h₂ : rtc r b c) : rtc r a c :=
rtc.trans _ _ _ (rtc.base _ _ h₁) h₂

lemma rtc.trans_base (h₁ : rtc r a b) (h₂ : r b c) : rtc r a c :=
rtc.trans _ _ _ h₁ (rtc.base _ _ h₂)
end

end relation