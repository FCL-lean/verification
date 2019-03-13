section relation

inductive rtc {α : Sort*} (r : α → α → Prop) : α → α → Prop
| refl  : ∀ a, rtc a a
| base  : ∀ a b, r a b → rtc a b
| trans : ∀ a b c, rtc a b → rtc b c → rtc a c

end relation