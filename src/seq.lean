import util

universe u

section seq
variable (α : Type u)
variable (R : α → α → Prop)

def seq : Type u := ℕ → α

def seq_R := { f : seq α // ∀ n, R (f n) (f (n + 1))}


def no_inf_chain : Prop := ¬' seq_R α R

end seq

variable (α : Type u)
variable (R : α → α → Prop)

lemma no_inf_chain_wf : no_inf_chain α R ↔ well_founded R := sorry