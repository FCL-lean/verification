import data.stream
import util

universe u
namespace seqR
section seq



def seq (α : Type u): Type u := ℕ → α

def seq_cons {α : Type u}: α → seq α → seq α
| elem seq nat.zero := elem
| elem seq (nat.succ n) := seq n


def seq_R (α : Type u) (R : α → α → Prop) := { f : stream α // ∀ n, R (f n) (f (n + 1))}

variable {α : Type u}
variable {R : α → α → Prop}

def seq_R_cons : Π (elem: α) (f : seq_R α R), R elem (f.1 0) → seq_R α R 
    := λ elem f r, ⟨seq_cons elem f.1, λ n, begin cases n, assumption, exact f.2 n, end⟩



def seq_R_s (elem : α) (R : α → α → Prop) : Type u := { f : seq_R α R // f.1 0 = elem }


def head (s: seq_R α R): α := s.1 0

def tail (s: seq_R α R): seq_R α R :=
    ⟨s.1.tail, λ n, s.2 (n + 1)⟩ 

protected def coinduction : 
    ∀ {s₁ s₂: seq_R α R}, head s₁ = head s₂ → 
        (∀ (β : Type u) (fr: seq_R α R → β), fr (tail s₁) = fr (tail s₂)) → s₁ = s₂
| ⟨f₁, p₁⟩ ⟨f₂, p₂⟩ he ft 
    := subtype.eq (stream.coinduction he (λ β tp eqt, (ft β (λ s, tp s.1))))

@[simp]
def nth (s: seq_R α R) (n: ℕ): α := s.1 n


def no_inf_chain (α: Type*) (R: α → α → Prop): Prop := ¬' seq_R α R

end seq

variable (α : Type u)
variable (R : α → α → Prop)


lemma no_inf_chain_wf : no_inf_chain α R → well_founded R := sorry

end seqR