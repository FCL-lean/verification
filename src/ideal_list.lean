import data.list
import ring_theory.ideals

namespace list
section ideal
variables {α : Type*} [comm_ring α] [decidable_eq α]

def to_ideal (l : list α) : ideal α := ideal.span ↑l.to_finset

end ideal
end list