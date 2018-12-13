import ring_theory.ideals

class noetherian (α : Type*) [comm_ring α] :=
(fin_ideal : ∀ i : ideal α, ∃ (s : finset α), ideal.span ↑s = i)

namespace noetherian




end noetherian