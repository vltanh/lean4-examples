import Lean4Examples.GrahamRearrangement.Rearrangement.Lemma55

open scoped BigOperators Pointwise

namespace GrahamRearrangement.Section5External

/-!
# Generic reversal transport for Lemma 5.6

This module contains only the order-reversal bookkeeping: reversing the finite
index interval converts a left-tail constraint into the right-tail constraint
used in Lemma 5.5, while preserving uniform orderings and local admissibility.
-/

noncomputable section

axiom lemma56_reversal_data
    {p D : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (b b' : Fin S.card)
    (hb2 : 2 ≤ paperPos b)
    (hb' : paperPos b' ≤ S.card - 2)
    (hgap : paperPos b' - paperPos b = 5 * D)
    (u : Fin D → Fin S.card)
    (hu : ∀ i,
      paperPos b ≤ paperPos (u i) ∧
        paperPos (u i) ≤ paperPos b')
    (πi : Fin D → Equiv.Perm (Fin S.card))
    (hfix : ∀ i, FixedOutside b b' (πi i)) :
    ∃ rb rb' : Fin S.card,
      ∃ ru : Fin D → Fin S.card,
      ∃ rπi : Fin D → Equiv.Perm (Fin S.card),
        2 ≤ paperPos rb ∧
        paperPos rb' ≤ S.card - 2 ∧
        paperPos rb' - paperPos rb = 5 * D ∧
        (∀ i,
          paperPos rb ≤ paperPos (ru i) ∧
            paperPos (ru i) ≤ paperPos rb') ∧
        (∀ i, FixedOutside rb rb' (rπi i)) ∧
        orderingEventMass S
          (fun σ => Lemma56Event σ b b' u πi) =
        orderingEventMass S
          (fun σ => Lemma55Event σ rb rb' ru rπi)

end

end GrahamRearrangement.Section5External
