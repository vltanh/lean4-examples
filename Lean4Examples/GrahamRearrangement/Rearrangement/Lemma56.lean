import Lean4Examples.GrahamRearrangement.Rearrangement.ReversalExternal

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Lemma 5.6

The left-tail counterpart of Lemma 5.5, obtained by reversing the finite ordering.
-/

noncomputable section

/-- Lemma 5.6. -/
theorem lemma5_6
    {α : ℝ} (hα0 : 0 < α) (hαh : α < 1 / 2)
    (P : Section5Parameters α)
    {p : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hreg : Section5Regime P p S)
    (b b' : Fin S.card)
    (hb2 : 2 ≤ paperPos b)
    (hb' : paperPos b' ≤ S.card - 2)
    (hgap : paperPos b' - paperPos b = 5 * P.D)
    (u : Fin P.D → Fin S.card)
    (hu : ∀ i,
      paperPos b ≤ paperPos (u i) ∧
        paperPos (u i) ≤ paperPos b')
    (πi : Fin P.D → Equiv.Perm (Fin S.card))
    (hfix : ∀ i, FixedOutside b b' (πi i)) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    orderingEventMass S
      (fun σ => Lemma56Event σ b b' u πi) ≤
        1 / (S.card : ℝ) ^ 2 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨rb, rb', ru, rπi,
      hrb2, hrb', hrgap, hru, hrfix, hmass⟩ :=
    Section5External.lemma56_reversal_data
      S b b' hb2 hb' hgap u hu πi hfix
  rw [hmass]
  exact lemma5_5 hα0 hαh P hp S hreg
    rb rb' hrb2 hrb' hrgap ru hru rπi hrfix

end

end GrahamRearrangement
