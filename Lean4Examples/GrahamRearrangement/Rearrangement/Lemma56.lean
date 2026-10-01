import Lean4Examples.GrahamRearrangement.Rearrangement.Reversal

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
  have hD7 : 7 ≤ P.D := by
    rw [P.D_eq]
    exact section5D_ge_seven hα0 hαh
  by_cases hbEq : paperPos b = 2
  · have hempty :=
      lemma56_event_empty_at_two
        (n := S.card) (p := p) (D := P.D)
        (by omega) b b' hbEq u πi
    have hzeroMass :
        orderingEventMass S
          (fun σ => Lemma56Event σ b b' u πi) = 0 := by
      unfold orderingEventMass
      apply uniformMass_empty_of_forall_not
      intro σ
      exact hempty σ
    rw [hzeroMass]
    positivity
  · have hb3 : 3 ≤ paperPos b := by omega
    let rb : Fin S.card := reverseIndex S.card b'
    let rb' : Fin S.card := reverseIndex S.card b
    let ru : Fin P.D → Fin S.card := reverseTuple u
    let rπi : Fin P.D → Equiv.Perm (Fin S.card) :=
      reversePermTuple πi
    have hrb2 : 2 ≤ paperPos rb := by
      dsimp [rb]
      rw [paperPos_reverseIndex]
      omega
    have hrb' : paperPos rb' ≤ S.card - 2 := by
      dsimp [rb']
      rw [paperPos_reverseIndex]
      omega
    have hrgap : paperPos rb' - paperPos rb = 5 * P.D := by
      dsimp [rb, rb']
      exact reverse_gap b b' hgap
    have hru :
        ∀ i,
          paperPos rb ≤ paperPos (ru i) ∧
            paperPos (ru i) ≤ paperPos rb' := by
      intro i
      dsimp [rb, rb', ru, reverseTuple]
      exact reverse_window_bounds b b' (u (reverseIndex P.D i))
        (hu (reverseIndex P.D i))
    have hrfix :
        ∀ i, FixedOutside rb rb' (rπi i) := by
      intro i
      dsimp [rb, rb', rπi, reversePermTuple]
      exact Section5External.reverseConjugate_fixedOutside
        b b' (πi (reverseIndex P.D i))
        (hfix (reverseIndex P.D i))
    have hmass :=
      lemma56_mass_le_reversed S b b' hgap u hu πi
    exact le_trans hmass
      (lemma5_5 hα0 hαh P hp S hreg
        rb rb' hrb2 hrb' hrgap ru hru rπi hrfix)

end

end GrahamRearrangement
