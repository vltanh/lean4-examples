import Lean4Examples.GrahamRearrangement.Rearrangement.Lemma53

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Deterministic Section 5 repair

This is the greedy descending-endpoint part of the proof of Theorem 1.2.
-/

noncomputable section

theorem applyPositionPerm_isIndexedOrdering
    {p : ℕ} {S : Finset (ZMod p)}
    {σ : Fin S.card → ZMod p}
    (hσ : IsIndexedOrdering S σ)
    (π : Equiv.Perm (Fin S.card)) :
    IsIndexedOrdering S (applyPositionPerm σ π) := by
  constructor
  · intro i j hij
    apply π.injective
    apply hσ.1
    exact hij
  · intro x
    rw [hσ.2]
    constructor
    · rintro ⟨j, hj⟩
      refine ⟨π.symm j, ?_⟩
      simpa [applyPositionPerm] using hj
    · rintro ⟨i, hi⟩
      refine ⟨π i, ?_⟩
      simpa [applyPositionPerm] using hi

theorem not_badEvent1_far
    {n p D : ℕ} {σ : Fin n → ZMod p}
    (h1 : ¬ BadEvent1 D σ) :
    ∀ b ∈ badRightEndpoints σ,
      paperPos b + 5 * D ≤ n := by
  intro b hb
  by_contra h
  have hlate : n ≤ paperPos b + 30 * D := by omega
  exact h1 ⟨b, hb, hlate⟩

theorem not_badEvent2_local
    {n p D : ℕ} {σ : Fin n → ZMod p}
    (h2 : ¬ BadEvent2 D σ) :
    ∀ z : Fin n,
      ((badRightEndpoints σ) ∩
        symmetricWindow z (10 * D)).card ≤ D := by
  intro z
  by_contra h
  have hgt :
      D < ((badRightEndpoints σ) ∩
        symmetricWindow z (10 * D)).card := by omega
  exact h2 ⟨z, hgt⟩

theorem not_badEvent3_blocked
    {n p D : ℕ} {σ : Fin n → ZMod p}
    (h3 : ¬ BadEvent3 D σ) :
    ∀ b ∈ badRightEndpoints σ,
      ∀ π : Equiv.Perm (Fin n),
        IsAdmissiblePermutation D π →
        FixedBelow b π →
        (blockedCandidates D σ b π).card < 2 * D := by
  intro b hb π hπ hfix
  by_contra h
  have hge :
      2 * D ≤ (blockedCandidates D σ b π).card := by omega
  exact h3 ⟨b, hb, π, hπ, hfix, hge⟩

/-- The deterministic local-repair step from the proof of Theorem 1.2. -/
theorem section5_local_repair
    {n p D : ℕ} (hD : 0 < D)
    (σ : Fin n → ZMod p)
    (hgood : Section5Good D σ) :
    ∃ π : Equiv.Perm (Fin n),
      IsAdmissiblePermutation D π ∧
      HasNoZeroPaperSegments
        (applyPositionPerm σ π) := by
  let B := badRightEndpoints σ
  have hfar :
      ∀ b ∈ B, paperPos b + 5 * D ≤ n :=
    not_badEvent1_far hgood.1
  have hlocal :
      ∀ z : Fin n,
        (B ∩ symmetricWindow z (10 * D)).card ≤ D :=
    not_badEvent2_local hgood.2.1
  have hblocked :
      ∀ b ∈ B, ∀ π : Equiv.Perm (Fin n),
        IsAdmissiblePermutation D π →
        FixedBelow b π →
        (blockedCandidates D σ b π).card < 2 * D :=
    not_badEvent3_blocked hgood.2.2
  apply Section5External.finite_descending_greedy_repair
    hD σ B rfl hfar hlocal hblocked
  intro b y π hb hπ hthrough hy hnot
  trivial

end

end GrahamRearrangement
