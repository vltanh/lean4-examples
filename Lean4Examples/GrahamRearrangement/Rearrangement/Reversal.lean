import Lean4Examples.GrahamRearrangement.Rearrangement.Lemma55

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Order reversal for Lemma 5.6

This file makes explicit the "flipping the ordering" argument used by the paper
to deduce Lemma 5.6 from Lemma 5.5.
-/

noncomputable section

def reverseTuple {n D : ℕ} (x : Fin D → Fin n) :
    Fin D → Fin n :=
  fun i => reverseIndex n (x (reverseIndex D i))

def reversePermTuple {n D : ℕ}
    (π : Fin D → Equiv.Perm (Fin n)) :
    Fin D → Equiv.Perm (Fin n) :=
  fun i => reverseConjugate (π (reverseIndex D i))

theorem reverseTuple_strictMono {n D : ℕ}
    {x : Fin D → Fin n} (hx : StrictMono x) :
    StrictMono (reverseTuple x) := by
  intro i j hij
  have hji :
      (reverseIndex D j).val < (reverseIndex D i).val := by
    simp [reverseIndex_apply_val]
    omega
  have hx' :
      (x (reverseIndex D j)).val <
        (x (reverseIndex D i)).val := by
    simpa only [Fin.mk_lt_mk] using hx hji
  simp [reverseTuple, reverseIndex_apply_val]
  omega

theorem reverseTuple_head_to_tail {n D : ℕ}
    (b : Fin n) {x : Fin D → Fin n}
    (hx : x ∈ headTuples b D) :
    reverseTuple x ∈ tailTuples (reverseIndex n b) D := by
  rcases (Finset.mem_filter.1 hx).2 with ⟨hmono, hrange⟩
  apply Finset.mem_filter.2
  refine ⟨Finset.mem_univ _, reverseTuple_strictMono hmono, ?_⟩
  intro i
  have h := hrange (reverseIndex D i)
  rw [paperPos_reverseIndex]
  rw [paperPos_reverseIndex]
  omega

theorem reverse_indexInterval_image {n : ℕ}
    (a b : Fin n) (hab : a.val ≤ b.val) :
    (indexInterval a b).image (reverseIndex n) =
      indexInterval (reverseIndex n b) (reverseIndex n a) := by
  ext i
  constructor
  · intro hi
    rcases Finset.mem_image.1 hi with ⟨j, hj, rfl⟩
    have hj' := (Finset.mem_filter.1 hj).2
    apply Finset.mem_filter.2
    refine ⟨Finset.mem_univ _, ?_⟩
    simp [reverseIndex_apply_val]
    omega
  · intro hi
    have hi' := (Finset.mem_filter.1 hi).2
    refine Finset.mem_image.2
      ⟨reverseIndex n i, ?_, reverseIndex_involutive i⟩
    apply Finset.mem_filter.2
    refine ⟨Finset.mem_univ _, ?_⟩
    simp [reverseIndex_apply_val] at hi' ⊢
    omega

theorem reverse_indexedIntervalSum {n p : ℕ}
    (σ : Fin n → ZMod p) (a b : Fin n)
    (hab : a.val ≤ b.val) :
    indexedIntervalSum
        (applyPositionPerm σ (reverseIndex n)) a b =
      indexedIntervalSum σ
        (reverseIndex n b) (reverseIndex n a) := by
  rw [← indexSetSum_indexInterval, ← indexSetSum_indexInterval]
  rw [indexSetSum_applyPositionPerm_image]
  rw [reverse_indexInterval_image a b hab]

theorem reverse_composed_ordering {n p : ℕ}
    (σ : Fin n → ZMod p)
    (π ρ : Equiv.Perm (Fin n)) :
    applyPositionPerm
        (applyPositionPerm
          (applyPositionPerm σ (reverseIndex n)) π) ρ =
      applyPositionPerm
        (applyPositionPerm
          (applyPositionPerm σ (reverseConjugate π))
          (reverseConjugate ρ))
        (reverseIndex n) := by
  funext i
  simp [applyPositionPerm, reverseConjugate_apply,
    reverseIndex_involutive]

theorem reverse_constraint_zero {n p : ℕ}
    (σ : Fin n → ZMod p)
    (π ρ : Equiv.Perm (Fin n))
    (a b : Fin n) (hab : a.val ≤ b.val)
    (hzero :
      indexedIntervalSum
        (applyPositionPerm
          (applyPositionPerm
            (applyPositionPerm σ (reverseIndex n)) π) ρ)
        a b = 0) :
    indexedIntervalSum
      (applyPositionPerm
        (applyPositionPerm σ (reverseConjugate π))
        (reverseConjugate ρ))
      (reverseIndex n b) (reverseIndex n a) = 0 := by
  rw [reverse_composed_ordering σ π ρ] at hzero
  have h :=
    reverse_indexedIntervalSum
      (applyPositionPerm
        (applyPositionPerm σ (reverseConjugate π))
        (reverseConjugate ρ))
      a b hab
  rw [h] at hzero
  exact hzero

theorem reverse_window_bounds {n : ℕ}
    (b b' u : Fin n)
    (hu : paperPos b ≤ paperPos u ∧
      paperPos u ≤ paperPos b') :
    paperPos (reverseIndex n b') ≤
        paperPos (reverseIndex n u) ∧
      paperPos (reverseIndex n u) ≤
        paperPos (reverseIndex n b) := by
  simp [paperPos_reverseIndex]
  omega

theorem reverse_gap {n D : ℕ}
    (b b' : Fin n)
    (hgap : paperPos b' - paperPos b = 5 * D) :
    paperPos (reverseIndex n b) -
        paperPos (reverseIndex n b') = 5 * D := by
  simp [paperPos_reverseIndex]
  omega

theorem lemma56_reversal_subset {p D : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (b b' : Fin S.card)
    (hgap : paperPos b' - paperPos b = 5 * D)
    (u : Fin D → Fin S.card)
    (hu : ∀ i,
      paperPos b ≤ paperPos (u i) ∧
        paperPos (u i) ≤ paperPos b')
    (πi : Fin D → Equiv.Perm (Fin S.card))
    (σ : Fin S.card → ZMod p) :
    Lemma56Event
        (applyPositionPerm σ (reverseIndex S.card))
        b b' u πi →
      Lemma55Event σ
        (reverseIndex S.card b')
        (reverseIndex S.card b)
        (reverseTuple u)
        (reversePermTuple πi) := by
  intro h
  rcases h with ⟨x, hx, π, hπadm, hzero⟩
  let rx := reverseTuple x
  let rπ := reverseConjugate π
  refine ⟨rx, reverseTuple_head_to_tail b hx,
    rπ, Section5External.reverseConjugate_admissible π hπadm, ?_⟩
  intro i
  let j := reverseIndex D i
  have hxu :
      (x j).val ≤ (u j).val := by
    have hxhead := (Finset.mem_filter.1 hx).2.2 j
    have huj := (hu j).1
    simp [paperPos] at hxhead huj ⊢
    omega
  have hz := hzero j
  have hr :=
    reverse_constraint_zero σ π (πi j)
      (x j) (u j) hxu hz
  simpa [rx, reverseTuple, reversePermTuple, rπ, j,
    reverseIndex_involutive] using hr

theorem lemma56_mass_le_reversed {p D : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (b b' : Fin S.card)
    (hgap : paperPos b' - paperPos b = 5 * D)
    (u : Fin D → Fin S.card)
    (hu : ∀ i,
      paperPos b ≤ paperPos (u i) ∧
        paperPos (u i) ≤ paperPos b')
    (πi : Fin D → Equiv.Perm (Fin S.card)) :
    orderingEventMass S
        (fun σ => Lemma56Event σ b b' u πi) ≤
      orderingEventMass S
        (fun σ =>
          Lemma55Event σ
            (reverseIndex S.card b')
            (reverseIndex S.card b)
            (reverseTuple u)
            (reversePermTuple πi)) := by
  rw [Section5External.ordering_perm_invariant
    S (reverseIndex S.card)
    (fun σ => Lemma56Event σ b b' u πi)]
  apply uniformMass_mono
  intro σ h
  exact lemma56_reversal_subset S b b' hgap u hu πi σ h

theorem lemma56_event_empty_at_two {n p D : ℕ}
    (hD2 : 2 ≤ D) (b b' : Fin n)
    (hb : paperPos b = 2)
    (u : Fin D → Fin n)
    (πi : Fin D → Equiv.Perm (Fin n)) :
    ∀ σ, ¬ Lemma56Event σ b b' u πi := by
  intro σ h
  rcases h with ⟨x, hx, _π, _hπ, _hz⟩
  have hmono := (Finset.mem_filter.1 hx).2.1
  have hrange := (Finset.mem_filter.1 hx).2.2
  let i0 : Fin D := ⟨0, by omega⟩
  let i1 : Fin D := ⟨1, by omega⟩
  have hx0 := hrange i0
  have hx1 := hrange i1
  have hlt := hmono (show i0 < i1 by
    simp [i0, i1])
  simp [paperPos, hb, i0, i1] at hx0 hx1 hlt
  omega

end

end GrahamRearrangement
