import Lean4Examples.GrahamRearrangement.Rearrangement.Lemma56

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Lemma 5.3

The blocked-choice event is split into the right-extending event E₁ and the
left-extending event E₂, bounded by Lemmas 5.5 and 5.6 respectively.
-/

noncomputable section

theorem swap_fixedOutside
    {n : ℕ} (b b' y : Fin n)
    (hby : paperPos b < paperPos y)
    (hyb' : paperPos y ≤ paperPos b') :
    FixedOutside b b' (Equiv.swap b y) := by
  intro i hi
  have hib : i ≠ b := by
    intro h
    subst h
    rcases hi with h | h <;> omega
  have hiy : i ≠ y := by
    intro h
    subst h
    rcases hi with h | h <;> omega
  exact Equiv.swap_apply_of_ne_of_ne hib hiy

theorem badEvent3_core_side_reduction
    {n p D : ℕ} (hD : 0 < D)
    (σ : Fin n → ZMod p)
    (h3 : BadEvent3 D σ)
    (h0 : ¬ BadEvent0 D σ)
    (h1 : ¬ BadEvent1 D σ) :
    RightRepairEvent D σ ∨ LeftRepairEvent D σ := by
  classical
  rcases h3 with ⟨b, hb, π, hπadm, hπfix, hblocked⟩
  have hbfar : paperPos b + 30 * D ≤ n := by
    by_contra h
    exact h1 ⟨b, hb, by omega⟩
  have hb2 : 2 ≤ paperPos b := by
    exact le_trans (by norm_num) (badRightEndpoint_ge_three hb)
  have hlocal :=
    Section5External.local_nonzero_after_admissible
      σ b hb hbfar h0 π hπadm hπfix
  rcases Section5External.blocked_family_split
      hD σ b π hlocal hblocked with
    hright | hleft
  · rcases hright with ⟨y, s, t, hyinj, htinj, hw⟩
    obtain ⟨ρ, htmono⟩ :=
      Section5External.exists_sorting_perm t htinj
    let y' : Fin D → Fin n := y ∘ ρ
    let s' : Fin D → Fin n := s ∘ ρ
    let t' : Fin D → Fin n := t ∘ ρ
    have hb'lt : b.val + 5 * D < n := by
      simp [paperPos] at hbfar
      omega
    let b' : Fin n := ⟨b.val + 5 * D, hb'lt⟩
    have hgap : paperPos b' - paperPos b = 5 * D := by
      simp [paperPos, b']
    have hywin :
        ∀ i,
          paperPos b < paperPos (y' i) ∧
            paperPos (y' i) ≤ paperPos b' := by
      intro i
      have h := hw (ρ i)
      simpa [y', b', paperPos] using ⟨h.1, h.2.1⟩
    have hswin :
        ∀ i,
          paperPos b < paperPos (s' i) ∧
            paperPos (s' i) ≤ paperPos b' := by
      intro i
      have h := hw (ρ i)
      simpa [s', b', paperPos] using ⟨h.2.2.1, h.2.2.2.1⟩
    have htTail : t' ∈ tailTuples b' D := by
      simp only [tailTuples, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact htmono
      · intro i
        have h := hw (ρ i)
        simpa [t', b', paperPos] using h.2.2.2.2.1
    have hzero :
        ∀ i,
          indexedIntervalSum
            (applyPositionPerm
              (applyPositionPerm σ π)
              (Equiv.swap b (y' i)))
            (s' i) (t' i) = 0 := by
      intro i
      simpa [y', s', t'] using (hw (ρ i)).2.2.2.2.2
    refine Or.inl ⟨b, b', hb2, hbfar, hgap, y', s',
      hywin, hswin, ?_⟩
    exact ⟨t', htTail, π, hπadm, hzero⟩
  · rcases hleft with ⟨y, s, t, hyinj, hsinj, hw⟩
    obtain ⟨ρ, hsmono⟩ :=
      Section5External.exists_sorting_perm s hsinj
    let y' : Fin D → Fin n := y ∘ ρ
    let s' : Fin D → Fin n := s ∘ ρ
    let t' : Fin D → Fin n := t ∘ ρ
    have hb'lt : b.val + 5 * D < n := by
      simp [paperPos] at hbfar
      omega
    let b' : Fin n := ⟨b.val + 5 * D, hb'lt⟩
    have hgap : paperPos b' - paperPos b = 5 * D := by
      simp [paperPos, b']
    have hywin :
        ∀ i,
          paperPos b < paperPos (y' i) ∧
            paperPos (y' i) ≤ paperPos b' := by
      intro i
      have h := hw (ρ i)
      simpa [y', b', paperPos] using ⟨h.1, h.2.1⟩
    have htwin :
        ∀ i,
          paperPos b ≤ paperPos (t' i) ∧
            paperPos (t' i) < paperPos b' := by
      intro i
      have h := hw (ρ i)
      have hlt : paperPos (t (ρ i)) < paperPos b' := by
        have hty := h.2.2.2.2.1
        have hyb := h.2.1
        simpa [b', paperPos] using lt_of_lt_of_le hty hyb
      exact ⟨h.2.2.2.1, by simpa [t'] using hlt⟩
    have hsHead : s' ∈ headTuples b D := by
      simp only [headTuples, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact hsmono
      · intro i
        simpa [s'] using (hw (ρ i)).2.2.1
    have hzero :
        ∀ i,
          indexedIntervalSum
            (applyPositionPerm
              (applyPositionPerm σ π)
              (Equiv.swap b (y' i)))
            (s' i) (t' i) = 0 := by
      intro i
      simpa [y', s', t'] using (hw (ρ i)).2.2.2.2.2
    refine Or.inr ⟨b, b', hb2, hbfar, hgap, y', t',
      hywin, htwin, ?_⟩
    exact ⟨s', hsHead, π, hπadm, hzero⟩

def rightRepairAtom {n p D : ℕ}
    (θ : RepairParams n D) (σ : Fin n → ZMod p) : Prop :=
  Lemma55Event σ θ.b θ.b' θ.u
    (fun i => Equiv.swap θ.b (θ.y i))

def leftRepairAtom {n p D : ℕ}
    (θ : RepairParams n D) (σ : Fin n → ZMod p) : Prop :=
  Lemma56Event σ θ.b θ.b' θ.u
    (fun i => Equiv.swap θ.b (θ.y i))

theorem rightRepairEvent_mass
    {α : ℝ} (hα0 : 0 < α) (hαh : α < 1 / 2)
    (P : Section5Parameters α)
    {p : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hreg : Section5Regime P p S) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    orderingEventMass S (RightRepairEvent P.D) ≤
      (1 / 100 : ℝ) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  let Θ := rightRepairParameters S.card P.D
  have hcover :
      ∀ σ ∈ indexedOrderings S,
        RightRepairEvent P.D σ →
          ∃ θ ∈ Θ, rightRepairAtom θ σ := by
    intro σ hσ h
    rcases h with
      ⟨b, b', hb2, hbfar, hgap, y, u, hy, hu, hev⟩
    let θ : RepairParams S.card P.D :=
      ⟨b, b', y, u⟩
    refine ⟨θ, ?_, ?_⟩
    · simp [Θ, rightRepairParameters, θ, hb2, hbfar, hgap, hy, hu]
    · exact hev
  have hpoint :
      ∀ θ ∈ Θ,
        orderingEventMass S (rightRepairAtom θ) ≤
          1 / (S.card : ℝ) ^ 2 := by
    intro θ hθ
    have hpθ := (Finset.mem_filter.1 hθ).2
    have hb'le : paperPos θ.b' ≤ S.card - 2 := by
      have hD := section5Parameters_D_pos hα0 hαh P
      omega
    have hfix :
        ∀ i, FixedOutside θ.b θ.b'
          (Equiv.swap θ.b (θ.y i)) := by
      intro i
      exact swap_fixedOutside θ.b θ.b' (θ.y i)
        (hpθ.2.2.2.1 i).1 (hpθ.2.2.2.1 i).2
    exact lemma5_5 hα0 hαh P hp S hreg
      θ.b θ.b' hpθ.1 hb'le hpθ.2.2.1
      θ.u hpθ.2.2.2.2 hfix
  have hmass :
      orderingEventMass S (RightRepairEvent P.D) ≤
        ((rightRepairParameters S.card P.D).card : ℝ) *
          (1 / (S.card : ℝ) ^ 2) := by
    unfold orderingEventMass
    exact Section5External.witness_union_bound
      (indexedOrderings S) Θ
      (RightRepairEvent P.D) rightRepairAtom
      (1 / (S.card : ℝ) ^ 2)
      hcover (by simpa [orderingEventMass] using hpoint)
  have hcount :=
    Section5External.rightRepairParameters_card_le
      (n := S.card) (D := P.D)
  calc
    orderingEventMass S (RightRepairEvent P.D)
      ≤ ((rightRepairParameters S.card P.D).card : ℝ) *
          (1 / (S.card : ℝ) ^ 2) := hmass
    _ ≤ (S.card * (5 * P.D) ^ (2 * P.D) : ℕ) *
          (1 / (S.card : ℝ) ^ 2) := by
          gcongr
          exact_mod_cast hcount
    _ = (5 * P.D : ℝ) ^ (2 * P.D) /
          (S.card : ℝ) := by
          have hnpos : 0 < (S.card : ℝ) := by positivity
          field_simp
          ring
    _ ≤ (1 / 100 : ℝ) := by
          have h100 := P.second_ge_100
          have hC := P.Cα_second
          have hn := hreg.2.1
          have hbound :
              100 * (5 * P.D : ℝ) ^ (2 * P.D) ≤
                (S.card : ℝ) := by
            exact le_trans h100 (le_trans hC hn)
          have hnpos : 0 < (S.card : ℝ) := by positivity
          apply (div_le_iff₀ hnpos).2
          nlinarith

theorem leftRepairEvent_mass
    {α : ℝ} (hα0 : 0 < α) (hαh : α < 1 / 2)
    (P : Section5Parameters α)
    {p : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hreg : Section5Regime P p S) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    orderingEventMass S (LeftRepairEvent P.D) ≤
      (1 / 100 : ℝ) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  let Θ := leftRepairParameters S.card P.D
  have hcover :
      ∀ σ ∈ indexedOrderings S,
        LeftRepairEvent P.D σ →
          ∃ θ ∈ Θ, leftRepairAtom θ σ := by
    intro σ hσ h
    rcases h with
      ⟨b, b', hb2, hbfar, hgap, y, u, hy, hu, hev⟩
    let θ : RepairParams S.card P.D :=
      ⟨b, b', y, u⟩
    refine ⟨θ, ?_, ?_⟩
    · simp [Θ, leftRepairParameters, θ, hb2, hbfar, hgap, hy, hu]
    · exact hev
  have hpoint :
      ∀ θ ∈ Θ,
        orderingEventMass S (leftRepairAtom θ) ≤
          1 / (S.card : ℝ) ^ 2 := by
    intro θ hθ
    have hpθ := (Finset.mem_filter.1 hθ).2
    have hb'le : paperPos θ.b' ≤ S.card - 2 := by
      have hD := section5Parameters_D_pos hα0 hαh P
      omega
    have hfix :
        ∀ i, FixedOutside θ.b θ.b'
          (Equiv.swap θ.b (θ.y i)) := by
      intro i
      exact swap_fixedOutside θ.b θ.b' (θ.y i)
        (hpθ.2.2.2.1 i).1 (hpθ.2.2.2.1 i).2
    exact lemma5_6 hα0 hαh P hp S hreg
      θ.b θ.b' hpθ.1 hb'le hpθ.2.2.1
      θ.u
      (fun i => ⟨(hpθ.2.2.2.2 i).1,
        le_of_lt (hpθ.2.2.2.2 i).2⟩)
      hfix
  have hmass :
      orderingEventMass S (LeftRepairEvent P.D) ≤
        ((leftRepairParameters S.card P.D).card : ℝ) *
          (1 / (S.card : ℝ) ^ 2) := by
    unfold orderingEventMass
    exact Section5External.witness_union_bound
      (indexedOrderings S) Θ
      (LeftRepairEvent P.D) leftRepairAtom
      (1 / (S.card : ℝ) ^ 2)
      hcover (by simpa [orderingEventMass] using hpoint)
  have hcount :=
    Section5External.leftRepairParameters_card_le
      (n := S.card) (D := P.D)
  calc
    orderingEventMass S (LeftRepairEvent P.D)
      ≤ ((leftRepairParameters S.card P.D).card : ℝ) *
          (1 / (S.card : ℝ) ^ 2) := hmass
    _ ≤ (S.card * (5 * P.D) ^ (2 * P.D) : ℕ) *
          (1 / (S.card : ℝ) ^ 2) := by
          gcongr
          exact_mod_cast hcount
    _ = (5 * P.D : ℝ) ^ (2 * P.D) /
          (S.card : ℝ) := by
          have hnpos : 0 < (S.card : ℝ) := by positivity
          field_simp
          ring
    _ ≤ (1 / 100 : ℝ) := by
          have h100 := P.second_ge_100
          have hC := P.Cα_second
          have hn := hreg.2.1
          have hbound :
              100 * (5 * P.D : ℝ) ^ (2 * P.D) ≤
                (S.card : ℝ) := by
            exact le_trans h100 (le_trans hC hn)
          have hnpos : 0 < (S.card : ℝ) := by positivity
          apply (div_le_iff₀ hnpos).2
          nlinarith

/-- Lemma 5.3. -/
theorem lemma5_3
    {α : ℝ} (hα0 : 0 < α) (hαh : α < 1 / 2)
    (P : Section5Parameters α)
    {p : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hreg : Section5Regime P p S) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    orderingEventMass S (BadEvent3 P.D) ≤
      (1 / 25 : ℝ) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  let Core : (Fin S.card → ZMod p) → Prop :=
    fun σ =>
      BadEvent3 P.D σ ∧
        ¬ BadEvent0 P.D σ ∧ ¬ BadEvent1 P.D σ
  have hD := section5Parameters_D_pos hα0 hαh P
  have hsubset :
      ∀ σ, Core σ →
        RightRepairEvent P.D σ ∨ LeftRepairEvent P.D σ := by
    intro σ h
    exact badEvent3_core_side_reduction
      hD σ h.1 h.2.1 h.2.2
  have hcore :
      orderingEventMass S Core ≤ (2 / 100 : ℝ) := by
    calc
      orderingEventMass S Core
        ≤ orderingEventMass S
            (fun σ =>
              RightRepairEvent P.D σ ∨
                LeftRepairEvent P.D σ) := by
            apply uniformMass_mono
            intro σ h
            exact hsubset σ h
      _ ≤ orderingEventMass S (RightRepairEvent P.D) +
          orderingEventMass S (LeftRepairEvent P.D) := by
            exact uniformMass_or_le_add
              (indexedOrderings S)
              (RightRepairEvent P.D)
              (LeftRepairEvent P.D)
      _ ≤ 1 / 100 + 1 / 100 := by
            gcongr
            · exact rightRepairEvent_mass hα0 hαh P hp S hreg
            · exact leftRepairEvent_mass hα0 hαh P hp S hreg
      _ = 2 / 100 := by norm_num
  have h0 := lemma5_4 hα0 hαh P hp S hreg
  have h1 := lemma5_1 hα0 hαh P hp S hreg
  have htotal :=
    Section5External.mass_le_two_exceptions
      (indexedOrderings S)
      (BadEvent3 P.D) (BadEvent0 P.D) (BadEvent1 P.D)
      (2 / 100 : ℝ)
      (by simpa [orderingEventMass, Core] using hcore)
  nlinarith

end

end GrahamRearrangement
