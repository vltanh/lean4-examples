import Lean4Examples.GrahamRearrangement.BooleanSlice.Definitions
import Lean4Examples.GrahamRearrangement.External

open scoped BigOperators Pointwise

namespace GrahamRearrangement.Section3External

/-!
# External sampling/Fourier inputs specialized to the Section 3 model

These are still generic finite-probability or Fourier facts, not results of
Pham--Sauermann.  The paper's Lemmas 3.1--3.7 are proved in subsequent modules.
-/

noncomputable section

theorem balancedPartitions_nonempty {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hm : 0 < m) (hmS : m ≤ S.card) :
    (balancedPartitions (p := p) (m := m) S).Nonempty := by
  refine ⟨canonicalBalancedPartition S hm hmS, ?_⟩
  simp [balancedPartitions, canonicalBalancedPartition_spec S hm hmS]

theorem balancedChoiceSpace_card {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) :
    (balancedChoiceSpace S).card =
      (balancedPartitions S).card *
        balancedChoiceMultiplicity S.card m := by
  classical
  rw [card_eq_sum_card_fibers
    (balancedChoiceSpace S) (balancedPartitions S)
    Prod.fst
    (by
      intro q hq
      exact (mem_balancedChoiceSpace.mp hq).1)]
  calc
    ∑ P ∈ balancedPartitions S,
        ((balancedChoiceSpace S).filter fun q => q.1 = P).card
      = ∑ P ∈ balancedPartitions S, (blockChoices P).card := by
          apply Finset.sum_congr rfl
          intro P hP
          apply Finset.card_bij (fun q _ => q.2)
          · intro q hq
            rcases Finset.mem_filter.mp hq with ⟨hqS,hqP⟩
            have hmem := mem_balancedChoiceSpace.mp hqS
            simpa [hqP] using hmem.2
          · intro q hq r hr heq
            rcases q with ⟨Pq,Xq⟩
            rcases r with ⟨Pr,Xr⟩
            have hqP := (Finset.mem_filter.mp hq).2
            have hrP := (Finset.mem_filter.mp hr).2
            simp only at heq
            subst Pq
            subst Pr
            simp_all
          · intro X hX
            refine ⟨(P,X), ?_, rfl⟩
            apply Finset.mem_filter.mpr
            exact ⟨mem_balancedChoiceSpace.mpr ⟨hP,hX⟩, rfl⟩
    _ = ∑ _P ∈ balancedPartitions S,
          balancedChoiceMultiplicity S.card m := by
          apply Finset.sum_congr rfl
          intro P hP
          exact blockChoices_card_balanced
            (by simpa [balancedPartitions] using hP)
    _ = (balancedPartitions S).card *
          balancedChoiceMultiplicity S.card m := by simp [mul_comm]

theorem balancedChoice_event_card {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (E : (Fin m → ZMod p) → Prop)
    [DecidablePred E] :
    ((balancedChoiceSpace S).filter fun q => E q.2).card =
      ∑ P ∈ balancedPartitions S,
        (blockChoices P).filter E |>.card := by
  classical
  rw [card_eq_sum_card_fibers
    ((balancedChoiceSpace S).filter fun q => E q.2)
    (balancedPartitions S) Prod.fst
    (by
      intro q hq
      exact (mem_balancedChoiceSpace.mp
        (Finset.mem_filter.mp hq).1).1)]
  apply Finset.sum_congr rfl
  intro P hP
  apply Finset.card_bij (fun q _ => q.2)
  · intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hqE,hqP⟩
    rcases Finset.mem_filter.mp hqE with ⟨hqS,hEq⟩
    have hmem := mem_balancedChoiceSpace.mp hqS
    apply Finset.mem_filter.mpr
    simpa [hqP] using ⟨hmem.2,hEq⟩
  · intro q hq r hr heq
    rcases q with ⟨Pq,Xq⟩
    rcases r with ⟨Pr,Xr⟩
    have hqP := (Finset.mem_filter.mp hq).2
    have hrP := (Finset.mem_filter.mp hr).2
    simp only at heq
    subst Pq
    subst Pr
    simp_all
  · intro X hX
    rcases Finset.mem_filter.mp hX with ⟨hXP,hE⟩
    refine ⟨(P,X), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      exact ⟨mem_balancedChoiceSpace.mpr ⟨hP,hXP⟩,hE⟩
    · rfl

def permuteBalancedPartition {p m : ℕ}
    (π : Equiv.Perm (ZMod p))
    (P : Fin m → Finset (ZMod p)) :
    Fin m → Finset (ZMod p) :=
  fun i => (P i).image π

def permuteBlockChoice {p m : ℕ}
    (π : Equiv.Perm (ZMod p))
    (X : Fin m → ZMod p) :
    Fin m → ZMod p :=
  fun i => π (X i)

theorem permuteBalancedPartition_spec {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (π : Equiv.Perm (ZMod p)) (hπS : S.image π = S)
    {P : Fin m → Finset (ZMod p)}
    (hP : IsBalancedPartition S P) :
    IsBalancedPartition S (permuteBalancedPartition π P) := by
  classical
  constructor
  · intro i x hx
    rcases Finset.mem_image.mp hx with ⟨y,hy,rfl⟩
    rw [← hπS]
    exact Finset.mem_image.mpr ⟨y,hP.1 i hy,rfl⟩
  constructor
  · intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    rcases Finset.mem_image.mp hxi with ⟨a,hai,ha⟩
    rcases Finset.mem_image.mp hxj with ⟨b,hbj,hb⟩
    have hab : a = b := π.injective (ha.trans hb.symm)
    subst b
    exact Finset.disjoint_left.mp (hP.2.1 i j hij) hai hbj
  constructor
  · intro x
    constructor
    · intro hx
      rw [← hπS] at hx
      rcases Finset.mem_image.mp hx with ⟨y,hy,rfl⟩
      rcases (hP.2.2.1 y).1 hy with ⟨i,hyi⟩
      exact ⟨i,Finset.mem_image.mpr ⟨y,hyi,rfl⟩⟩
    · rintro ⟨i,hxi⟩
      rcases Finset.mem_image.mp hxi with ⟨y,hyi,rfl⟩
      rw [← hπS]
      exact Finset.mem_image.mpr
        ⟨y,(hP.2.2.1 y).2 ⟨i,hyi⟩,rfl⟩
  · intro i
    unfold permuteBalancedPartition
    rw [Finset.card_image_of_injective _ π.injective,
      hP.2.2.2 i]

theorem permuteBlockChoice_mem {p m : ℕ} [NeZero p]
    (π : Equiv.Perm (ZMod p))
    {P : Fin m → Finset (ZMod p)}
    {X : Fin m → ZMod p}
    (hX : X ∈ blockChoices P) :
    permuteBlockChoice π X ∈
      blockChoices (permuteBalancedPartition π P) := by
  apply blockChoices_mem_iff.mpr
  intro i
  exact Finset.mem_image.mpr
    ⟨X i,(blockChoices_mem_iff.mp hX) i,rfl⟩

theorem choiceSet_permute {p m : ℕ}
    (π : Equiv.Perm (ZMod p)) (X : Fin m → ZMod p) :
    choiceSet (permuteBlockChoice π X) =
      (choiceSet X).image π := by
  ext x
  simp [choiceSet,permuteBlockChoice]

theorem balancedChoice_fiber_equipotent {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    {R R' : Finset (ZMod p)}
    (hR : R ∈ S.powersetCard m)
    (hR' : R' ∈ S.powersetCard m) :
    ((balancedChoiceSpace S).filter fun q => choiceSet q.2 = R).card =
    ((balancedChoiceSpace S).filter fun q => choiceSet q.2 = R').card := by
  classical
  obtain ⟨π,hπR,hπS,hπout⟩ :=
    exists_perm_maps_finset S R R'
      (Finset.mem_powersetCard.mp hR).1
      (Finset.mem_powersetCard.mp hR').1
      (by rw [(Finset.mem_powersetCard.mp hR).2,
              (Finset.mem_powersetCard.mp hR').2])
  apply Finset.card_bij
    (fun q _ =>
      (permuteBalancedPartition π q.1,
       permuteBlockChoice π q.2))
  · intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hqS,hset⟩
    rcases mem_balancedChoiceSpace.mp hqS with ⟨hPmem,hX⟩
    have hP : IsBalancedPartition S q.1 := by
      simpa [balancedPartitions] using hPmem
    apply Finset.mem_filter.mpr
    constructor
    · apply mem_balancedChoiceSpace.mpr
      constructor
      · simpa [balancedPartitions] using
          permuteBalancedPartition_spec S π hπS hP
      · exact permuteBlockChoice_mem π hX
    · rw [choiceSet_permute,hset,hπR]
  · intro q hq r hr heq
    rcases q with ⟨P,X⟩
    rcases r with ⟨Q,Y⟩
    have hP := congrArg Prod.fst heq
    have hX := congrArg Prod.snd heq
    funext i at hP
    funext i at hX
    apply Prod.ext
    · funext i
      apply Finset.image_injective π.injective
      exact hP i
    · funext i
      exact π.injective (hX i)
  · intro q hq
    rcases q with ⟨P,X⟩
    let pre :=
      (permuteBalancedPartition π.symm P,
       permuteBlockChoice π.symm X)
    refine ⟨pre, ?_, ?_⟩
    · rcases Finset.mem_filter.mp hq with ⟨hqS,hset⟩
      rcases mem_balancedChoiceSpace.mp hqS with ⟨hPmem,hXmem⟩
      have hP : IsBalancedPartition S P := by
        simpa [balancedPartitions] using hPmem
      have hπsymS : S.image π.symm = S := by
        apply Finset.image_injective π.injective
        simp [hπS]
      apply Finset.mem_filter.mpr
      constructor
      · apply mem_balancedChoiceSpace.mpr
        constructor
        · simpa [balancedPartitions] using
            permuteBalancedPartition_spec S π.symm hπsymS hP
        · exact permuteBlockChoice_mem π.symm hXmem
      · rw [choiceSet_permute]
        apply Finset.image_injective π.injective
        simp [hπR,hset]
    · apply Prod.ext <;> funext i <;> simp [pre,
        permuteBalancedPartition,permuteBlockChoice]

theorem balancedChoiceSpace_nonempty {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hm : 0 < m) (hmS : m ≤ S.card) :
    (balancedChoiceSpace S).Nonempty := by
  obtain ⟨P,hPmem⟩ := balancedPartitions_nonempty S hm hmS
  have hP : IsBalancedPartition S P := by
    simpa [balancedPartitions] using hPmem
  have hne : ∀ i, (P i).Nonempty := by
    intro i
    have hb := balanced_block_size_bounds S hm hmS hP i
    have hq := Nat.div_pos hmS hm
    exact Finset.card_pos.mp (lt_of_lt_of_le hq hb.1)
  let X : Fin m → ZMod p := fun i => Classical.choose (hne i)
  have hX : X ∈ blockChoices P := by
    apply blockChoices_mem_iff.mpr
    intro i
    exact Classical.choose_spec (hne i)
  exact ⟨(P,X),mem_balancedChoiceSpace.mpr ⟨hPmem,hX⟩⟩

theorem balancedChoice_choiceSet_uniform {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hm : 0 < m) (hmS : m ≤ S.card)
    (E : Finset (ZMod p) → Prop) [DecidablePred E] :
    uniformMass (balancedChoiceSpace S)
        (fun q => E (choiceSet q.2)) =
      uniformMass (S.powersetCard m) E := by
  classical
  have hvalues : (S.powersetCard m).Nonempty :=
    powersetCard_nonempty S hmS
  have hspace := balancedChoiceSpace_nonempty S hm hmS
  apply uniformMass_statistic_of_pairwise_equal_fibers
    (balancedChoiceSpace S) (S.powersetCard m)
    (fun q => choiceSet q.2)
  · intro q hq
    exact choiceSet_mem_powersetCard hq
  · exact hvalues
  · exact hspace
  · intro R hR R' hR'
    exact balancedChoice_fiber_equipotent S hR hR'
  · exact E

theorem balancedChoice_mass_eq_partitionExpectation {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hm : 0 < m) (hmS : m ≤ S.card)
    (z : ZMod p) :
    uniformMass (balancedChoiceSpace S)
        (fun q => choiceSum q.2 = z) =
      partitionExpectation S (fun P => conditionalSumMass P z) := by
  classical
  let K := balancedChoiceMultiplicity S.card m
  have hK : 0 < K := balancedChoiceMultiplicity_pos S.card m hm hmS
  unfold partitionExpectation conditionalSumMass
  unfold uniformExpectation uniformMass
  rw [balancedChoice_event_card S (fun X => choiceSum X = z),
      balancedChoiceSpace_card S]
  have hpart :
      ∀ P ∈ balancedPartitions S,
        (blockChoices P).card = K := by
    intro P hP
    exact blockChoices_card_balanced
      (by simpa [balancedPartitions] using hP)
  have hden :
      ∀ P ∈ balancedPartitions S,
        ((blockChoices P).card : ℝ) = K := by
    intro P hP
    exact_mod_cast hpart P hP
  simp_rw [hden]
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  field_simp
  ring

/-- The balanced-partition/one-choice-per-block sampling experiment is exactly
uniform on size-`m` subsets. -/
theorem sliceMass_eq_partition_average {p m : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hm : 0 < m) (hmS : m ≤ S.card)
    (z : ZMod p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    sliceMass S m z =
      partitionExpectation S (fun P => conditionalSumMass P z) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [← balancedChoice_mass_eq_partitionExpectation S hm hmS z]
  unfold sliceMass
  rw [← balancedChoice_choiceSet_uniform S hm hmS
      (fun R => subsetSum R = z)]
  apply uniformMass_congr
  intro q hq
  rcases mem_balancedChoiceSpace.mp hq with ⟨hPmem,hX⟩
  have hP : IsBalancedPartition S q.1 := by
    simpa [balancedPartitions] using hPmem
  rw [choiceSum_eq_subsetSum_choiceSet hP hX]

/-- Every block in a valid balanced partition has the prescribed size. -/
theorem balanced_block_size_bounds {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hm : 0 < m) (hmS : m ≤ S.card)
    {P : Fin m → Finset (ZMod p)} (hP : IsBalancedPartition S P)
    (i : Fin m) :
    S.card / m ≤ (P i).card ∧
      (P i).card ≤ S.card / m + 1 := by
  rw [hP.2.2.2 i]
  unfold balancedBlockSize
  split <;> omega

/-- The quantitative block-size estimate used in (3.3). -/
theorem balanced_block_sqrt_two_bound {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : 2 ≤ S.card)
    (hm4 : m ≤ S.card / 4)
    {P : Fin m → Finset (ZMod p)} (hP : IsBalancedPartition S P)
    (i : Fin m) :
    ((P i).card : ℝ) ≤ Real.sqrt 2 * S.card / m := by
  have hm : 0 < m := by
    by_contra h
    have : m = 0 := Nat.eq_zero_of_not_pos h
    subst m
    exact Fin.elim0 i
  have hmS : m ≤ S.card := by
    exact le_trans hm4 (Nat.div_le_self _ _)
  have hb := balanced_block_size_bounds S hm hmS hP i
  have hfloor :
      (S.card / m : ℕ) ≤ (S.card : ℝ) / m := by
    exact_mod_cast Nat.div_le_iff_le_mul (by omega) |>.2
      (Nat.sub_lt_iff_lt_add.mp (Nat.mod_lt S.card hm))
  have hratio : (4 : ℝ) ≤ (S.card : ℝ) / m := by
    have hm4' : 4 * m ≤ S.card := by
      exact (Nat.le_div_iff_mul_le (by omega)).mp hm4
    exact (le_div_iff₀ (by positivity : (0 : ℝ) < m)).2
      (by exact_mod_cast hm4')
  have hsqrt : (5 / 4 : ℝ) ≤ Real.sqrt 2 := by
    have hs0 := Real.sqrt_nonneg 2
    have hs2 : (Real.sqrt 2) ^ 2 = 2 := by norm_num
    nlinarith
  have hcard :
      ((P i).card : ℝ) ≤ (S.card : ℝ) / m + 1 := by
    exact_mod_cast hb.2
    nlinarith
  nlinarith

/-- After removing a fixed point, its balanced block still has at least
|S|/(2m) remaining points in the Section 3 range. -/
theorem point_block_remainder_lower {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (x : ZMod p)
    (hm : 0 < m) (hm4 : m ≤ S.card / 4)
    {P : Fin m → Finset (ZMod p)}
    (hP : IsBalancedPartition S P) (hx : x ∈ S) :
    S.card / (2 * m) ≤ (pointBlock S P x \ {x}).card := by
  have hmS : m ≤ S.card := le_trans hm4 (Nat.div_le_self _ _)
  have hmem : x ∈ pointBlock S P x :=
    mem_blockIndex S P x hm hP hx
  have hcardBlock :=
    (balanced_block_size_bounds S hm hmS hP (blockIndex S P x)).1
  have hcardErase :
      (pointBlock S P x \ {x}).card =
        (pointBlock S P x).card - 1 := by
    rw [Finset.sdiff_singleton_eq_erase,
      Finset.card_erase_of_mem hmem]
  rw [hcardErase]
  have hq4 : 4 ≤ S.card / m := by
    apply (Nat.le_div_iff_mul_le hm).2
    have hm4' : 4 * m ≤ S.card :=
      (Nat.le_div_iff_mul_le (by omega)).mp hm4
    simpa [mul_comm] using hm4'
  have hhalf :
      S.card / (2 * m) ≤ (S.card / m) / 2 := by
    exact Nat.div_le_div_right
      (Nat.le_of_eq (by omega : 2 * m = m * 2))
  omega

theorem permuteBalancedPartition_blockIndex
    {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (x : ZMod p)
    (hm : 0 < m) (hxS : x ∈ S)
    (π : Equiv.Perm (ZMod p))
    (hπS : S.image π = S) (hπx : π x = x)
    {P : Fin m → Finset (ZMod p)}
    (hP : IsBalancedPartition S P) :
    blockIndex S (permuteBalancedPartition π P) x =
      blockIndex S P x := by
  let i := blockIndex S P x
  have hxi : x ∈ P i :=
    mem_blockIndex S P x hm hP hxS
  have hP' := permuteBalancedPartition_spec S π hπS hP
  apply blockIndex_eq_of_mem S hm hP' hxS
  exact Finset.mem_image.mpr ⟨x,hxi,hπx⟩

theorem permute_pointBlock_remainder
    {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (x : ZMod p)
    (hm : 0 < m) (hxS : x ∈ S)
    (π : Equiv.Perm (ZMod p))
    (hπS : S.image π = S) (hπx : π x = x)
    {P : Fin m → Finset (ZMod p)}
    (hP : IsBalancedPartition S P) :
    pointBlock S (permuteBalancedPartition π P) x \ {x} =
      (pointBlock S P x \ {x}).image π := by
  have hidx :=
    permuteBalancedPartition_blockIndex S x hm hxS π hπS hπx hP
  unfold pointBlock permuteBalancedPartition
  rw [hidx]
  ext y
  constructor
  · intro hy
    rcases Finset.mem_sdiff.mp hy with ⟨hyim,hyx⟩
    rcases Finset.mem_image.mp hyim with ⟨z,hz,rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨z,?_,rfl⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨hz,?_⟩
    intro hzx
    simp at hzx
    subst z
    exact hyx (by simp [hπx])
  · intro hy
    rcases Finset.mem_image.mp hy with ⟨z,hz,rfl⟩
    rcases Finset.mem_sdiff.mp hz with ⟨hzP,hzx⟩
    apply Finset.mem_sdiff.mpr
    constructor
    · exact Finset.mem_image.mpr ⟨z,hzP,rfl⟩
    · intro h
      simp at h
      have : z = x := π.injective (h.trans hπx.symm)
      exact hzx (by simp [this])

def blockIndexFiber {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (x : ZMod p) (i : Fin m) :
    Finset (Fin m → Finset (ZMod p)) :=
  (balancedPartitions S).filter fun P => blockIndex S P x = i

theorem blockRemainder_fiber_equipotent
    {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (x : ZMod p)
    (hm : 0 < m) (hmS : m ≤ S.card) (hxS : x ∈ S)
    (i : Fin m)
    {A B : Finset (ZMod p)}
    (hA : A ∈ (S \ {x}).powersetCard
      (balancedBlockSize S.card m i - 1))
    (hB : B ∈ (S \ {x}).powersetCard
      (balancedBlockSize S.card m i - 1)) :
    ((blockIndexFiber S x i).filter fun P =>
      pointBlock S P x \ {x} = A).card =
    ((blockIndexFiber S x i).filter fun P =>
      pointBlock S P x \ {x} = B).card := by
  classical
  let U := S \ {x}
  obtain ⟨π,hπA,hπU,hπfix⟩ :=
    exists_perm_maps_finset U A B
      (Finset.mem_powersetCard.mp hA).1
      (Finset.mem_powersetCard.mp hB).1
      (by rw [(Finset.mem_powersetCard.mp hA).2,
              (Finset.mem_powersetCard.mp hB).2])
  have hxU : x ∉ U := by simp [U]
  have hπx : π x = x := hπfix x hxU
  have hπS : S.image π = S := by
    ext y
    by_cases hyx : y = x
    · subst y
      simp [hπx,hxS]
    · have hyU : y ∈ U ↔ y ∈ S := by simp [U,hyx]
      rw [← hπU]
      constructor
      · intro hy
        rcases Finset.mem_image.mp hy with ⟨z,hz,rfl⟩
        exact Finset.mem_image.mpr ⟨z,(hyU.mp hz),rfl⟩
      · intro hy
        rcases Finset.mem_image.mp hy with ⟨z,hz,rfl⟩
        have hzx : z ≠ x := by
          intro h
          subst z
          have : π x = x := hπx
          subst y
          exact hyx rfl
        exact Finset.mem_image.mpr
          ⟨z,(by simpa [U,hzx] using hz),rfl⟩
  apply Finset.card_bij
    (fun P _ => permuteBalancedPartition π P)
  · intro P hP
    rcases Finset.mem_filter.mp hP with ⟨hPF,hrem⟩
    rcases Finset.mem_filter.mp hPF with ⟨hPmem,hidx⟩
    have hPbal : IsBalancedPartition S P := by
      simpa [balancedPartitions] using hPmem
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      constructor
      · simpa [balancedPartitions] using
          permuteBalancedPartition_spec S π hπS hPbal
      · rw [permuteBalancedPartition_blockIndex
          S x hm hxS π hπS hπx hPbal,hidx]
    · rw [permute_pointBlock_remainder
        S x hm hxS π hπS hπx hPbal,hrem,hπA]
  · intro P hP Q hQ hEq
    funext r
    have hr := congrFun hEq r
    apply Finset.image_injective π.injective
    exact hr
  · intro Q hQ
    rcases Finset.mem_filter.mp hQ with ⟨hQF,hrem⟩
    rcases Finset.mem_filter.mp hQF with ⟨hQmem,hidx⟩
    have hQbal : IsBalancedPartition S Q := by
      simpa [balancedPartitions] using hQmem
    let P := permuteBalancedPartition π.symm Q
    refine ⟨P,?_,?_⟩
    · have hπsymS : S.image π.symm = S := by
        apply Finset.image_injective π.injective
        simpa using congrArg (Finset.image π) hπS
      have hπsymx : π.symm x = x :=
        symm_fixes_of_fixes π hπx
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_filter.mpr
        constructor
        · simpa [balancedPartitions,P] using
            permuteBalancedPartition_spec S π.symm hπsymS hQbal
        · simpa [P,permuteBalancedPartition_blockIndex
            S x hm hxS π.symm hπsymS hπsymx hQbal] using hidx
      · have hrem' :=
          permute_pointBlock_remainder
            S x hm hxS π.symm hπsymS hπsymx hQbal
        rw [hrem',hrem]
        apply Finset.image_injective π.injective
        simpa using congrArg (Finset.image π.symm) hπA
    · funext r
      simp [P,permuteBalancedPartition]

theorem blockRemainder_conditional_uniform
    {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (x : ZMod p)
    (hm : 0 < m) (hmS : m ≤ S.card) (hxS : x ∈ S)
    (i : Fin m)
    (hfiber : (blockIndexFiber S x i).Nonempty)
    (E : Finset (ZMod p) → Prop) [DecidablePred E] :
    uniformMass (blockIndexFiber S x i)
      (fun P => E (pointBlock S P x \ {x})) =
    uniformMass
      ((S \ {x}).powersetCard
        (balancedBlockSize S.card m i - 1)) E := by
  classical
  let values := (S \ {x}).powersetCard
    (balancedBlockSize S.card m i - 1)
  have hvalues : values.Nonempty := by
    obtain ⟨P,hPF⟩ := hfiber
    rcases Finset.mem_filter.mp hPF with ⟨hPmem,hidx⟩
    have hP : IsBalancedPartition S P := by
      simpa [balancedPartitions] using hPmem
    exact ⟨pointBlock S P x \ {x},
      pointBlock_remainder_mem_powerset S x hm hmS hP hxS i hidx⟩
  have hmap :
      ∀ P ∈ blockIndexFiber S x i,
        pointBlock S P x \ {x} ∈ values := by
    intro P hPF
    rcases Finset.mem_filter.mp hPF with ⟨hPmem,hidx⟩
    have hP : IsBalancedPartition S P := by
      simpa [balancedPartitions] using hPmem
    exact pointBlock_remainder_mem_powerset S x hm hmS hP hxS i hidx
  apply uniformMass_statistic_of_pairwise_equal_fibers
    (blockIndexFiber S x i) values
    (fun P => pointBlock S P x \ {x})
    hmap hvalues hfiber
  · intro A hA B hB
    exact blockRemainder_fiber_equipotent
      S x hm hmS hxS i hA hB
  · exact E

/-- If a subset has density at least 1/4, the block containing a fixed point
misses the expected number of its points only with the hypergeometric tail used
in Lemma 3.1. -/
axiom block_sparse_tail {p m : ℕ} [NeZero p]
    (S G : Finset (ZMod p)) (x : ZMod p)
    (hx : x ∈ S) (hGS : G ⊆ S)
    (hdensity : S.card ≤ 4 * G.card)
    (hm : 0 < m) (hm4 : m ≤ S.card / 4) :
    partitionMass S (fun P =>
      ((pointBlock S P x \\ {x}) ∩ G).card <
        S.card / (16 * m)) ≤
      Real.exp (-(S.card : ℝ) / (64 * m))

/-- If a subset has density at least 3/4, the block containing a fixed point
has fewer than a quarter-block worth of its points only with the tail used in
Lemma 3.3. -/
axiom block_dense_tail {p m : ℕ} [NeZero p]
    (S G : Finset (ZMod p)) (x : ZMod p)
    (hx : x ∈ S) (hGS : G ⊆ S)
    (hdensity : 3 * S.card ≤ 4 * G.card)
    (hm : 0 < m) (hm4 : m ≤ S.card / 4) :
    partitionMass S (fun P =>
      ((pointBlock S P x \\ {x}) ∩ G).card <
        S.card / (4 * m)) ≤
      Real.exp (-(S.card : ℝ) / (48 * m))

/-- Fubini for counting a finite family of partition events. -/
theorem partitionExpectation_card_eq_sum_mass {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (E : ZMod p → (Fin m → Finset (ZMod p)) → Prop)
    [∀ χ, DecidablePred (E χ)] :
    partitionExpectation S
        (fun P => ((Finset.univ.filter fun χ => E χ P).card : ℝ)) =
      ∑ χ : ZMod p, partitionMass S (E χ) := by
  classical
  unfold partitionExpectation partitionMass uniformExpectation uniformMass
  rw [Finset.sum_div]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ hχ
  norm_cast
  exact Finset.card_bij
    (fun P _ => P)
    (by intro P hP; simpa using hP)
    (by intro P hP Q hQ h; exact h)
    (by intro P hP; exact ⟨P, by simpa using hP, rfl⟩)

/-- Average indicator bound for a deterministic subset of characters. -/
theorem partitionExpectation_filter_le {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (T : Finset (ZMod p))
    (E : ZMod p → (Fin m → Finset (ZMod p)) → Prop)
    [∀ χ, DecidablePred (E χ)]
    (hbound : ∀ χ ∈ T, partitionMass S (E χ) ≤ 1 / (S.card : ℝ) ^ 9) :
    partitionExpectation S
      (fun P => ((T.filter fun χ => E χ P).card : ℝ)) ≤
        (T.card : ℝ) / (S.card : ℝ) ^ 9 := by
  classical
  unfold partitionExpectation
  have hrewrite :
      uniformExpectation (balancedPartitions S)
          (fun P => ((T.filter fun χ => E χ P).card : ℝ)) =
        ∑ χ ∈ T, partitionMass S (E χ) := by
    unfold uniformExpectation partitionMass uniformMass
    rw [Finset.sum_div]
    congr 1
    rw [Finset.sum_comm]
    rfl
  rw [hrewrite]
  calc
    ∑ χ ∈ T, partitionMass S (E χ)
      ≤ ∑ _χ ∈ T, 1 / (S.card : ℝ) ^ 9 := by
          gcongr with χ hχ
          exact hbound χ hχ
    _ = (T.card : ℝ) / (S.card : ℝ) ^ 9 := by
          simp [div_eq_mul_inv, mul_comm]

/-- Generic double counting over the rows of a partition energy. -/
theorem partition_energy_lower_by_rows {α ι : Type*}
    [Fintype ι] [DecidableEq α]
    (S : Finset α) (P : ι → Finset α)
    (hpartition : (∀ i, P i ⊆ S) ∧
      (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
      (∀ x, x ∈ S ↔ ∃ i, x ∈ P i))
    (w : α → α → ℝ) (rowLower : α → ℝ)
    (hrow : ∀ i, ∀ x ∈ P i,
      rowLower x ≤ ∑ y ∈ P i, w x y) :
    ∑ i, ∑ x ∈ P i, ∑ y ∈ P i, w x y ≥
      ∑ x ∈ S, rowLower x := by
  classical
  have hsum :
      ∑ i, ∑ x ∈ P i, rowLower x =
        ∑ x ∈ S, rowLower x := by
    rw [← Finset.sum_biUnion]
    · congr 1
      ext x
      simp [hpartition.2.2 x]
    · intro i hi j hj hij
      exact hpartition.2.1 i j hij
  rw [← hsum]
  gcongr with i hi x hx
  exact hrow i x hx

/-- Pair-uniform expectation expands into the double average over `S×S`. -/
theorem pair_uniform_expectation {α : Type*} [DecidableEq α]
    (S : Finset α) (hS : S.Nonempty) (f : α → α → ℝ) :
    uniformExpectation (S.product S) (fun q => f q.1 q.2) =
      (1 / (S.card : ℝ) ^ 2) *
        ∑ x ∈ S, ∑ y ∈ S, f x y := by
  unfold uniformExpectation
  rw [Finset.sum_product, Finset.card_product]
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  field_simp
  ring

/-- Averaging over one coordinate extracts a fixed witness with at least the
global average success probability. -/
theorem exists_fiber_mass_ge_pair_mass {α : Type*} [DecidableEq α]
    (S : Finset α) (hS : S.Nonempty) (E : α → α → Prop)
    [DecidablePred fun q : α × α => E q.1 q.2]
    [∀ y, DecidablePred fun x => E x y] :
    ∃ y ∈ S,
      uniformMass S (fun x => E x y) ≥
        uniformMass (S.product S) (fun q => E q.1 q.2) := by
  classical
  have havg :
      uniformMass (S.product S) (fun q => E q.1 q.2) =
        uniformExpectation S (fun y => uniformMass S (fun x => E x y)) := by
    unfold uniformMass uniformExpectation
    rw [Finset.card_product]
    have hcard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
    field_simp
    rw [Finset.sum_comm]
    ring
  rw [havg]
  by_contra h
  push_neg at h
  have hlt :
      uniformExpectation S (fun y => uniformMass S (fun x => E x y)) <
        uniformExpectation S
          (fun _ => uniformExpectation S
            (fun y => uniformMass S (fun x => E x y))) := by
    apply uniformExpectation_strictMono hS
    intro y hy
    exact h y hy
  rw [uniformExpectation_const S hS] at hlt
  exact lt_irrefl _ hlt

/-- The elementary dyadic numerical tail summation used at the end of Theorem 1.3. -/
axiom dyadic_exp_sum_le_two :
    ∑' l : ℕ, Real.exp ((l : ℝ) / 2 - (2 : ℝ) ^ l) ≤ 2

end

end GrahamRearrangement.Section3External
