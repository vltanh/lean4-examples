import Lean4Examples.GrahamRearrangement.Preliminaries
import Lean4Examples.GrahamRearrangement.Probability

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Section 3: definitions

Finite sample spaces and deterministic/Fourier quantities used in the proof of
Theorem 1.3.
-/

noncomputable section

/-- Uniform probability mass that a size-`m` subset of `S` has sum `z`. -/
def sliceMass {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (m : ℕ) (z : ZMod p) : ℝ :=
  uniformMass (S.powersetCard m) (fun R => subsetSum R = z)

theorem sliceMass_nonneg {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (z : ZMod p) :
    0 ≤ sliceMass S m z :=
  uniformMass_nonneg _ _

theorem sliceMass_le_one {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (z : ZMod p) :
    sliceMass S m z ≤ 1 :=
  uniformMass_le_one _ _

/-- The balanced size of block `i` when `n` points are split into `m` blocks.
The first `n % m` blocks have size `n / m + 1`; the rest have size `n / m`. -/
def balancedBlockSize (n m : ℕ) (i : Fin m) : ℕ :=
  n / m + if i.val < n % m then 1 else 0

def balancedPrefix (n m i : ℕ) : ℕ :=
  i * (n / m) + min i (n % m)

theorem balancedPrefix_zero (n m : ℕ) :
    balancedPrefix n m 0 = 0 := by
  simp [balancedPrefix]

theorem balancedPrefix_succ {n m i : ℕ}
    (hm : 0 < m) (hi : i < m) :
    balancedPrefix n m (i + 1) - balancedPrefix n m i =
      balancedBlockSize n m ⟨i,hi⟩ := by
  unfold balancedPrefix balancedBlockSize
  by_cases hir : i < n % m
  · have hir' : i + 1 ≤ n % m := by omega
    simp [hir, Nat.min_eq_left (by omega),
      Nat.min_eq_left hir']
    omega
  · have hri : n % m ≤ i := Nat.le_of_not_gt hir
    have hri' : n % m ≤ i + 1 := le_trans hri (Nat.le_succ _)
    simp [hir, Nat.min_eq_right hri, Nat.min_eq_right hri']
    omega

theorem balancedPrefix_m {n m : ℕ} (hm : 0 < m) :
    balancedPrefix n m m = n := by
  unfold balancedPrefix
  have hmod : n % m < m := Nat.mod_lt n hm
  rw [Nat.min_eq_right (Nat.le_of_lt hmod)]
  exact Nat.div_add_mod n m

theorem balancedPrefix_mono {n m i j : ℕ}
    (hij : i ≤ j) :
    balancedPrefix n m i ≤ balancedPrefix n m j := by
  unfold balancedPrefix
  gcongr
  exact min_le_min_right _ hij

def balancedBlockIndex (n m j : ℕ) : ℕ :=
  if j < (n % m) * (n / m + 1) then
    j / (n / m + 1)
  else
    n % m +
      (j - (n % m) * (n / m + 1)) / (n / m)

theorem balancedBlockIndex_lt
    (n m : ℕ) (hm : 0 < m) (hmn : m ≤ n)
    (j : ℕ) (hj : j < n) :
    balancedBlockIndex n m j < m := by
  let q := n / m
  let r := n % m
  have hq : 0 < q := Nat.div_pos hmn hm
  have hr : r < m := Nat.mod_lt n hm
  have hn : n = m * q + r := by
    simpa [q,r, Nat.mul_comm] using (Nat.div_add_mod n m).symm
  unfold balancedBlockIndex
  by_cases hfirst : j < r * (q + 1)
  · simp [hfirst]
    have hdiv : j / (q + 1) < r := by
      exact (Nat.div_lt_iff_lt_mul (by omega)).2 (by simpa [mul_comm] using hfirst)
    omega
  · simp [hfirst]
    have hj2 : j - r * (q + 1) < (m - r) * q := by
      rw [hn] at hj
      omega
    have hdiv :
        (j - r * (q + 1)) / q < m - r := by
      exact (Nat.div_lt_iff_lt_mul hq).2
        (by simpa [mul_comm] using hj2)
    omega

theorem balancedBlockIndex_range
    (n m : ℕ) (hm : 0 < m) (hmn : m ≤ n)
    (j : ℕ) (hj : j < n) :
    balancedPrefix n m (balancedBlockIndex n m j) ≤ j ∧
      j < balancedPrefix n m (balancedBlockIndex n m j + 1) := by
  let q := n / m
  let r := n % m
  have hq : 0 < q := Nat.div_pos hmn hm
  have hr : r < m := Nat.mod_lt n hm
  unfold balancedBlockIndex balancedPrefix
  by_cases hfirst : j < r * (q + 1)
  · have hi : j / (q + 1) < r :=
      (Nat.div_lt_iff_lt_mul (by omega)).2
        (by simpa [mul_comm] using hfirst)
    simp [hfirst, q, r, Nat.min_eq_left (Nat.le_of_lt hi),
      Nat.min_eq_left (by omega : j / (q + 1) + 1 ≤ r)]
    constructor
    · exact Nat.mul_div_le j (q + 1)
    · have hmod := Nat.mod_lt j (by omega : 0 < q + 1)
      have hdecomp := Nat.div_add_mod j (q + 1)
      omega
  · have hri : r ≤ r +
        (j - r * (q + 1)) / q := by omega
    have hltm := balancedBlockIndex_lt n m hm hmn j hj
    have hidx :
        r + (j - r * (q + 1)) / q < m := by
      simpa [balancedBlockIndex, hfirst, q, r] using hltm
    simp [hfirst, q, r, Nat.min_eq_right hri,
      Nat.min_eq_right (by omega : r ≤ r +
        (j - r * (q + 1)) / q + 1)]
    have hge : r * (q + 1) ≤ j := Nat.le_of_not_gt hfirst
    constructor
    · have hmul := Nat.mul_div_le
          (j - r * (q + 1)) q
      omega
    · have hmod :=
        Nat.mod_lt (j - r * (q + 1)) hq
      have hdecomp :=
        Nat.div_add_mod (j - r * (q + 1)) q
      omega

def canonicalBalancedPartition {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hm : 0 < m) (hmS : m ≤ S.card) :
    Fin m → Finset (ZMod p) := by
  classical
  let e : Fin S.card ≃ {x // x ∈ S} :=
    Fintype.equivOfCardEq (by simp)
  exact fun i =>
    (finSegment S.card
      (balancedPrefix S.card m i.val)
      (balancedPrefix S.card m (i.val + 1))
      (by
        exact le_trans
          (balancedPrefix_mono (show i.val + 1 ≤ m by omega))
          (by rw [balancedPrefix_m hm])))
      ).image (fun j => (e j).1)

theorem canonicalBalancedPartition_spec {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hm : 0 < m) (hmS : m ≤ S.card) :
    IsBalancedPartition S (canonicalBalancedPartition S hm hmS) := by
  classical
  let e : Fin S.card ≃ {x // x ∈ S} :=
    Fintype.equivOfCardEq (by simp)
  constructor
  · intro i x hx
    rcases Finset.mem_image.mp hx with ⟨j,hj,rfl⟩
    exact (e j).2
  constructor
  · intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    rcases Finset.mem_image.mp hxi with ⟨a,ha,hax⟩
    rcases Finset.mem_image.mp hxj with ⟨b,hb,hbx⟩
    have hab : a = b := e.injective (Subtype.ext (hax.trans hbx.symm))
    subst b
    have hai := mem_finSegment.mp ha
    have haj := mem_finSegment.mp hb
    by_cases hijv : i.val < j.val
    · have hp :=
        balancedPrefix_mono (show i.val + 1 ≤ j.val by omega)
      omega
    · have hp :=
        balancedPrefix_mono (show j.val + 1 ≤ i.val by omega)
      omega
  constructor
  · intro x
    constructor
    · intro hx
      obtain ⟨j,hj⟩ := e.surjective ⟨x,hx⟩
      let i : ℕ := balancedBlockIndex S.card m j.val
      have hi : i < m := by
        exact balancedBlockIndex_lt S.card m hm hmS j.val j.isLt
      refine ⟨⟨i,hi⟩, ?_⟩
      apply Finset.mem_image.mpr
      refine ⟨j, ?_, congrArg Subtype.val hj⟩
      apply mem_finSegment.mpr
      simpa [i] using
        balancedBlockIndex_range S.card m hm hmS j.val j.isLt
    · rintro ⟨i,hxi⟩
      exact (show x ∈ S from by
        rcases Finset.mem_image.mp hxi with ⟨j,hj,rfl⟩
        exact (e j).2)
  · intro i
    unfold canonicalBalancedPartition
    rw [Finset.card_image_of_injective _ e.injective]
    rw [card_finSegment]
    exact balancedPrefix_succ hm i.isLt

/-- Ordered balanced partitions of `S` into `m` labelled blocks. -/
def IsBalancedPartition {p m : ℕ} (S : Finset (ZMod p))
    (P : Fin m → Finset (ZMod p)) : Prop :=
  (∀ i, P i ⊆ S) ∧
  (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
  (∀ x, x ∈ S ↔ ∃ i, x ∈ P i) ∧
  (∀ i, (P i).card = balancedBlockSize S.card m i)

/-- The finite sample space of ordered balanced partitions. -/
def balancedPartitions {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) : Finset (Fin m → Finset (ZMod p)) := by
  classical
  exact Finset.univ.filter (IsBalancedPartition S)

/-- The block index containing `x` in a balanced partition; arbitrary outside
well-formed inputs. -/
def blockIndex {p m : ℕ} [NeZero p] (S : Finset (ZMod p))
    (P : Fin m → Finset (ZMod p)) (x : ZMod p) : Fin m := by
  classical
  by_cases hm : 0 < m
  · by_cases hP : IsBalancedPartition S P ∧ x ∈ S
    · have hex : ∃ i : Fin m, x ∈ P i := (hP.1.2.2 x).1 hP.2
      exact Classical.choose hex
    · exact ⟨0, hm⟩
  · exact Fin.elim0 (by simpa [Nat.not_lt] using hm)

theorem mem_blockIndex {p m : ℕ} [NeZero p] (S : Finset (ZMod p))
    (P : Fin m → Finset (ZMod p)) (x : ZMod p)
    (hm : 0 < m) (hP : IsBalancedPartition S P) (hx : x ∈ S) :
    x ∈ P (blockIndex S P x) := by
  classical
  unfold blockIndex
  simp [hm, hP, hx, Classical.choose_spec]

theorem blockIndex_eq_of_mem {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    {P : Fin m → Finset (ZMod p)}
    (hm : 0 < m) (hP : IsBalancedPartition S P)
    {x : ZMod p} (hxS : x ∈ S)
    {i : Fin m} (hxi : x ∈ P i) :
    blockIndex S P x = i := by
  have hxChosen := mem_blockIndex S P x hm hP hxS
  by_contra hne
  exact Finset.disjoint_left.mp
    (hP.2.1 (blockIndex S P x) i hne) hxChosen hxi

theorem pointBlock_card {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    {P : Fin m → Finset (ZMod p)}
    (hm : 0 < m) (hP : IsBalancedPartition S P)
    {x : ZMod p} (hxS : x ∈ S) :
    (pointBlock S P x).card =
      balancedBlockSize S.card m (blockIndex S P x) := by
  exact hP.2.2.2 (blockIndex S P x)

/-- The block containing a given point. -/
def pointBlock {p m : ℕ} [NeZero p] (S : Finset (ZMod p))
    (P : Fin m → Finset (ZMod p)) (x : ZMod p) : Finset (ZMod p) :=
  P (blockIndex S P x)

/-- Conditional choices of one point from each block. -/
def blockChoices {p m : ℕ} [NeZero p]
    (P : Fin m → Finset (ZMod p)) : Finset (Fin m → ZMod p) :=
  Finset.univ.pi P

/-- The chosen subset generated by one point from each block. -/
def choiceSet {p m : ℕ} (X : Fin m → ZMod p) : Finset (ZMod p) :=
  Finset.univ.image X

/-- Sum of one point chosen from each block. -/
def choiceSum {p m : ℕ} (X : Fin m → ZMod p) : ZMod p :=
  ∑ i, X i

theorem blockChoices_mem_iff {p m : ℕ} [NeZero p]
    {P : Fin m → Finset (ZMod p)} {X : Fin m → ZMod p} :
    X ∈ blockChoices P ↔ ∀ i, X i ∈ P i := by
  simp [blockChoices]

theorem choice_injective_of_partition {p m : ℕ} [NeZero p]
    {S : Finset (ZMod p)}
    {P : Fin m → Finset (ZMod p)} (hP : IsBalancedPartition S P)
    {X : Fin m → ZMod p} (hX : X ∈ blockChoices P) :
    Function.Injective X := by
  intro i j hij
  by_contra hne
  have hXi : X i ∈ P i := (blockChoices_mem_iff.mp hX) i
  have hXj : X j ∈ P j := (blockChoices_mem_iff.mp hX) j
  exact Finset.disjoint_left.mp (hP.2.1 i j hne) hXi
    (by simpa [hij] using hXj)

theorem choiceSet_card_of_partition {p m : ℕ} [NeZero p]
    {S : Finset (ZMod p)}
    {P : Fin m → Finset (ZMod p)} (hP : IsBalancedPartition S P)
    {X : Fin m → ZMod p} (hX : X ∈ blockChoices P) :
    (choiceSet X).card = m := by
  unfold choiceSet
  rw [Finset.card_image_of_injective _ (choice_injective_of_partition hP hX)]
  simp

theorem choiceSet_subset_of_partition {p m : ℕ} [NeZero p]
    {S : Finset (ZMod p)}
    {P : Fin m → Finset (ZMod p)} (hP : IsBalancedPartition S P)
    {X : Fin m → ZMod p} (hX : X ∈ blockChoices P) :
    choiceSet X ⊆ S := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨i,hi,rfl⟩
  exact hP.1 i ((blockChoices_mem_iff.mp hX) i)

theorem choiceSum_eq_subsetSum_choiceSet {p m : ℕ} [NeZero p]
    {S : Finset (ZMod p)}
    {P : Fin m → Finset (ZMod p)} (hP : IsBalancedPartition S P)
    {X : Fin m → ZMod p} (hX : X ∈ blockChoices P) :
    choiceSum X = subsetSum (choiceSet X) := by
  unfold choiceSum subsetSum choiceSet
  rw [Finset.sum_image]
  intro i hi j hj h
  exact choice_injective_of_partition hP hX h

def balancedChoiceMultiplicity (n m : ℕ) : ℕ :=
  ∏ i : Fin m, balancedBlockSize n m i

theorem blockChoices_card {p m : ℕ} [NeZero p]
    (P : Fin m → Finset (ZMod p)) :
    (blockChoices P).card = ∏ i, (P i).card := by
  simp [blockChoices, Finset.card_pi]

theorem blockChoices_card_balanced {p m : ℕ} [NeZero p]
    {S : Finset (ZMod p)} {P : Fin m → Finset (ZMod p)}
    (hP : IsBalancedPartition S P) :
    (blockChoices P).card = balancedChoiceMultiplicity S.card m := by
  rw [blockChoices_card]
  unfold balancedChoiceMultiplicity
  apply Finset.prod_congr rfl
  intro i hi
  exact hP.2.2.2 i

theorem balancedChoiceMultiplicity_pos (n m : ℕ)
    (hm : 0 < m) (hmn : m ≤ n) :
    0 < balancedChoiceMultiplicity n m := by
  unfold balancedChoiceMultiplicity
  apply Finset.prod_pos
  intro i hi
  unfold balancedBlockSize
  have hq : 0 < n / m := Nat.div_pos hmn hm
  split <;> omega

/-- Joint sample space: an ordered balanced partition and one selected point
from each block. -/
def balancedChoiceSpace {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) :
    Finset ((Fin m → Finset (ZMod p)) × (Fin m → ZMod p)) := by
  classical
  exact Finset.univ.filter fun q =>
    q.1 ∈ balancedPartitions S ∧ q.2 ∈ blockChoices q.1

theorem mem_balancedChoiceSpace {p m : ℕ} [NeZero p]
    {S : Finset (ZMod p)}
    {P : Fin m → Finset (ZMod p)}
    {X : Fin m → ZMod p} :
    (P,X) ∈ balancedChoiceSpace S ↔
      P ∈ balancedPartitions S ∧ X ∈ blockChoices P := by
  simp [balancedChoiceSpace]

theorem choiceSet_mem_powersetCard {p m : ℕ} [NeZero p]
    {S : Finset (ZMod p)}
    {P : Fin m → Finset (ZMod p)}
    {X : Fin m → ZMod p}
    (h : (P,X) ∈ balancedChoiceSpace S) :
    choiceSet X ∈ S.powersetCard m := by
  rcases mem_balancedChoiceSpace.mp h with ⟨hPmem,hX⟩
  have hP : IsBalancedPartition S P := by
    simpa [balancedPartitions] using hPmem
  exact Finset.mem_powersetCard.mpr
    ⟨choiceSet_subset_of_partition hP hX,
     choiceSet_card_of_partition hP hX⟩

/-- Conditional point mass of the block-choice sum. -/
def conditionalSumMass {p m : ℕ} [NeZero p]
    (P : Fin m → Finset (ZMod p)) (z : ZMod p) : ℝ :=
  uniformMass (blockChoices P) (fun X => choiceSum X = z)

/-- Average over the balanced-partition sample space. -/
def partitionExpectation {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (F : (Fin m → Finset (ZMod p)) → ℝ) : ℝ :=
  uniformExpectation (balancedPartitions S) F

/-- Probability of an event over the uniformly random balanced partition. -/
def partitionMass {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (E : (Fin m → Finset (ZMod p)) → Prop)
    [DecidablePred E] : ℝ :=
  uniformMass (balancedPartitions S) E

/-- The paper's random-partition quantity `ψ(χ)`. -/
def psi {p m : ℕ} [NeZero p]
    (P : Fin m → Finset (ZMod p)) (χ : ZMod p) : ℝ :=
  ∑ i,
    (1 / ((P i).card : ℝ) ^ 2) *
      ∑ x ∈ P i, ∑ x' ∈ P i,
        zmodNorm (χ * x - χ * x') ^ 2

/-- The deterministic comparison quantity `Ψ(χ)`. -/
def Psi {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (m : ℕ) (χ : ZMod p) : ℝ :=
  (m : ℝ) / (S.card : ℝ) ^ 2 *
    ∑ x ∈ S, ∑ x' ∈ S,
      zmodNorm (χ * x - χ * x') ^ 2

/-- The dyadic low-`ψ` set `A₀`. -/
def A0 {p m : ℕ} [NeZero p]
    (P : Fin m → Finset (ZMod p)) : Finset (ZMod p) :=
  Finset.univ.filter fun χ => psi P χ < 1

/-- The dyadic shell `A_t={χ:t≤ψ(χ)<2t}`. -/
def At {p m : ℕ} [NeZero p]
    (P : Fin m → Finset (ZMod p)) (t : ℕ) : Finset (ZMod p) :=
  Finset.univ.filter fun χ => (t : ℝ) ≤ psi P χ ∧ psi P χ < 2 * t

/-- The deterministic low-energy set `B_t`. -/
def Bset {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (m t : ℕ) : Finset (ZMod p) :=
  Finset.univ.filter fun χ => Psi S m χ ≤ t

/-- Points of `S` within the `8 sqrt(t/m)` ball about `y` after dilation by `χ`. -/
def nearSet {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (m t : ℕ) (χ y : ZMod p) : Finset (ZMod p) :=
  S.filter fun x =>
    zmodNorm (χ * x - y) ≤ 8 * Real.sqrt ((t : ℝ) / m)

/-- The deterministic structured-character set `D_t`. -/
def Dset {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (m t : ℕ) : Finset (ZMod p) :=
  Finset.univ.filter fun χ =>
    χ ≠ 0 ∧ ∃ y : ZMod p, 3 * S.card ≤ 4 * (nearSet S m t χ y).card

/-- There is some positive scale at which `χ` belongs to `D_t`. -/
def HasDTime {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (m : ℕ) (χ : ZMod p) : Prop :=
  ∃ t : ℕ, 0 < t ∧ χ ∈ Dset S m t

/-- The smallest positive scale at which `χ ∈ D_t`, whenever such a scale
exists. This is the scale used in the paper to choose a center independent of
the later value of `t`. -/
def firstDTime {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (m : ℕ) (χ : ZMod p) : ℕ := by
  classical
  by_cases h : HasDTime S m χ
  · exact Nat.find h
  · exact 1

theorem firstDTime_spec {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : ℕ) (χ : ZMod p)
    (h : HasDTime S m χ) :
    0 < firstDTime S m χ ∧
      χ ∈ Dset S m (firstDTime S m χ) := by
  classical
  simp [firstDTime, h, Nat.find_spec h]

theorem firstDTime_le {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m t : ℕ) (χ : ZMod p)
    (ht : 0 < t) (hχ : χ ∈ Dset S m t) :
    firstDTime S m χ ≤ t := by
  classical
  have hex : HasDTime S m χ := ⟨t, ht, hχ⟩
  simp [firstDTime, hex]
  exact Nat.find_min' hex ⟨ht, hχ⟩

theorem nearSet_mono_t {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m t₁ t₂ : ℕ)
    (χ y : ZMod p) (htt : t₁ ≤ t₂) :
    nearSet S m t₁ χ y ⊆ nearSet S m t₂ χ y := by
  intro x hx
  simp only [nearSet, Finset.mem_filter] at hx ⊢
  refine ⟨hx.1, le_trans hx.2 ?_⟩
  gcongr

/-- The paper's center `yχ`, chosen once and for all from the smallest positive
scale at which `χ ∈ D_t`. The formal parameter `t` is intentionally ignored,
so the center is definitionally independent of `t`. -/
def centerAt {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (m : ℕ) (_t : ℕ) (χ : ZMod p) : ZMod p := by
  classical
  by_cases h : HasDTime S m χ
  · have hD :
        χ ∈ Dset S m (firstDTime S m χ) :=
      (firstDTime_spec S m χ h).2
    exact Classical.choose
      ((Finset.mem_filter.1 hD).2.2)
  · exact 0

theorem centerAt_independent_of_t {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m t₁ t₂ : ℕ) (χ : ZMod p) :
    centerAt S m t₁ χ = centerAt S m t₂ χ := by
  rfl

theorem centerAt_spec {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (m t : ℕ) {χ : ZMod p} (ht : 0 < t)
    (hχ : χ ∈ Dset S m t) :
    3 * S.card ≤
      4 * (nearSet S m t χ (centerAt S m t χ)).card := by
  classical
  have hex : HasDTime S m χ := ⟨t, ht, hχ⟩
  have hD :
      χ ∈ Dset S m (firstDTime S m χ) :=
    (firstDTime_spec S m χ hex).2
  have hcenter :
      3 * S.card ≤
        4 * (nearSet S m (firstDTime S m χ) χ
          (centerAt S m t χ)).card := by
    simpa [centerAt, hex] using
      Classical.choose_spec ((Finset.mem_filter.1 hD).2.2)
  have hsubset :
      nearSet S m (firstDTime S m χ) χ (centerAt S m t χ) ⊆
        nearSet S m t χ (centerAt S m t χ) :=
    nearSet_mono_t S m (firstDTime S m χ) t χ
      (centerAt S m t χ) (firstDTime_le S m t χ ht hχ)
  exact le_trans hcenter (Nat.mul_le_mul_left 4 (Finset.card_le_card hsubset))

/-- The enlarged set `J_{χ,t} ⊆ Z_p` used in Lemmas 3.2 and 3.3. -/
def Jset {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (m t : ℕ) (χ : ZMod p) : Finset (ZMod p) :=
  Finset.univ.filter fun x =>
    zmodNorm (χ * x - centerAt S m t χ) ≤
      16 * Real.sqrt ((t : ℝ) / m)

/-- The set `Q_{t,δ}` from Lemma 3.4. -/
def Qset {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (m t : ℕ) (δ : ℝ) : Finset (ZMod p) :=
  Finset.univ.filter fun x =>
    (∑ χ ∈ Bset S m t, zmodNorm (χ * x) ^ 2) <
      δ * (Bset S m t).card

/-- Theorem 1.3 exactly in finite-cardinality probability language. -/
def Theorem13Statement : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (p : ℕ) (hp : p.Prime),
      letI : NeZero p := ⟨hp.ne_zero⟩
      ∀ (S : Finset (ZMod p)), 2 ≤ S.card →
      ∀ (m : ℕ),
        C * Real.log (S.card : ℝ) ≤ (m : ℝ) →
        (m : ℝ) ≤ (1 / 1000 : ℝ) * S.card / Real.log (S.card : ℝ) →
        ∀ z : ZMod p,
          sliceMass S m z ≤
            1 / (p : ℝ) + C / ((S.card : ℝ) * Real.sqrt (m : ℝ))

end

end GrahamRearrangement
