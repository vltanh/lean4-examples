import Lean4Examples.GrahamRearrangement.Combinatorial.Definitions

open scoped BigOperators Pointwise

namespace GrahamRearrangement.Section4External

/-!
# Finite sampling and tuple bookkeeping for Section 4

Everything in this file is proved from finite cardinalities.  No Section 4
argument is axiomatized.
-/

noncomputable section

def extendPairSpace {α : Type*} [DecidableEq α]
    (S : Finset α) (m : ℕ) : Finset (Finset α × α) :=
  ((S.powersetCard (m - 1)).product S).filter fun q => q.2 ∉ q.1

theorem mem_extendPairSpace {α : Type*} [DecidableEq α]
    {S : Finset α} {m : ℕ} {R : Finset α} {x : α} :
    (R,x) ∈ extendPairSpace S m ↔
      R ∈ S.powersetCard (m - 1) ∧ x ∈ S \ R := by
  simp [extendPairSpace]

def extendPairMap {α : Type*} [DecidableEq α]
    (q : Finset α × α) : Finset α :=
  insert q.2 q.1

theorem extendPairMap_mem {α : Type*} [DecidableEq α]
    {S : Finset α} {m : ℕ} (hm : 0 < m)
    {q : Finset α × α} (hq : q ∈ extendPairSpace S m) :
    extendPairMap q ∈ S.powersetCard m := by
  rcases (mem_extendPairSpace.mp hq) with ⟨hR, hx⟩
  rcases Finset.mem_powersetCard.mp hR with ⟨hRS, hcard⟩
  rcases Finset.mem_sdiff.mp hx with ⟨hxS, hxR⟩
  apply Finset.mem_powersetCard.mpr
  constructor
  · intro y hy
    simp [extendPairMap] at hy
    rcases hy with rfl | hy
    · exact hxS
    · exact hRS hy
  · simp [extendPairMap, hxR, hcard, hm]

/-- Every m-subset has exactly m extension-pair representations. -/
theorem extendPair_fiber_card {α : Type*} [DecidableEq α]
    (S : Finset α) {m : ℕ} (hm : 0 < m)
    {T : Finset α} (hT : T ∈ S.powersetCard m) :
    ((extendPairSpace S m).filter fun q => extendPairMap q = T).card = m := by
  classical
  let f : {q // q ∈ (extendPairSpace S m).filter
      (fun q => extendPairMap q = T)} ≃ {x // x ∈ T} :=
    { toFun := fun q => ⟨q.1.2, by
        have hmap := (Finset.mem_filter.mp q.2).2
        rw [← hmap]
        simp [extendPairMap]⟩
      invFun := fun x => ⟨(T.erase x, x), by
        apply Finset.mem_filter.mpr
        constructor
        · apply mem_extendPairSpace.mpr
          have hT' := Finset.mem_powersetCard.mp hT
          constructor
          · apply Finset.mem_powersetCard.mpr
            constructor
            · exact (Finset.erase_subset _ _).trans hT'.1
            · rw [Finset.card_erase_of_mem x.2, hT'.2]
              omega
          · exact Finset.mem_sdiff.mpr
              ⟨hT'.1 x.2, Finset.not_mem_erase _ _⟩
        · simp [extendPairMap, x.2]
      left_inv := by
        intro q
        apply Subtype.ext
        rcases q with ⟨⟨R,x⟩, hq⟩
        simp only
        have hmem := (mem_extendPairSpace.mp (Finset.mem_filter.mp hq).1).2
        have hmap := (Finset.mem_filter.mp hq).2
        simp [extendPairMap] at hmap
        apply Prod.ext
        · rw [← hmap]
          simp [hmem.2]
        · rfl
      right_inv := by
        intro x
        apply Subtype.ext
        simp }
  have hc := Fintype.card_congr f
  simpa [Finset.card_attach, (Finset.mem_powersetCard.mp hT).2] using hc

theorem extendPair_event_card {α : Type*} [DecidableEq α]
    (S : Finset α) {m : ℕ} (hm : 0 < m)
    (E : Finset α → Prop) [DecidablePred E] :
    ((extendPairSpace S m).filter fun q => E (extendPairMap q)).card =
      m * ((S.powersetCard m).filter E).card := by
  classical
  calc
    ((extendPairSpace S m).filter fun q => E (extendPairMap q)).card
      = ∑ T ∈ (S.powersetCard m).filter E,
          ((extendPairSpace S m).filter
            fun q => extendPairMap q = T).card := by
          apply Finset.card_eq_sum_card_fiberwise
          · intro q hq
            exact extendPairMap_mem hm (Finset.mem_filter.mp hq).1
          · intro q hq
            exact (Finset.mem_filter.mp hq).2
    _ = ∑ _T ∈ (S.powersetCard m).filter E, m := by
          apply Finset.sum_congr rfl
          intro T hT
          exact extendPair_fiber_card S hm (Finset.mem_filter.mp hT).1
    _ = m * ((S.powersetCard m).filter E).card := by simp [mul_comm]

theorem extendPairSpace_card {α : Type*} [DecidableEq α]
    (S : Finset α) {m : ℕ} (hm : 0 < m) :
    (extendPairSpace S m).card = m * (S.powersetCard m).card := by
  simpa using extendPair_event_card S hm (fun _ => True)

/-- A uniform m-subset can be sampled by first taking a uniform (m-1)-subset
and then one uniform point of its complement. -/
theorem uniformSubset_twoStage {α : Type*} [DecidableEq α]
    (S : Finset α) (m : ℕ) (hm : 0 < m) (hmS : m ≤ S.card)
    (E : Finset α → Prop) [DecidablePred E] :
    uniformMass (S.powersetCard m) E =
      uniformExpectation (S.powersetCard (m - 1))
        (fun R =>
          uniformMass (S \ R) (fun x => E (insert x R))) := by
  classical
  have houter := powersetCard_nonempty S (show m - 1 ≤ S.card by omega)
  have hcomp : ∀ R ∈ S.powersetCard (m - 1),
      (S \ R).card = S.card - m + 1 := by
    intro R hR
    rw [card_sdiff_of_mem_powersetCard hR]
    omega
  have hpairMass :
      uniformMass (extendPairSpace S m)
        (fun q => E (extendPairMap q)) =
      uniformMass (S.powersetCard m) E := by
    unfold uniformMass
    rw [extendPair_event_card S hm E, extendPairSpace_card S hm]
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    field_simp
    ring
  rw [← hpairMass]
  unfold uniformExpectation uniformMass extendPairSpace
  rw [Finset.sum_div]
  have hconst :
      ∀ R ∈ S.powersetCard (m - 1),
        ((S \ R).card : ℝ) = S.card - m + 1 := by
    intro R hR
    exact_mod_cast hcomp R hR
  simp_rw [hconst]
  field_simp
  ring

def splitPairSpace {α : Type*} [DecidableEq α]
    (S : Finset α) (m₁ m₂ : ℕ) :
    Finset (Finset α × Finset α) :=
  ((S.powersetCard m₁).product (S.powersetCard m₂)).filter
    fun q => Disjoint q.1 q.2

def splitPairMap {α : Type*} [DecidableEq α]
    (q : Finset α × Finset α) : Finset α :=
  q.1 ∪ q.2

theorem splitPairMap_mem {α : Type*} [DecidableEq α]
    {S : Finset α} {m₁ m₂ : ℕ}
    {q : Finset α × Finset α}
    (hq : q ∈ splitPairSpace S m₁ m₂) :
    splitPairMap q ∈ S.powersetCard (m₁ + m₂) := by
  rcases Finset.mem_filter.mp hq with ⟨hqmem, hdisj⟩
  rcases Finset.mem_product.mp hqmem with ⟨h1,h2⟩
  rcases Finset.mem_powersetCard.mp h1 with ⟨h1S,hc1⟩
  rcases Finset.mem_powersetCard.mp h2 with ⟨h2S,hc2⟩
  apply Finset.mem_powersetCard.mpr
  constructor
  · exact Finset.union_subset h1S h2S
  · rw [splitPairMap, Finset.card_union_of_disjoint hdisj, hc1, hc2]

/-- A fixed (m₁+m₂)-subset has choose(m₁+m₂,m₁) ordered disjoint decompositions. -/
theorem splitPair_fiber_card {α : Type*} [DecidableEq α]
    (S : Finset α) (m₁ m₂ : ℕ)
    {T : Finset α} (hT : T ∈ S.powersetCard (m₁ + m₂)) :
    ((splitPairSpace S m₁ m₂).filter
      fun q => splitPairMap q = T).card =
      Nat.choose (m₁ + m₂) m₁ := by
  classical
  let f :
      {q // q ∈ (splitPairSpace S m₁ m₂).filter
        (fun q => splitPairMap q = T)} ≃
      {R // R ∈ T.powersetCard m₁} :=
    { toFun := fun q => ⟨q.1.1, by
        rcases Finset.mem_filter.mp q.2 with ⟨hq,_⟩
        rcases Finset.mem_filter.mp hq with ⟨hprod,_⟩
        rcases Finset.mem_product.mp hprod with ⟨h1,_⟩
        apply Finset.mem_powersetCard.mpr
        refine ⟨?_, (Finset.mem_powersetCard.mp h1).2⟩
        intro x hx
        have hmap := (Finset.mem_filter.mp q.2).2
        rw [← hmap]
        exact Finset.mem_union_left _ hx⟩
      invFun := fun R => ⟨(R, T \ R), by
        apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_filter.mpr
          constructor
          · apply Finset.mem_product.mpr
            constructor
            · exact Finset.mem_powersetCard.mpr
                ⟨(Finset.mem_powersetCard.mp R.2).1.trans
                  (Finset.mem_powersetCard.mp hT).1,
                 (Finset.mem_powersetCard.mp R.2).2⟩
            · apply Finset.mem_powersetCard.mpr
              constructor
              · exact Finset.sdiff_subset.trans
                  (Finset.mem_powersetCard.mp hT).1
              · rw [Finset.card_sdiff
                  (Finset.mem_powersetCard.mp R.2).1,
                  (Finset.mem_powersetCard.mp hT).2,
                  (Finset.mem_powersetCard.mp R.2).2]
                omega
          · exact Finset.disjoint_sdiff_right
        · simp [splitPairMap,
            (Finset.mem_powersetCard.mp R.2).1]
      left_inv := by
        intro q
        apply Subtype.ext
        rcases q with ⟨⟨R₁,R₂⟩, hq⟩
        have hdisj := (Finset.mem_filter.mp
          (Finset.mem_filter.mp hq).1).2
        have hmap := (Finset.mem_filter.mp hq).2
        apply Prod.ext
        · rfl
        · rw [← hmap]
          exact (Finset.sdiff_eq_right.mpr
            (Finset.disjoint_left.mp hdisj)).symm
      right_inv := by intro R; apply Subtype.ext; rfl }
  have hc := Fintype.card_congr f
  simpa [Finset.card_powersetCard] using hc

theorem splitPair_event_card {α : Type*} [DecidableEq α]
    (S : Finset α) (m₁ m₂ : ℕ)
    (E : Finset α → Prop) [DecidablePred E] :
    ((splitPairSpace S m₁ m₂).filter
      fun q => E (splitPairMap q)).card =
      Nat.choose (m₁ + m₂) m₁ *
        ((S.powersetCard (m₁ + m₂)).filter E).card := by
  classical
  calc
    _ = ∑ T ∈ (S.powersetCard (m₁ + m₂)).filter E,
          ((splitPairSpace S m₁ m₂).filter
            fun q => splitPairMap q = T).card := by
          apply Finset.card_eq_sum_card_fiberwise
          · intro q hq
            exact splitPairMap_mem (Finset.mem_filter.mp hq).1
          · intro q hq
            exact (Finset.mem_filter.mp hq).2
    _ = ∑ _T ∈ (S.powersetCard (m₁ + m₂)).filter E,
          Nat.choose (m₁ + m₂) m₁ := by
          apply Finset.sum_congr rfl
          intro T hT
          exact splitPair_fiber_card S m₁ m₂
            (Finset.mem_filter.mp hT).1
    _ = _ := by simp [mul_comm]

/-- A uniform (m₁+m₂)-subset can be sampled in two uniform stages. -/
theorem uniformSubset_split {α : Type*} [DecidableEq α]
    (S : Finset α) (m₁ m₂ : ℕ)
    (hle : m₁ + m₂ ≤ S.card)
    (E : Finset α → Prop) [DecidablePred E] :
    uniformMass (S.powersetCard (m₁ + m₂)) E =
      uniformExpectation (S.powersetCard m₁)
        (fun R₁ =>
          uniformMass ((S \ R₁).powersetCard m₂)
            (fun R₂ => E (R₁ ∪ R₂))) := by
  classical
  have houter := powersetCard_nonempty S (le_trans (Nat.le_add_right _ _) hle)
  have hinnerCard : ∀ R₁ ∈ S.powersetCard m₁,
      ((S \ R₁).powersetCard m₂).card =
        Nat.choose (S.card - m₁) m₂ := by
    intro R₁ hR₁
    rw [Finset.card_powersetCard,
      card_sdiff_of_mem_powersetCard hR₁]
  have hpair :
      uniformMass (splitPairSpace S m₁ m₂)
        (fun q => E (splitPairMap q)) =
      uniformMass (S.powersetCard (m₁ + m₂)) E := by
    unfold uniformMass
    rw [splitPair_event_card S m₁ m₂ E,
      splitPair_event_card S m₁ m₂ (fun _ => True)]
    field_simp
    ring
  rw [← hpair]
  unfold uniformExpectation uniformMass splitPairSpace
  simp_rw [hinnerCard]
  field_simp
  ring

/-- Pigeonhole for the k+1 consecutive gaps of an increasing size tuple. -/
theorem exists_large_chain_gap {k n : ℕ} (m : Fin k → ℕ)
    (hm : IsChainSizeTuple n m) :
    ∃ j : Fin (k + 1),
      (n : ℝ) / (k + 1 : ℝ) ≤ chainGap n m j := by
  classical
  have hsum :
      ∑ j : Fin (k + 1), chainGap n m j = n := by
    unfold chainGap
    exact Fin.sum_consecutive_sub_eq
      (fun i : Fin (k + 2) => extendedSize n m i.val)
  by_contra h
  push_neg at h
  have hlt :
      (∑ j : Fin (k + 1), (chainGap n m j : ℝ)) <
        ∑ _j : Fin (k + 1), (n : ℝ) / (k + 1 : ℝ) := by
    exact Finset.sum_lt_sum (fun j _ => h j)
      (Finset.univ_nonempty)
  simp at hlt
  exact (lt_irrefl (n : ℝ)) (by
    simpa [hsum] using hlt)

/-- Equation (4.1)'s positive-kernel induction, proved by induction on h. -/
theorem prefixKernelSum_le_pow (n h : ℕ) (w : ℕ → ℝ) (B : ℝ)
    (hw : ∀ d, 0 ≤ w d)
    (hrow : ∀ a < n,
      (∑ d ∈ Finset.Icc 1 (n - a), w d) ≤ B) :
    prefixKernelSum n h w ≤ B ^ h := by
  induction h with
  | zero =>
      simp [prefixKernelSum, chainSizeTuples]
  | succ h ih =>
      rw [prefixKernelSum_succ]
      calc
        _ ≤ prefixKernelSum n h w * B := by
          apply Finset.sum_le_sum
          intro m hm
          have hlast : extendedSize n m h < n :=
            prefix_tuple_last_lt n h m hm
          have := hrow (extendedSize n m h) hlast
          positivity
        _ ≤ B ^ h * B := by
          gcongr
        _ = B ^ (h + 1) := by rw [pow_succ]

/-- Omitted-gap factorization used after (4.1). -/
theorem omittedKernelSum_le_prefix_mul (n k : ℕ) (w : ℕ → ℝ)
    (hw : ∀ d, 0 ≤ w d) (j : Fin (k + 1)) :
    omittedKernelSum n k w j ≤
      prefixKernelSum n j.val w *
        prefixKernelSum n (k - j.val) w := by
  classical
  unfold omittedKernelSum
  apply Finset.sum_le_sum_of_injOn
    (f := fun m =>
      (leftPrefixTuple m j, reverseRightTuple n m j))
  · intro m hm
    exact Finset.mem_product.mpr
      ⟨leftPrefixTuple_mem m hm j,
       reverseRightTuple_mem n m hm j⟩
  · intro m hm m' hm' heq
    exact fullTuple_eq_of_left_reverseRight_eq n m m' j heq
  · intro m hm
    rw [omitted_product_split n k w m j]
    rfl
  · intro q hq hnot
    positivity

end

end GrahamRearrangement.Section4External
