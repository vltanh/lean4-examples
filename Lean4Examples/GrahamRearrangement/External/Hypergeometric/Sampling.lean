import Lean4Examples.GrahamRearrangement.Probability

open scoped BigOperators

namespace GrahamRearrangement.External.Hypergeometric

/-!
# Sampling without replacement

A finite, source-level model of sequential sampling without replacement.
The main result identifies the unordered sample produced by this recursion with
the uniform distribution on `U.powersetCard k`.
-/

noncomputable section

/-- Expectation under k sequential uniform draws without replacement. -/
def withoutReplacementExpectation {α : Type*} [DecidableEq α]
    (U : Finset α) : (k : ℕ) → (List α → ℝ) → ℝ
  | 0, f => f []
  | k + 1, f =>
      uniformExpectation U fun x =>
        withoutReplacementExpectation (U.erase x) k
          (fun xs => f (x :: xs))

/-- Event probability for the recursive without-replacement sampler. -/
def withoutReplacementMass {α : Type*} [DecidableEq α]
    (U : Finset α) (k : ℕ) (E : List α → Prop)
    [DecidablePred E] : ℝ :=
  withoutReplacementExpectation U k
    (fun xs => if E xs then 1 else 0)

theorem withoutReplacementExpectation_zero {α : Type*} [DecidableEq α]
    (U : Finset α) (f : List α → ℝ) :
    withoutReplacementExpectation U 0 f = f [] := rfl

theorem withoutReplacementExpectation_succ {α : Type*} [DecidableEq α]
    (U : Finset α) (k : ℕ) (f : List α → ℝ) :
    withoutReplacementExpectation U (k + 1) f =
      uniformExpectation U fun x =>
        withoutReplacementExpectation (U.erase x) k
          (fun xs => f (x :: xs)) := rfl

theorem withoutReplacementExpectation_mono
    {α : Type*} [DecidableEq α]
    (U : Finset α) (k : ℕ) (f g : List α → ℝ)
    (hfg : ∀ xs, f xs ≤ g xs) :
    withoutReplacementExpectation U k f ≤
      withoutReplacementExpectation U k g := by
  induction k generalizing U f g with
  | zero => simpa [withoutReplacementExpectation] using hfg []
  | succ k ih =>
      rw [withoutReplacementExpectation_succ,
        withoutReplacementExpectation_succ]
      by_cases hU : U.Nonempty
      · apply uniformExpectation_mono U hU
        intro x hx
        exact ih (U.erase x)
          (fun xs => f (x :: xs)) (fun xs => g (x :: xs))
          (fun xs => hfg (x :: xs))
      · simp [uniformExpectation, Finset.not_nonempty_iff_eq_empty.mp hU]

theorem withoutReplacementExpectation_nonneg
    {α : Type*} [DecidableEq α]
    (U : Finset α) (k : ℕ) (f : List α → ℝ)
    (hf : ∀ xs, 0 ≤ f xs) :
    0 ≤ withoutReplacementExpectation U k f := by
  exact le_trans
    (by
      induction k generalizing U with
      | zero => simp [withoutReplacementExpectation]
      | succ k ih =>
          rw [withoutReplacementExpectation_succ]
          unfold uniformExpectation
          positivity)
    (withoutReplacementExpectation_mono U k (fun _ => 0) f
      (fun xs => hf xs))

theorem withoutReplacementExpectation_const
    {α : Type*} [DecidableEq α]
    (U : Finset α) {k : ℕ} (hk : k ≤ U.card) (c : ℝ) :
    withoutReplacementExpectation U k (fun _ => c) = c := by
  induction k generalizing U E with
  | zero => simp [withoutReplacementExpectation]
  | succ k ih =>
      have hU : U.Nonempty := by
        exact Finset.card_pos.mp (lt_of_lt_of_le (Nat.zero_lt_succ k) hk)
      rw [withoutReplacementExpectation_succ]
      have hchild : ∀ x ∈ U, k ≤ (U.erase x).card := by
        intro x hx
        rw [Finset.card_erase_of_mem hx]
        omega
      have heq :
          (fun x => withoutReplacementExpectation (U.erase x) k
              (fun _ => c)) = fun _ => c := by
        funext x
        by_cases hx : x ∈ U
        · exact ih (U.erase x) (hchild x hx)
        · have hcard : U.erase x = U := Finset.erase_eq_of_not_mem hx
          rw [hcard]
          exact ih U (by omega)
      rw [heq]
      exact uniformExpectation_const U hU c

def IsWithoutReplacementSample {α : Type*} [DecidableEq α]
    (U : Finset α) (k : ℕ) (xs : List α) : Prop :=
  xs.length = k ∧ xs.Nodup ∧ ∀ x ∈ xs, x ∈ U

theorem withoutReplacementExpectation_congr_on_samples
    {α : Type*} [DecidableEq α]
    (U : Finset α) (k : ℕ) (f g : List α → ℝ)
    (h :
      ∀ xs, IsWithoutReplacementSample U k xs → f xs = g xs) :
    withoutReplacementExpectation U k f =
      withoutReplacementExpectation U k g := by
  induction k generalizing U f g with
  | zero =>
      have hnil : IsWithoutReplacementSample U 0 [] := by
        simp [IsWithoutReplacementSample]
      simpa [withoutReplacementExpectation] using h [] hnil
  | succ k ih =>
      rw [withoutReplacementExpectation_succ,
        withoutReplacementExpectation_succ]
      apply le_antisymm
      · by_cases hU : U.Nonempty
        · apply uniformExpectation_mono U hU
          intro x hx
          have htail :
              ∀ xs, IsWithoutReplacementSample (U.erase x) k xs →
                f (x::xs) = g (x::xs) := by
            intro xs hxs
            apply h
            rcases hxs with ⟨hlen,hnd,hmem⟩
            have hxnot : x ∉ xs := by
              intro hxin
              have hxerase := hmem x hxin
              exact (Finset.mem_erase.mp hxerase).1 rfl
            refine ⟨by simp [hlen], ?_, ?_⟩
            · exact List.nodup_cons.mpr ⟨hxnot,hnd⟩
            · intro y hy
              simp at hy
              rcases hy with rfl | hy
              · exact hx
              · exact Finset.mem_of_mem_erase (hmem y hy)
          exact (ih (U.erase x)
            (fun xs => f (x::xs)) (fun xs => g (x::xs)) htail).le
        · simp [uniformExpectation, Finset.not_nonempty_iff_eq_empty.mp hU]
      · by_cases hU : U.Nonempty
        · apply uniformExpectation_mono U hU
          intro x hx
          have htail :
              ∀ xs, IsWithoutReplacementSample (U.erase x) k xs →
                g (x::xs) = f (x::xs) := by
            intro xs hxs
            symm
            apply h
            rcases hxs with ⟨hlen,hnd,hmem⟩
            have hxnot : x ∉ xs := by
              intro hxin
              have hxerase := hmem x hxin
              exact (Finset.mem_erase.mp hxerase).1 rfl
            refine ⟨by simp [hlen], ?_, ?_⟩
            · exact List.nodup_cons.mpr ⟨hxnot,hnd⟩
            · intro y hy
              simp at hy
              rcases hy with rfl | hy
              · exact hx
              · exact Finset.mem_of_mem_erase (hmem y hy)
          exact (ih (U.erase x)
            (fun xs => g (x::xs)) (fun xs => f (x::xs)) htail).le
        · simp [uniformExpectation, Finset.not_nonempty_iff_eq_empty.mp hU]

theorem withoutReplacementMass_congr_on_samples
    {α : Type*} [DecidableEq α]
    (U : Finset α) (k : ℕ)
    (E F : List α → Prop) [DecidablePred E] [DecidablePred F]
    (h : ∀ xs, IsWithoutReplacementSample U k xs → (E xs ↔ F xs)) :
    withoutReplacementMass U k E =
      withoutReplacementMass U k F := by
  unfold withoutReplacementMass
  apply withoutReplacementExpectation_congr_on_samples U k
  intro xs hxs
  by_cases hE : E xs <;> by_cases hF : F xs <;>
    simp [hE,hF] at *
  · exact False.elim ((h xs hxs).1 hE hF)
  · exact False.elim ((h xs hxs).2 hF hE)

/-- The joint space obtained by first choosing x in U and then a k-subset of
U\{x}. -/
def headTailSpace {α : Type*} [DecidableEq α]
    (U : Finset α) (k : ℕ) : Finset (α × Finset α) :=
  U.biUnion fun x =>
    ((U.erase x).powersetCard k).image fun R => (x, R)

theorem mem_headTailSpace {α : Type*} [DecidableEq α]
    {U : Finset α} {k : ℕ} {x : α} {R : Finset α} :
    (x,R) ∈ headTailSpace U k ↔
      x ∈ U ∧ R ∈ (U.erase x).powersetCard k := by
  classical
  constructor
  · intro h
    simp [headTailSpace] at h
    exact h
  · rintro ⟨hx,hR⟩
    simp [headTailSpace,hx,hR]

def headTailSet {α : Type*} [DecidableEq α]
    (q : α × Finset α) : Finset α :=
  insert q.1 q.2

theorem headTailSet_mem_powersetCard
    {α : Type*} [DecidableEq α]
    {U : Finset α} {k : ℕ} {q : α × Finset α}
    (hq : q ∈ headTailSpace U k) :
    headTailSet q ∈ U.powersetCard (k + 1) := by
  rcases mem_headTailSpace.mp hq with ⟨hx,hR⟩
  rcases Finset.mem_powersetCard.mp hR with ⟨hRU,hcard⟩
  have hxR : q.1 ∉ q.2 := by
    intro hxmem
    have := hRU hxmem
    exact (Finset.mem_erase.mp this).1 rfl
  apply Finset.mem_powersetCard.mpr
  constructor
  · intro y hy
    simp [headTailSet] at hy
    rcases hy with rfl | hy
    · exact hx
    · exact Finset.mem_of_mem_erase (hRU hy)
  · simp [headTailSet,hxR,hcard]

/-- A fixed (k+1)-subset has exactly one head-tail representation for each of
its k+1 elements. -/
theorem headTail_fiber_card
    {α : Type*} [DecidableEq α]
    (U : Finset α) (k : ℕ)
    {T : Finset α} (hT : T ∈ U.powersetCard (k + 1)) :
    ((headTailSpace U k).filter fun q => headTailSet q = T).card =
      k + 1 := by
  classical
  let A :=
    (headTailSpace U k).filter fun q => headTailSet q = T
  let f : {q // q ∈ A} → {x // x ∈ T} :=
    fun q => ⟨q.1.1, by
      have hqeq := (Finset.mem_filter.mp q.2).2
      rw [← hqeq]
      simp [headTailSet]⟩
  have hinj : Function.Injective f := by
    intro q r h
    apply Subtype.ext
    rcases q with ⟨⟨x,R⟩,hq⟩
    rcases r with ⟨⟨y,Q⟩,hr⟩
    simp only [f, Subtype.mk.injEq] at h
    subst y
    have hRq := (Finset.mem_filter.mp hq).2
    have hQr := (Finset.mem_filter.mp hr).2
    apply Prod.ext
    · rfl
    · have hxR :
          x ∉ R := by
        rcases mem_headTailSpace.mp (Finset.mem_filter.mp hq).1
          with ⟨_,hRmem⟩
        intro hx
        exact (Finset.mem_erase.mp
          ((Finset.mem_powersetCard.mp hRmem).1 hx)).1 rfl
      have hxQ :
          x ∉ Q := by
        rcases mem_headTailSpace.mp (Finset.mem_filter.mp hr).1
          with ⟨_,hQmem⟩
        intro hx
        exact (Finset.mem_erase.mp
          ((Finset.mem_powersetCard.mp hQmem).1 hx)).1 rfl
      have : insert x R = insert x Q := hRq.trans hQr.symm
      simpa [Finset.insert_eq_self, hxR, hxQ] using
        congrArg (Finset.erase · x) this
  have hsurj : Function.Surjective f := by
    intro x
    let R := T.erase x.1
    have hTU := (Finset.mem_powersetCard.mp hT).1
    have hxU : x.1 ∈ U := hTU x.2
    have hRmem : R ∈ (U.erase x.1).powersetCard k := by
      apply Finset.mem_powersetCard.mpr
      constructor
      · intro y hy
        rcases Finset.mem_erase.mp hy with ⟨hyx,hyT⟩
        exact Finset.mem_erase.mpr ⟨hyx,hTU hyT⟩
      · rw [Finset.card_erase_of_mem x.2,
          (Finset.mem_powersetCard.mp hT).2]
        omega
    refine ⟨⟨(x.1,R),?_⟩,?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · exact mem_headTailSpace.mpr ⟨hxU,hRmem⟩
      · simp [headTailSet,R,x.2]
    · rfl
  have hcard := Fintype.card_congr (Equiv.ofBijective f ⟨hinj,hsurj⟩)
  simpa [A,(Finset.mem_powersetCard.mp hT).2] using hcard

theorem headTailSpace_card
    {α : Type*} [DecidableEq α]
    (U : Finset α) (k : ℕ) (hk : k + 1 ≤ U.card) :
    (headTailSpace U k).card =
      (k + 1) * (U.powersetCard (k + 1)).card := by
  rw [card_eq_sum_card_fibers
    (headTailSpace U k) (U.powersetCard (k+1)) headTailSet
    (fun q hq => headTailSet_mem_powersetCard hq)]
  simp_rw [headTail_fiber_card U k]
  simp [mul_comm]

theorem headTail_event_card
    {α : Type*} [DecidableEq α]
    (U : Finset α) (k : ℕ)
    (E : Finset α → Prop) [DecidablePred E] :
    ((headTailSpace U k).filter fun q => E (headTailSet q)).card =
      (k + 1) * ((U.powersetCard (k + 1)).filter E).card := by
  classical
  rw [card_eq_sum_card_fibers
    ((headTailSpace U k).filter fun q => E (headTailSet q))
    ((U.powersetCard (k+1)).filter E) headTailSet
    (by
      intro q hq
      rcases Finset.mem_filter.mp hq with ⟨hspace,hE⟩
      exact Finset.mem_filter.mpr
        ⟨headTailSet_mem_powersetCard hspace,hE⟩)]
  calc
    _ = ∑ T ∈ (U.powersetCard (k+1)).filter E, k + 1 := by
      apply Finset.sum_congr rfl
      intro T hT
      exact headTail_fiber_card U k (Finset.mem_filter.mp hT).1
    _ = _ := by simp [mul_comm]

/-- Uniform (k+1)-subset sampling can be exposed by one uniform head followed
by a uniform k-subset of the erased ground set. -/
theorem uniformSubset_head_tail
    {α : Type*} [DecidableEq α]
    (U : Finset α) (k : ℕ) (hk : k + 1 ≤ U.card)
    (E : Finset α → Prop) [DecidablePred E] :
    uniformMass (U.powersetCard (k + 1)) E =
      uniformExpectation U fun x =>
        uniformMass ((U.erase x).powersetCard k)
          (fun R => E (insert x R)) := by
  classical
  have hU : U.Nonempty := Finset.card_pos.mp
    (lt_of_lt_of_le (Nat.zero_lt_succ k) hk)
  unfold uniformMass uniformExpectation
  have hinnerCard : ∀ x ∈ U,
      ((U.erase x).powersetCard k).card =
        Nat.choose (U.card - 1) k := by
    intro x hx
    rw [Finset.card_powersetCard,
      Finset.card_erase_of_mem hx]
  have hsum :
      (∑ x ∈ U,
        (((U.erase x).powersetCard k).filter
          (fun R => E (insert x R))).card) =
      ((headTailSpace U k).filter
        (fun q => E (headTailSet q))).card := by
    classical
    unfold headTailSpace
    rw [Finset.sum_biUnion]
    · apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.card_image_iff.mpr]
      · rfl
      · intro R hR Q hQ h
        exact Prod.mk.inj_iff.mp h |>.2
    · intro x hx y hy hxy
      rw [Finset.disjoint_left]
      intro q hqx hqy
      rcases Finset.mem_image.mp hqx with ⟨R,hR,rfl⟩
      rcases Finset.mem_image.mp hqy with ⟨Q,hQ,hEq⟩
      exact hxy (Prod.mk.inj_iff.mp hEq).1
  have hchoose :
      U.card * Nat.choose (U.card - 1) k =
        (k + 1) * Nat.choose U.card (k + 1) := by
    have hpred : U.card - 1 + 1 = U.card := by omega
    have h := Nat.add_one_mul_choose_eq (U.card - 1) k
    rw [hpred] at h
    simpa [mul_comm] using h
  simp_rw [hinnerCard]
  rw [← Finset.sum_div]
  rw [hsum,headTail_event_card U k E]
  rw [Finset.card_powersetCard,Finset.card_powersetCard]
  have hdenU : (0 : ℝ) < U.card := by exact_mod_cast hU.card_pos
  have hchild : 0 < Nat.choose (U.card - 1) k := by
    exact Nat.choose_pos (by omega)
  have hdenChild : (0 : ℝ) < Nat.choose (U.card - 1) k := by
    exact_mod_cast hchild
  field_simp
  exact_mod_cast hchoose

theorem withoutReplacementMass_toFinset
    {α : Type*} [DecidableEq α]
    (U : Finset α) (k : ℕ) (hk : k ≤ U.card)
    (E : Finset α → Prop) [DecidablePred E] :
    withoutReplacementMass U k (fun xs => E xs.toFinset) =
      uniformMass (U.powersetCard k) E := by
  induction k generalizing U with
  | zero =>
      simp [withoutReplacementMass,withoutReplacementExpectation,
        uniformMass,subsetSum]
  | succ k ih =>
      rw [withoutReplacementMass,withoutReplacementExpectation_succ]
      simp only [List.toFinset_cons]
      have hchild : ∀ x ∈ U, k ≤ (U.erase x).card := by
        intro x hx
        rw [Finset.card_erase_of_mem hx]
        omega
      have hrewrite :
          (fun x =>
            withoutReplacementExpectation (U.erase x) k
              (fun xs => if E (insert x xs.toFinset) then 1 else 0)) =
          (fun x =>
            uniformMass ((U.erase x).powersetCard k)
              (fun R => E (insert x R))) := by
        funext x
        by_cases hx : x ∈ U
        · simpa [withoutReplacementMass] using
            ih (U.erase x) (hchild x hx)
              (fun R => E (insert x R))
        · have hzero : U.erase x = U := Finset.erase_eq_of_not_mem hx
          rw [hzero]
          simpa [withoutReplacementMass] using
            ih U (by omega) (fun R => E (insert x R))
      rw [hrewrite]
      symm
      exact uniformSubset_head_tail U k hk E

end

end GrahamRearrangement.External.Hypergeometric
