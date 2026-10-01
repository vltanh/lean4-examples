import Lean4Examples.GrahamRearrangement.Rearrangement.Lemma53

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Deterministic Section 5 repair

The descending greedy construction from the proof of Theorem 1.2.
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

/-- The 5D possible choices {b+1,...,b+5D}. -/
def repairWindow {n : ℕ} (b : Fin n) (D : ℕ) :
    Finset (Fin n) :=
  (forwardWindow b (5 * D)).erase b

theorem mem_repairWindow {n D : ℕ} {b y : Fin n} :
    y ∈ repairWindow b D ↔
      paperPos b < paperPos y ∧
        paperPos y ≤ paperPos b + 5 * D := by
  simp [repairWindow, forwardWindow, paperPos]
  omega

theorem card_repairWindow {n D : ℕ} (b : Fin n)
    (hfit : paperPos b + 5 * D ≤ n) :
    (repairWindow b D).card = 5 * D := by
  have hfit' : b.val + 5 * D < n := by
    simp [paperPos] at hfit
    omega
  have hcard :=
    card_forwardWindow_eq b (5 * D) hfit'
  have hb : b ∈ forwardWindow b (5 * D) := by
    simp [forwardWindow]
  unfold repairWindow
  rw [Finset.card_erase_of_mem hb, hcard]
  omega

def usedSeconds {n : ℕ}
    (P : Finset (Fin n × Fin n)) : Finset (Fin n) :=
  P.image Prod.snd

def ZeroRightInvariant {n p D : ℕ}
    (σ : Fin n → ZMod p)
    (P : Finset (Fin n × Fin n))
    (R : Finset (Fin n)) : Prop :=
  ∀ a t : Fin n,
    2 ≤ paperPos a → paperPos a < paperPos t →
    indexedIntervalSum
        (applyPositionPerm σ (collectionPerm P)) a t = 0 →
      t ∈ R

/-- State invariant for the descending repair. -/
structure RepairState {n p D : ℕ}
    (σ : Fin n → ZMod p)
    (B R : Finset (Fin n))
    (P : Finset (Fin n × Fin n)) : Prop where
  admissible : IsAdmissibleCollection D P
  remaining_subset : R ⊆ B
  pair_data :
    ∀ q ∈ P,
      q.1 ∈ B ∧ q.1 ∉ R ∧ q.2 ∉ B
  processed_above :
    ∀ q ∈ P, ∀ r ∈ R,
      paperPos r < paperPos q.1
  zero_right : ZeroRightInvariant σ P R

theorem empty_repair_state {n p D : ℕ}
    (σ : Fin n → ZMod p)
    (B : Finset (Fin n)) :
    RepairState σ B B ∅ := by
  refine ⟨?_, by intro x hx; exact hx, ?_, ?_, ?_⟩
  · constructor <;> simp
  · simp
  · simp
  · intro a t ha hat hz
    apply mem_badRightEndpoints_iff.2
    exact ⟨a, ha, hat, by
      simpa [collectionPerm, swapsPermList, applyPositionPerm] using hz⟩

theorem collectionPerm_fixes_of_support_above
    {n D : ℕ} {P : Finset (Fin n × Fin n)}
    (hP : IsAdmissibleCollection D P)
    {b : Fin n}
    (habove : ∀ q ∈ P, paperPos b < paperPos q.1) :
    FixedThrough b (collectionPerm P) := by
  intro i hi
  unfold collectionPerm
  induction P.toList with
  | nil => simp [swapsPermList]
  | cons q qs ih =>
      have hqP : q ∈ P := by
        simpa using List.mem_toFinset.1 (by simp)
      have hqb : paperPos b < paperPos q.1 := habove q hqP
      have hq2 := (hP.2 q hqP).1
      have hi1 : i ≠ q.1 := by
        intro h; subst h; omega
      have hi2 : i ≠ q.2 := by
        intro h; subst h; omega
      simp [swapsPermList, Equiv.swap_apply_of_ne_of_ne hi1 hi2, ih]

theorem usedSeconds_near_card_le
    {n p D : ℕ}
    {σ : Fin n → ZMod p}
    {B R : Finset (Fin n)}
    {P : Finset (Fin n × Fin n)}
    (hstate : RepairState σ B R P)
    (hlocal : ∀ z : Fin n,
      (B ∩ symmetricWindow z (10 * D)).card ≤ D)
    {b : Fin n} (hbR : b ∈ R) :
    ((repairWindow b D) ∩ usedSeconds P).card ≤ D := by
  let Q :=
    P.filter fun q => q.2 ∈ repairWindow b D
  have hsecond :
      ((repairWindow b D) ∩ usedSeconds P).card = Q.card := by
    unfold usedSeconds Q
    have hinj : Set.InjOn Prod.snd (P : Set (Fin n × Fin n)) := by
      intro q hq r hr heq
      by_contra hqr
      have hd := hstate.admissible.1 hq hr hqr
      exact hd.2.2.2 heq
    rw [← Finset.card_image_of_injOn (s := Q)
      (hinj.mono (Finset.coe_filter_subset _ _))]
    congr 1
    ext y
    simp [Q]
  have hfirst :
      Q.card ≤ (B ∩ symmetricWindow b (10 * D)).card := by
    let f : Fin n × Fin n → Fin n := Prod.fst
    apply Finset.card_le_of_injOn f
    · intro q hq
      have hqP : q ∈ P := (Finset.mem_filter.1 hq).1
      have hqC : q.2 ∈ repairWindow b D :=
        (Finset.mem_filter.1 hq).2
      have hqB := (hstate.pair_data q hqP).1
      have hqb := hstate.processed_above q hqP b hbR
      have hlen := (hstate.admissible.2 q hqP).2
      apply Finset.mem_inter.2
      refine ⟨hqB, ?_⟩
      simp [symmetricWindow, Nat.dist_eq]
      have hqy := (mem_repairWindow.mp hqC)
      simp [paperPos] at hqb hlen hqy ⊢
      omega
    · intro q hq r hr h
      apply Prod.ext
      · exact h
      · have hqP := (Finset.mem_filter.1 hq).1
        have hrP := (Finset.mem_filter.1 hr).1
        by_contra h2
        have hqr : q ≠ r := by
          intro he
          exact h2 (congrArg Prod.snd he)
        have hd := hstate.admissible.1 hqP hrP hqr
        exact hd.2.1 h
  rw [hsecond]
  exact le_trans hfirst (hlocal b)

theorem badEndpoints_in_repairWindow_le
    {n p D : ℕ} {σ : Fin n → ZMod p}
    (B : Finset (Fin n))
    (hB : B = badRightEndpoints σ)
    (hlocal : ∀ z : Fin n,
      (B ∩ symmetricWindow z (10 * D)).card ≤ D)
    (b : Fin n) :
    ((repairWindow b D) ∩ B).card ≤ D := by
  apply le_trans ?_ (hlocal b)
  apply Finset.card_le_card
  intro y hy
  rcases Finset.mem_inter.1 hy with ⟨hyC, hyB⟩
  apply Finset.mem_inter.2
  refine ⟨hyB, ?_⟩
  have hyw := mem_repairWindow.mp hyC
  simp [symmetricWindow, Nat.dist_eq, paperPos] at *
  omega

theorem blocked_in_repairWindow_le
    {n p D : ℕ}
    (σ : Fin n → ZMod p) (b : Fin n)
    (π : Equiv.Perm (Fin n))
    (hblocked :
      (blockedCandidates D σ b π).card < 2 * D) :
    ((repairWindow b D) ∩
      blockedCandidates D σ b π).card ≤ 2 * D := by
  calc
    _ ≤ (blockedCandidates D σ b π).card :=
      Finset.card_inter_le_right
    _ ≤ 2 * D := Nat.le_of_lt_succ (lt_succ_of_lt hblocked)

theorem swap_preserves_interval_of_membership_iff
    {n p : ℕ} (τ : Fin n → ZMod p)
    (b y a t : Fin n)
    (hbt :
      (b ∈ indexInterval a t ↔ y ∈ indexInterval a t)) :
    indexedIntervalSum
        (applyPositionPerm τ (Equiv.swap b y)) a t =
      indexedIntervalSum τ a t := by
  rw [← indexSetSum_indexInterval,
    indexSetSum_applyPositionPerm_image,
    indexSetSum_indexInterval]
  congr 1
  ext i
  by_cases hi : i = b
  · subst i
    simp [hbt]
  · by_cases hi' : i = y
    · subst i
      simp [hbt]
    · simp [Equiv.swap_apply_of_ne_of_ne hi hi']

theorem not_blocked_zero_preserves
    {n p D : ℕ}
    (σ : Fin n → ZMod p)
    (π : Equiv.Perm (Fin n))
    (b y a t : Fin n)
    (hy : y ∈ repairWindow b D)
    (ha2 : 2 ≤ paperPos a)
    (hat : paperPos a < paperPos t)
    (hnot : ¬ IsBlockedAt D σ b π y)
    (hz :
      indexedIntervalSum
        (applyPositionPerm
          (applyPositionPerm σ π) (Equiv.swap b y))
        a t = 0) :
    indexedIntervalSum (applyPositionPerm σ π) a t = 0 ∧ t ≠ b := by
  have hyw := mem_repairWindow.mp hy
  have hsame :
      (b ∈ indexInterval a t ↔ y ∈ indexInterval a t) := by
    by_contra hiff
    have hx : (b ∈ indexInterval a t) ≠
        (y ∈ indexInterval a t) := hiff
    have hcross :
        (paperPos b < paperPos a ∧ paperPos a ≤ paperPos y) ∨
          (paperPos b ≤ paperPos t ∧ paperPos t < paperPos y) := by
      simp only [indexInterval, Finset.mem_filter, Finset.mem_univ,
        true_and, paperPos] at hx ⊢
      omega
    apply hnot
    exact ⟨hyw.1, hyw.2, a, t, ha2, hat, hz, hcross⟩
  have hpres :=
    swap_preserves_interval_of_membership_iff
      (applyPositionPerm σ π) b y a t hsame
  have hzero : indexedIntervalSum (applyPositionPerm σ π) a t = 0 := by
    rw [← hpres]
    exact hz
  refine ⟨hzero, ?_⟩
  intro htb
  subst t
  apply hnot
  refine ⟨hyw.1, hyw.2, a, b, ha2, hat, hz, ?_⟩
  exact Or.inr ⟨le_rfl, hyw.1⟩

theorem extend_admissible_collection
    {n D : ℕ}
    {P : Finset (Fin n × Fin n)}
    (hP : IsAdmissibleCollection D P)
    {b y : Fin n}
    (hby : paperPos b < paperPos y)
    (hlen : paperPos y - paperPos b ≤ 5 * D)
    (hbfirst : ∀ q ∈ P, q.1 ≠ b)
    (hbsecond : ∀ q ∈ P, q.2 ≠ b)
    (hyfirst : ∀ q ∈ P, q.1 ≠ y)
    (hysecond : ∀ q ∈ P, q.2 ≠ y) :
    IsAdmissibleCollection D (insert (b, y) P) := by
  constructor
  · rw [Finset.coe_insert, Set.pairwise_insert_of_symmetric]
    · constructor
      · intro q hq hne
        exact ⟨hbfirst q hq, hyfirst q hq,
          hbsecond q hq, hysecond q hq⟩
      · exact hP.1
    · intro q r h
      exact ⟨h.1.symm, h.2.2.1.symm,
        h.2.1.symm, h.2.2.2.symm⟩
  · intro q hq
    rcases Finset.mem_insert.1 hq with rfl | hq
    · exact ⟨hby, hlen⟩
    · exact hP.2 q hq

theorem collectionPerm_insert
    {n D : ℕ}
    {P : Finset (Fin n × Fin n)}
    (hP : IsAdmissibleCollection D P)
    {b y : Fin n}
    (hnew : IsAdmissibleCollection D (insert (b,y) P))
    (hnotmem : (b,y) ∉ P) :
    collectionPerm (insert (b,y) P) =
      (Equiv.swap b y).trans (collectionPerm P) := by
  let l := (b,y) :: P.toList
  have hl : l.toFinset = insert (b,y) P := by
    simp [l]
  have hln : l.Nodup := by
    simp [l, hnotmem]
  have hord :=
    collectionPerm_order_independent hnew l hl hln
  simpa [l, swapsPermList, collectionPerm] using hord.symm

theorem repair_state_step
    {n p D : ℕ} (hD : 0 < D)
    (σ : Fin n → ZMod p)
    (B R : Finset (Fin n))
    (P : Finset (Fin n × Fin n))
    (hB : B = badRightEndpoints σ)
    (hstate : RepairState σ B R P)
    (hfar : ∀ b ∈ B, paperPos b + 5 * D ≤ n)
    (hlocal : ∀ z : Fin n,
      (B ∩ symmetricWindow z (10 * D)).card ≤ D)
    (hblocked :
      ∀ b ∈ B, ∀ π : Equiv.Perm (Fin n),
        IsAdmissiblePermutation D π →
        FixedBelow b π →
        (blockedCandidates D σ b π).card < 2 * D)
    (hR : R.Nonempty) :
    ∃ b ∈ R, ∃ y ∈ repairWindow b D,
      y ∉ badRightEndpoints σ ∧
      y ∉ usedSeconds P ∧
      ¬ IsBlockedAt D σ b (collectionPerm P) y ∧
      RepairState σ B (R.erase b) (insert (b,y) P) := by
  classical
  let b := R.max' hR
  have hbR : b ∈ R := R.max'_mem hR
  have hbB : b ∈ B := hstate.remaining_subset hbR
  have hbfar := hfar b hbB
  have hfixThrough :
      FixedThrough b (collectionPerm P) := by
    apply collectionPerm_fixes_of_support_above hstate.admissible
    intro q hq
    exact hstate.processed_above q hq b hbR
  have hfix : FixedBelow b (collectionPerm P) := by
    intro i hi
    exact hfixThrough i (le_of_lt hi)
  have hπadm : IsAdmissiblePermutation D (collectionPerm P) :=
    ⟨P, hstate.admissible, rfl⟩
  have hblockedCard :=
    hblocked b hbB (collectionPerm P) hπadm hfix
  let C := repairWindow b D
  have hCcard : C.card = 5 * D :=
    card_repairWindow b hbfar
  have h₁ :
      (C ∩ blockedCandidates D σ b (collectionPerm P)).card ≤
        2 * D :=
    blocked_in_repairWindow_le σ b (collectionPerm P) hblockedCard
  have h₂ : (C ∩ B).card ≤ D :=
    badEndpoints_in_repairWindow_le B hB hlocal b
  have h₃ : (C ∩ usedSeconds P).card ≤ D :=
    usedSeconds_near_card_le hstate hlocal hbR
  obtain ⟨y, hyC, hyBlocked, hyB, hyUsed⟩ :=
    Section5External.exists_after_three_forbidden
      D hD C
      (blockedCandidates D σ b (collectionPerm P))
      B (usedSeconds P)
      hCcard h₁ h₂ h₃
  have hyw := mem_repairWindow.mp hyC
  have hyNotBad : y ∉ badRightEndpoints σ := by
    simpa [← hB] using hyB
  have hnotBlocked : ¬ IsBlockedAt D σ b (collectionPerm P) y := by
    intro h
    exact hyBlocked (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
  have hbfirst : ∀ q ∈ P, q.1 ≠ b := by
    intro q hq h
    subst h
    exact (not_lt_of_ge (le_rfl : paperPos b ≤ paperPos b))
      (hstate.processed_above q hq b hbR)
  have hbsecond : ∀ q ∈ P, q.2 ≠ b := by
    intro q hq h
    subst h
    exact (hstate.pair_data q hq).2.2 hbB
  have hyfirst : ∀ q ∈ P, q.1 ≠ y := by
    intro q hq h
    subst h
    exact hyNotBad (hstate.pair_data q hq).1
  have hysecond : ∀ q ∈ P, q.2 ≠ y := by
    intro q hq h
    subst h
    exact hyUsed (by
      unfold usedSeconds
      exact Finset.mem_image.2 ⟨q, hq, rfl⟩)
  have hnewAdm :
      IsAdmissibleCollection D (insert (b,y) P) :=
    extend_admissible_collection hstate.admissible
      hyw.1 (by simpa [paperPos] using Nat.sub_le_iff_le_add.2 hyw.2)
      hbfirst hbsecond hyfirst hysecond
  have hnotmem : (b,y) ∉ P := by
    intro h
    exact hbfirst (b,y) h rfl
  have hperm :
      collectionPerm (insert (b,y) P) =
        (Equiv.swap b y).trans (collectionPerm P) :=
    collectionPerm_insert hstate.admissible hnewAdm hnotmem
  have hnewState :
      RepairState σ B (R.erase b) (insert (b,y) P) := by
    refine ⟨hnewAdm, ?_, ?_, ?_, ?_⟩
    · intro r hr
      exact hstate.remaining_subset (Finset.mem_erase.1 hr).2
    · intro q hq
      rcases Finset.mem_insert.1 hq with rfl | hq
      · refine ⟨hbB, ?_, hyB⟩
        simp
      · rcases hstate.pair_data q hq with ⟨hqB, hqR, hq2⟩
        exact ⟨hqB, by
          intro h
          exact hqR (Finset.mem_erase.1 h).2, hq2⟩
    · intro q hq r hr
      rcases Finset.mem_insert.1 hq with rfl | hq
      · have hrR := (Finset.mem_erase.1 hr).2
        have hrne := (Finset.mem_erase.1 hr).1
        have hle := R.le_max' r hrR
        have hval : r.val < b.val := by
          have : r ≠ b := by simpa [eq_comm] using hrne
          omega
        simpa [paperPos] using hval
      · exact hstate.processed_above q hq r
          (Finset.mem_erase.1 hr).2
    · intro a t ha hat hz
      have hz' :
          indexedIntervalSum
            (applyPositionPerm
              (applyPositionPerm σ (collectionPerm P))
              (Equiv.swap b y)) a t = 0 := by
        rw [← hperm] at hz
        simpa [applyPositionPerm, Function.comp_def] using hz
      rcases not_blocked_zero_preserves
          σ (collectionPerm P) b y a t
          hyC ha hat hnotBlocked hz' with ⟨hbefore, htne⟩
      have htR := hstate.zero_right a t ha hat hbefore
      exact Finset.mem_erase.2 ⟨htne, htR⟩
  exact ⟨b, hbR, y, hyC, hyNotBad, hyUsed,
    hnotBlocked, hnewState⟩

/-- The complete induction on the number of unprocessed bad endpoints. -/
theorem repair_all_bad_endpoints
    {n p D : ℕ} (hD : 0 < D)
    (σ : Fin n → ZMod p)
    (B R : Finset (Fin n))
    (P : Finset (Fin n × Fin n))
    (hB : B = badRightEndpoints σ)
    (hstate : RepairState σ B R P)
    (hfar : ∀ b ∈ B, paperPos b + 5 * D ≤ n)
    (hlocal : ∀ z : Fin n,
      (B ∩ symmetricWindow z (10 * D)).card ≤ D)
    (hblocked :
      ∀ b ∈ B, ∀ π : Equiv.Perm (Fin n),
        IsAdmissiblePermutation D π →
        FixedBelow b π →
        (blockedCandidates D σ b π).card < 2 * D) :
    ∃ P' : Finset (Fin n × Fin n),
      IsAdmissibleCollection D P' ∧
      ZeroRightInvariant σ P' ∅ := by
  classical
  induction hcard : R.card using Nat.strong_induction_on
      generalizing R P with
  | h k ih =>
      by_cases hR : R.Nonempty
      · obtain ⟨b, hbR, y, hyC, hyB, hyUsed, hyBlocked, hstep⟩ :=
          repair_state_step hD σ B R P hB hstate
            hfar hlocal hblocked hR
        have hlt :
            (R.erase b).card < R.card := by
          rw [Finset.card_erase_of_mem hbR]
          omega
        exact ih (R.erase b).card hlt
          (R.erase b) (insert (b,y) P) rfl hstep
      · have hRempty : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hR
        subst R
        exact ⟨P, hstate.admissible, hstate.zero_right⟩

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
  have hinit : RepairState σ B B ∅ :=
    empty_repair_state σ B
  obtain ⟨P, hPadm, hzero⟩ :=
    repair_all_bad_endpoints hD σ B B ∅ rfl
      hinit hfar hlocal hblocked
  let π := collectionPerm P
  refine ⟨π, ⟨P, hPadm, rfl⟩, ?_⟩
  intro a t ha hat hz
  have : t ∈ (∅ : Finset (Fin n)) :=
    hzero a t ha hat hz
  simpa using this

end

end GrahamRearrangement
