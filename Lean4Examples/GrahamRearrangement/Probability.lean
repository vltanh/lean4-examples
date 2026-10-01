import Mathlib

open scoped BigOperators

namespace GrahamRearrangement

/-!
# Finite uniform probability

The paper only uses finite probability spaces.  We keep the core notions as
cardinality ratios so that every random-subset, random-partition, and random-bijection
statement has an explicit finite sample space.
-/

noncomputable section

/-- Uniform probability of an event on a finite sample space. -/
def uniformMass {Ω : Type*} [DecidableEq Ω] (space : Finset Ω)
    (event : Ω → Prop) [DecidablePred event] : ℝ :=
  ((space.filter event).card : ℝ) / (space.card : ℝ)

/-- Uniform expectation of a real-valued function on a finite sample space. -/
def uniformExpectation {Ω : Type*} [DecidableEq Ω] (space : Finset Ω)
    (f : Ω → ℝ) : ℝ :=
  (∑ ω ∈ space, f ω) / (space.card : ℝ)

/-- Conditional uniform mass, obtained by restricting the finite sample space. -/
def uniformConditionalMass {Ω : Type*} [DecidableEq Ω] (space : Finset Ω)
    (given event : Ω → Prop) [DecidablePred given] [DecidablePred event] : ℝ :=
  uniformMass (space.filter given) event

theorem uniformMass_nonneg {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (event : Ω → Prop) [DecidablePred event] :
    0 ≤ uniformMass space event := by
  unfold uniformMass
  positivity

theorem uniformMass_le_one {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (event : Ω → Prop) [DecidablePred event] :
    uniformMass space event ≤ 1 := by
  unfold uniformMass
  by_cases h : space.card = 0
  · simp [h]
  · have hpos : (0 : ℝ) < space.card := by
      exact_mod_cast Nat.pos_of_ne_zero h
    apply (div_le_one hpos).2
    exact_mod_cast Finset.card_filter_le space event

theorem uniformMass_empty_of_forall_not
    {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (E : Ω → Prop) [DecidablePred E]
    (hE : ∀ ω, ¬ E ω) :
    uniformMass space E = 0 := by
  unfold uniformMass
  have hempty : space.filter E = ∅ := by
    ext ω
    simp [hE ω]
  rw [hempty]
  simp

theorem uniformMass_empty {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) :
    uniformMass space (fun _ => False) = 0 := by
  simp [uniformMass]

theorem uniformMass_univ {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (h : space.Nonempty) :
    uniformMass space (fun _ => True) = 1 := by
  simp [uniformMass, h.card_ne_zero]

theorem uniformMass_congr {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (E F : Ω → Prop)
    [DecidablePred E] [DecidablePred F]
    (h : ∀ ω ∈ space, (E ω ↔ F ω)) :
    uniformMass space E = uniformMass space F := by
  unfold uniformMass
  congr 2
  ext ω
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hω, hE⟩
    exact ⟨hω, (h ω hω).1 hE⟩
  · rintro ⟨hω, hF⟩
    exact ⟨hω, (h ω hω).2 hF⟩

/-- Monotonicity of finite uniform mass. -/
theorem uniformMass_mono {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (E F : Ω → Prop)
    [DecidablePred E] [DecidablePred F]
    (hEF : ∀ ω, E ω → F ω) :
    uniformMass space E ≤ uniformMass space F := by
  unfold uniformMass
  gcongr
  exact Finset.card_le_card fun ω hω => by
    simp only [Finset.mem_filter] at hω ⊢
    exact ⟨hω.1, hEF _ hω.2⟩

theorem uniformMass_mono_on {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (E F : Ω → Prop)
    [DecidablePred E] [DecidablePred F]
    (hEF : ∀ ω ∈ space, E ω → F ω) :
    uniformMass space E ≤ uniformMass space F := by
  unfold uniformMass
  gcongr
  exact Finset.card_le_card fun ω hω => by
    rcases Finset.mem_filter.1 hω with ⟨hspace, hE⟩
    exact Finset.mem_filter.2 ⟨hspace, hEF ω hspace hE⟩

/-- Finite union bound for an indexed family of events. -/
theorem uniformMass_exists_le_sum {Ω ι : Type*}
    [DecidableEq Ω] [DecidableEq ι]
    (space : Finset Ω) (I : Finset ι) (E : ι → Ω → Prop)
    [∀ i, DecidablePred (E i)] :
    uniformMass space (fun ω => ∃ i ∈ I, E i ω) ≤
      ∑ i ∈ I, uniformMass space (E i) := by
  classical
  unfold uniformMass
  by_cases hspace : space.card = 0
  · simp [hspace]
  · have hden : (0 : ℝ) < space.card := by
      exact_mod_cast Nat.pos_of_ne_zero hspace
    apply (div_le_iff₀ hden).2
    have hcard :
        (space.filter fun ω => ∃ i ∈ I, E i ω).card ≤
          ∑ i ∈ I, (space.filter (E i)).card := by
      apply Finset.card_biUnion_le
      intro i hi
      exact space.filter (E i)
    exact_mod_cast hcard

/-- A pointwise bound averages to the same bound over a nonempty uniform space. -/
theorem uniformExpectation_le_const {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (hspace : space.Nonempty)
    (f : Ω → ℝ) (c : ℝ)
    (h : ∀ ω ∈ space, f ω ≤ c) :
    uniformExpectation space f ≤ c := by
  unfold uniformExpectation
  have hsum :
      (∑ ω ∈ space, f ω) ≤ space.card * c := by
    calc
      (∑ ω ∈ space, f ω) ≤ ∑ _ω ∈ space, c := by
        gcongr with ω hω
        exact h ω hω
      _ = space.card * c := by simp [mul_comm]
  have hden : (0 : ℝ) < space.card := by
    exact_mod_cast hspace.card_pos
  apply (div_le_iff₀ hden).2
  simpa [mul_comm] using hsum

theorem powersetCard_nonempty {α : Type*} [DecidableEq α]
    (S : Finset α) {m : ℕ} (hm : m ≤ S.card) :
    (S.powersetCard m).Nonempty := by
  obtain ⟨T, hTS, hcard⟩ := Finset.exists_subset_card_eq hm
  exact ⟨T, Finset.mem_powersetCard.2 ⟨hTS, hcard⟩⟩

theorem mem_powersetCard_card {α : Type*} [DecidableEq α]
    {S R : Finset α} {m : ℕ} (hR : R ∈ S.powersetCard m) :
    R.card = m :=
  (Finset.mem_powersetCard.1 hR).2

theorem card_sdiff_of_mem_powersetCard {α : Type*} [DecidableEq α]
    {S R : Finset α} {m : ℕ} (hR : R ∈ S.powersetCard m) :
    (S \ R).card = S.card - m := by
  have hsub := (Finset.mem_powersetCard.1 hR).1
  rw [Finset.card_sdiff hsub, mem_powersetCard_card hR]

/-- Removing two exceptional events. -/
theorem uniformMass_le_two_exceptions
    {Ω : Type*} [DecidableEq Ω] (space : Finset Ω)
    (E A B : Ω → Prop)
    [DecidablePred E] [DecidablePred A] [DecidablePred B]
    (q : ℝ)
    (hrest :
      uniformMass space (fun ω => E ω ∧ ¬ A ω ∧ ¬ B ω) ≤ q) :
    uniformMass space E ≤ uniformMass space A + uniformMass space B + q := by
  have hsubset : ∀ ω, E ω →
      (A ω ∨ B ω) ∨ (E ω ∧ ¬ A ω ∧ ¬ B ω) := by
    intro ω hE
    by_cases hA : A ω
    · exact Or.inl (Or.inl hA)
    by_cases hB : B ω
    · exact Or.inl (Or.inr hB)
    · exact Or.inr ⟨hE, hA, hB⟩
  have hmono :
      uniformMass space E ≤
        uniformMass space
          (fun ω => (A ω ∨ B ω) ∨ (E ω ∧ ¬ A ω ∧ ¬ B ω)) := by
    apply uniformMass_mono
    exact hsubset
  have hor1 :=
    uniformMass_or_le_add space
      (fun ω => A ω ∨ B ω)
      (fun ω => E ω ∧ ¬ A ω ∧ ¬ B ω)
  have hor2 := uniformMass_or_le_add space A B
  linarith

/-- If three events have total mass below one in a nonempty finite space, some
outcome avoids all three. -/
theorem exists_avoiding_three_events
    {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (hspace : space.Nonempty)
    (E₁ E₂ E₃ : Ω → Prop)
    [DecidablePred E₁] [DecidablePred E₂] [DecidablePred E₃]
    (a₁ a₂ a₃ : ℝ)
    (h₁ : uniformMass space E₁ ≤ a₁)
    (h₂ : uniformMass space E₂ ≤ a₂)
    (h₃ : uniformMass space E₃ ≤ a₃)
    (hsum : a₁ + a₂ + a₃ < 1) :
    ∃ ω ∈ space, ¬ E₁ ω ∧ ¬ E₂ ω ∧ ¬ E₃ ω := by
  by_contra hnone
  push_neg at hnone
  have hcover : ∀ ω ∈ space, E₁ ω ∨ E₂ ω ∨ E₃ ω := by
    intro ω hω
    exact hnone ω hω
  have hall :
      uniformMass space (fun ω => E₁ ω ∨ E₂ ω ∨ E₃ ω) = 1 := by
    rw [← uniformMass_univ space hspace]
    apply uniformMass_congr
    intro ω hω
    simp [hcover ω hω]
  have h12 := uniformMass_or_le_add space E₁ E₂
  have h123 := uniformMass_or_le_add space
    (fun ω => E₁ ω ∨ E₂ ω) E₃
  rw [hall] at h123
  linarith

theorem log_card_sdiff_le {α : Type*} [DecidableEq α]
    {S R : Finset α} (hne : (S \ R).Nonempty) :
    Real.log ((S \ R).card : ℝ) ≤ Real.log (S.card : ℝ) := by
  apply Real.strictMonoOn_log.monotoneOn
  · exact_mod_cast hne.card_pos
  · exact_mod_cast Finset.card_sdiff_le S R

theorem card_pi_le_pow {ι α : Type*}
    [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (U : ι → Finset α) (M : ℕ)
    (hU : ∀ i, (U i).card ≤ M) :
    (Finset.univ.pi U).card ≤ M ^ Fintype.card ι := by
  classical
  rw [Finset.card_pi]
  calc
    (∏ i : ι, (U i).card) ≤ ∏ _i : ι, M := by
      gcongr with i
      exact hU i
    _ = M ^ Fintype.card ι := by simp

theorem card_product_le_mul {α β : Type*}
    [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β)
    (a b : ℕ) (hA : A.card ≤ a) (hB : B.card ≤ b) :
    (A.product B).card ≤ a * b := by
  rw [Finset.card_product]
  exact Nat.mul_le_mul hA hB

theorem card_eq_sum_card_fibers {α β : Type*}
    [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (f : α → β)
    (hmap : ∀ a ∈ A, f a ∈ B) :
    A.card = ∑ b ∈ B, (A.filter fun a => f a = b).card := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a A ha ih =>
      have hfa : f a ∈ B := hmap a (by simp)
      have hmapA : ∀ x ∈ A, f x ∈ B := by
        intro x hx
        exact hmap x (by simp [hx])
      rw [Finset.card_insert_of_not_mem ha, ih B f hmapA]
      rw [Finset.sum_eq_add_sum_diff_singleton hfa]
      simp [ha]

/-- Finite union bound for two events. -/
theorem uniformMass_or_le_add {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (E F : Ω → Prop)
    [DecidablePred E] [DecidablePred F] :
    uniformMass space (fun ω => E ω ∨ F ω) ≤
      uniformMass space E + uniformMass space F := by
  unfold uniformMass
  by_cases h : space.card = 0
  · simp [h]
  · have hpos : (0 : ℝ) < space.card := by
      exact_mod_cast Nat.pos_of_ne_zero h
    rw [div_add_div_same]
    apply (div_le_div_iff_of_pos_right hpos).2
    exact_mod_cast
      (Finset.card_filter_or_le (s := space) (p := E) (q := F))

/-- An event and its complement have total mass one on a nonempty space. -/
theorem uniformMass_compl_eq_one {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (hspace : space.Nonempty)
    (E : Ω → Prop) [DecidablePred E] :
    uniformMass space E + uniformMass space (fun ω => ¬ E ω) = 1 := by
  unfold uniformMass
  have hpartition :
      (space.filter E).card + (space.filter fun ω => ¬ E ω).card = space.card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext ω
      simp
    · exact Finset.disjoint_filter_filter_neg _ _
  rw [← add_div]
  norm_num [hspace.card_ne_zero, hpartition]

/-- Cardinal form of a lower bound on uniform mass. -/
theorem card_filter_ge_of_uniformMass_ge {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (hspace : space.Nonempty)
    (E : Ω → Prop) [DecidablePred E] (c : ℝ)
    (h : c ≤ uniformMass space E) :
    c * space.card ≤ (space.filter E).card := by
  unfold uniformMass at h
  have hcard : (0 : ℝ) < space.card := by
    exact_mod_cast hspace.card_pos
  apply (le_div_iff₀ hcard).1
  simpa [mul_comm] using h

/-- Uniform probability of a singleton in a nonempty finite space. -/
theorem uniformMass_eq_singleton {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (ω : Ω) (hω : ω ∈ space) :
    uniformMass space (fun x => x = ω) = 1 / (space.card : ℝ) := by
  rw [uniformMass]
  have hcard : (space.filter fun x => x = ω).card = 1 := by
    rw [Finset.card_eq_one]
    exact ⟨ω, by ext x; simp [hω]⟩
  rw [hcard]
  norm_num

/-- Monotonicity of uniform expectation. -/
theorem uniformExpectation_mono {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (f g : Ω → ℝ)
    (hfg : ∀ ω ∈ space, f ω ≤ g ω) :
    uniformExpectation space f ≤ uniformExpectation space g := by
  unfold uniformExpectation
  by_cases h : space.card = 0
  · simp [h]
  · have hden : (0 : ℝ) < space.card := by
      exact_mod_cast Nat.pos_of_ne_zero h
    apply (div_le_div_iff_of_pos_right hden).2
    exact Finset.sum_le_sum fun i hi =>
      Finset.sum_le_sum fun _ _ => hfg i hi

theorem uniformExpectation_add {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (f g : Ω → ℝ) :
    uniformExpectation space (fun ω => f ω + g ω) =
      uniformExpectation space f + uniformExpectation space g := by
  unfold uniformExpectation
  rw [Finset.sum_add_distrib]
  ring

theorem uniformExpectation_smul {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (c : ℝ) (f : Ω → ℝ) :
    uniformExpectation space (fun ω => c * f ω) =
      c * uniformExpectation space f := by
  unfold uniformExpectation
  rw [← Finset.mul_sum]
  ring

/-- Average of a constant over a nonempty finite space. -/
theorem uniformExpectation_const {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (h : space.Nonempty) (c : ℝ) :
    uniformExpectation space (fun _ => c) = c := by
  simp [uniformExpectation, h.card_ne_zero]

/-- The indicator expectation equals the corresponding uniform mass. -/
theorem uniformExpectation_indicator {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (E : Ω → Prop) [DecidablePred E] :
    uniformExpectation space (fun ω => if E ω then 1 else 0) =
      uniformMass space E := by
  classical
  unfold uniformExpectation uniformMass
  congr 1
  simpa [Finset.sum_boole]

end

end GrahamRearrangement
