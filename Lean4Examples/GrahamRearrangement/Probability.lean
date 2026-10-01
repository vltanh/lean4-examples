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

theorem uniformMass_empty {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) :
    uniformMass space (fun _ => False) = 0 := by
  simp [uniformMass]

theorem uniformMass_univ {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (h : space.Nonempty) :
    uniformMass space (fun _ => True) = 1 := by
  simp [uniformMass, h.card_ne_zero]

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
