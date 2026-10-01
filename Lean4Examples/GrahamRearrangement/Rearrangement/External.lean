import Lean4Examples.GrahamRearrangement.Rearrangement.Parameters

open scoped BigOperators Pointwise

namespace GrahamRearrangement.Section5External

/-!
# External finite-permutation facts used in Section 5

All axioms here are generic facts about uniformly random bijections, conditioning,
finite fibers, and matchings.  None is a numbered result of Pham--Sauermann.
-/

noncomputable section

axiom indexedOrderings_nonempty {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) :
    (indexedOrderings S).Nonempty

/-- Reindexing a family of left endpoints by the corresponding interval length
only decreases a sum of nonnegative weights when we enlarge to all lengths 1,...,n-1. -/
axiom endpoint_reindex_sum_le
    {n : ℕ} (b : Fin n) (A : Finset (Fin n))
    (hA : ∀ a ∈ A, a.val ≤ b.val)
    (w : ℕ → ℝ) (hw : ∀ r, 0 ≤ w r) :
    (∑ a ∈ A, w (b.val - a.val + 1)) ≤
      ∑ r ∈ Finset.Icc 1 (n - 1), w r

/-- The image of a fixed r-set of indices under a uniform bijection is a uniform
r-subset of S. -/
axiom fixedIndexSet_sumMass {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (I : Finset (Fin S.card))
    (z : ZMod p) :
    orderingEventMass S (fun σ => indexSetSum σ I = z) =
      sliceMass S I.card z

/-- Composition by a fixed permutation of positions preserves the uniform law. -/
axiom ordering_perm_invariant {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (π : Equiv.Perm (Fin S.card))
    (E : (Fin S.card → ZMod p) → Prop) [DecidablePred E] :
    orderingEventMass S E =
      orderingEventMass S (fun σ => E (applyPositionPerm σ π))

/-- Conditional version of the preceding invariance. -/
axiom ordering_conditional_perm_invariant {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (π : Equiv.Perm (Fin S.card))
    (given event : (Fin S.card → ZMod p) → Prop)
    [DecidablePred given] [DecidablePred event] :
    orderingConditionalMass S given event =
      orderingConditionalMass S
        (fun σ => given (applyPositionPerm σ π))
        (fun σ => event (applyPositionPerm σ π))

/-- Distinct index subsets in a window have equal image sums with probability at
most the reciprocal number of choices left for one exposed coordinate. -/
axiom distinct_index_subset_sums_mass_le {p : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (W J J' : Finset (Fin S.card))
    (hJ : J ⊆ W) (hJ' : J' ⊆ W) (hne : J ≠ J')
    (hW : W.card ≤ S.card) :
    orderingEventMass S (fun σ => indexSetSum σ J = indexSetSum σ J') ≤
      1 / ((S.card - W.card + 1 : ℕ) : ℝ)

/-- Conditioning a uniform bijection on its values on F leaves a uniform bijection
between the unexposed positions and S minus the exposed image. Nested image sets
therefore have exactly the chain law on the remaining ground set. -/
axiom conditional_nested_images_chainMass {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (τ : Fin S.card → ZMod p) (hτ : IsIndexedOrdering S τ)
    (F : Finset (Fin S.card))
    (I : Fin k → Finset (Fin S.card))
    (hdisj : ∀ i, Disjoint F (I i))
    (hnested : ∀ i j, i ≤ j → I i ⊆ I j)
    (m : Fin k → ℕ) (hcard : ∀ i, (I i).card = m i)
    (z : Fin k → ZMod p) :
    orderingConditionalMass S
      (fun σ => AgreesOn F σ τ)
      (fun σ => ∀ i, indexSetSum σ (I i) = z i) =
      chainMass (S \ indexImageSet τ F) m z

/-- Conditioning on a window gives the obvious complement cardinality. -/
axiom exposed_image_card {p : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    {τ : Fin S.card → ZMod p} (hτ : IsIndexedOrdering S τ)
    (F : Finset (Fin S.card)) :
    (indexImageSet τ F).card = F.card

/-- Generic multiplication of an event probability by a uniform upper bound for a
second event on every fiber of a finite statistic. -/
axiom joint_event_le_of_fiber_bound
    {Ω K : Type*} [DecidableEq Ω] [DecidableEq K]
    (space : Finset Ω) (key : Ω → K)
    (A B : Ω → Prop) [DecidablePred A] [DecidablePred B]
    (a b : ℝ)
    (hA : uniformMass space A ≤ a)
    (hB : ∀ κ : K,
      uniformConditionalMass space (fun ω => key ω = κ) B ≤ b) :
    uniformMass space (fun ω => A ω ∧ B ω) ≤ a * b

/-- Fiber multiplication specialized to exposing a set of positions in a
uniform random ordering. -/
axiom joint_event_le_of_agreesOn_fibers {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (F : Finset (Fin S.card))
    (A B : (Fin S.card → ZMod p) → Prop)
    [DecidablePred A] [DecidablePred B]
    (a b : ℝ)
    (hA : orderingEventMass S A ≤ a)
    (hdetermined :
      ∀ σ τ, AgreesOn F σ τ → (A σ ↔ A τ))
    (hfiber :
      ∀ τ, IsIndexedOrdering S τ → A τ →
        orderingConditionalMass S
          (fun σ => AgreesOn F σ τ) B ≤ b) :
    orderingEventMass S (fun σ => A σ ∧ B σ) ≤ a * b

/-- Union bound over a finite set of possible parameter records. -/
axiom finite_parameter_union_bound
    {Ω Θ : Type*} [DecidableEq Ω] [DecidableEq Θ]
    (space : Finset Ω) (params : Finset Θ)
    (E : Θ → Ω → Prop) [∀ θ, DecidablePred (E θ)] :
    uniformMass space (fun ω => ∃ θ ∈ params, E θ ω) ≤
      ∑ θ ∈ params, uniformMass space (E θ)

/-- A generic upper bound for the number of partial matchings when each of q
possible first endpoints has at most r possible partners. -/
axiom partial_matching_count_le (q r : ℕ) :
    ∀ {n : ℕ} (Q : Finset (Fin n)),
      Q.card ≤ q →
      ((r + 1 : ℕ) ^ q : ℕ) ≤ (r + 1) ^ q ∧
      0 < (r + 1) ^ q

/-- Fixed-position reversal is a permutation and therefore preserves a uniform
random ordering. -/
axiom reversal_perm_invariant {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (E : (Fin S.card → ZMod p) → Prop)
    [DecidablePred E] :
    orderingEventMass S E =
      orderingEventMass S (fun σ =>
        E (fun i => σ ⟨S.card - 1 - i.val, by omega⟩))

/-- Generic finite choice principle used in the greedy repair: a finite candidate
set of cardinality 5D with three forbidden subsets of sizes at most 2D,D,D
has a remaining element when D>0. -/
axiom exists_after_three_forbidden {α : Type*} [DecidableEq α]
    (D : ℕ) (hD : 0 < D)
    (C F₁ F₂ F₃ : Finset α)
    (hC : C.card = 5 * D)
    (h₁ : (C ∩ F₁).card ≤ 2 * D)
    (h₂ : (C ∩ F₂).card ≤ D)
    (h₃ : (C ∩ F₃).card ≤ D) :
    ∃ x ∈ C, x ∉ F₁ ∧ x ∉ F₂ ∧ x ∉ F₃

end

end GrahamRearrangement.Section5External
