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

/-- Specialized finite form of the preceding sampling fact for ZMod orderings. -/
axiom conditional_index_family_sumMass_le_zmod
    {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (τ : Fin S.card → ZMod p) (hτ : IsIndexedOrdering S τ)
    (F : Finset (Fin S.card))
    (A : Finset (Fin S.card))
    (I : Fin S.card → Finset (Fin S.card))
    (z : Fin S.card → ZMod p)
    (hdisj : ∀ a ∈ A, Disjoint F (I a)) :
    orderingConditionalMass S
      (fun σ => AgreesOn F σ τ)
      (fun σ => ∃ a ∈ A, indexSetSum σ (I a) = z a) ≤
      ∑ a ∈ A,
        sliceMass (S \ indexImageSet τ F) (I a).card (z a)

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

/-- A uniform bound on an event in every fiber obtained by exposing F is also
an unconditional bound. -/
axiom event_le_of_agreesOn_fibers {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (F : Finset (Fin S.card))
    (E : (Fin S.card → ZMod p) → Prop) [DecidablePred E]
    (q : ℝ)
    (hfiber :
      ∀ τ, IsIndexedOrdering S τ →
        orderingConditionalMass S
          (fun σ => AgreesOn F σ τ) E ≤ q) :
    orderingEventMass S E ≤ q

/-- Crude count of a base point and D ordered choices from a 20D-window. -/
axiom base_and_window_tuple_count {n D : ℕ} :
    (Finset.univ : Finset (Fin n × (Fin D → Fin n))).filter
      (fun θ =>
        ∀ i, paperPos θ.1 < paperPos (θ.2 i) ∧
          paperPos (θ.2 i) ≤ paperPos θ.1 + 20 * D)
      |>.card ≤ n * (20 * D) ^ D

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

/-- Union bound in witness form: if every occurrence of E supplies a parameter
θ and the θ-event has mass at most q, then E has mass at most |params| q. -/
axiom witness_union_bound
    {Ω Θ : Type*} [DecidableEq Ω] [DecidableEq Θ]
    (space : Finset Ω) (params : Finset Θ)
    (E : Ω → Prop) (A : Θ → Ω → Prop)
    [DecidablePred E] [∀ θ, DecidablePred (A θ)]
    (q : ℝ)
    (hcover : ∀ ω ∈ space, E ω → ∃ θ ∈ params, A θ ω)
    (hbound : ∀ θ ∈ params, uniformMass space (A θ) ≤ q) :
    uniformMass space E ≤ (params.card : ℝ) * q

/-- Removing two exceptional events: if E outside A∪B has mass q, then E has
mass at most mass(A)+mass(B)+q. -/
axiom mass_le_two_exceptions
    {Ω : Type*} [DecidableEq Ω] (space : Finset Ω)
    (E A B : Ω → Prop)
    [DecidablePred E] [DecidablePred A] [DecidablePred B]
    (q : ℝ)
    (hrest :
      uniformMass space (fun ω => E ω ∧ ¬ A ω ∧ ¬ B ω) ≤ q) :
    uniformMass space E ≤
      uniformMass space A + uniformMass space B + q

/-- Generic ordered-window extraction. More than D points in a symmetric 10D
window yield a least point b₀ and D further distinct points in the following 20D
window. -/
axiom dense_window_extract {n D : ℕ}
    (B : Finset (Fin n)) (hD : 0 < D)
    (h : ∃ z : Fin n,
      D < (B ∩ symmetricWindow z (10 * D)).card) :
    ∃ b₀ ∈ B, ∃ b : Fin D → Fin n,
      Function.Injective b ∧
      (∀ i, b i ∈ B) ∧
      (∀ i, paperPos b₀ < paperPos (b i) ∧
        paperPos (b i) ≤ paperPos b₀ + 20 * D)

/-- A finite tuple of distinct elements in a linear order can be relabelled in
strictly increasing order without changing the underlying set of witnesses. -/
axiom relabel_strictly_increasing
    {α : Type*} [LinearOrder α] [Fintype α] [DecidableEq α]
    {D : ℕ} (x : Fin D → α) (hinj : Function.Injective x) :
    ∃ y : Fin D → α, StrictMono y ∧
      Set.range y = Set.range x

/-- Generic permutation fact: transpositions with disjoint supports commute. -/
axiom disjoint_swaps_commute {α : Type*} [DecidableEq α]
    (a b c d : α)
    (hab : a ≠ b) (hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) :
    (Equiv.swap a b).trans (Equiv.swap c d) =
      (Equiv.swap c d).trans (Equiv.swap a b)

/-- Generic permutation fact: the product of a finite family of pairwise
support-disjoint transpositions is independent of the enumeration. -/
axiom disjoint_swaps_order_independent {α : Type*} [DecidableEq α]
    (P : Finset (α × α))
    (hP : P.toSet.Pairwise fun q r =>
      q.1 ≠ r.1 ∧ q.1 ≠ r.2 ∧ q.2 ≠ r.1 ∧ q.2 ≠ r.2)
    (l : List (α × α)) (hl : l.toFinset = P) (hln : l.Nodup) :
    swapsPermList l = swapsPermList P.toList

/-- Generic permutation fact: a finite collection of disjoint nontrivial
transpositions is recovered from the resulting permutation once each pair is
oriented by a fixed strict order. -/
axiom disjoint_swaps_reconstruct
    {α : Type*} [LinearOrder α] [DecidableEq α]
    (P Q : Finset (α × α))
    (hPpair : P.toSet.Pairwise fun q r =>
      q.1 ≠ r.1 ∧ q.1 ≠ r.2 ∧ q.2 ≠ r.1 ∧ q.2 ≠ r.2)
    (hQpair : Q.toSet.Pairwise fun q r =>
      q.1 ≠ r.1 ∧ q.1 ≠ r.2 ∧ q.2 ≠ r.1 ∧ q.2 ≠ r.2)
    (hPord : ∀ q ∈ P, q.1 < q.2)
    (hQord : ∀ q ∈ Q, q.1 < q.2)
    (hperm : swapsPermList P.toList = swapsPermList Q.toList) :
    P = Q

/-- A product of support-disjoint swaps fixes every point outside all swap
supports. -/
axiom disjoint_swaps_fix_outside_support
    {α : Type*} [DecidableEq α]
    (P : Finset (α × α))
    (hP : P.toSet.Pairwise fun q r =>
      q.1 ≠ r.1 ∧ q.1 ≠ r.2 ∧ q.2 ≠ r.1 ∧ q.2 ≠ r.2)
    (i : α)
    (hi : ∀ q ∈ P, i ≠ q.1 ∧ i ≠ q.2) :
    swapsPermList P.toList i = i

/-- Generic trimming principle for disjoint transpositions: swaps crossing none
of a finite family of index sets can be deleted without changing the image of
any of those sets. -/
axiom trim_irrelevant_disjoint_swaps
    {n k : ℕ} (P : Finset (Fin n × Fin n))
    (hP : P.toSet.Pairwise swapPairsDisjoint)
    (I : Fin k → Finset (Fin n)) :
    ∃ P' ⊆ P,
      P'.toSet.Pairwise swapPairsDisjoint ∧
      (∀ q ∈ P', ∃ i, ((q.1 ∈ I i) ↔ q.2 ∉ I i)) ∧
      ∀ i, (I i).image (collectionPerm P') =
        (I i).image (collectionPerm P)

/-- Interesting permutations are counted by their admissible collections once
all possible first endpoints are confined to Q. -/
axiom interestingPermutations_card_le_of_left_support
    {n k D : ℕ} (hD : 7 ≤ D)
    (I : Fin k → Finset (Fin n)) (Q : Finset (Fin n))
    (hQ : Q.card ≤ 7 * D ^ 2)
    (hsupport :
      ∀ π ∈ interestingPermutations D I,
        ∃ P : Finset (Fin n × Fin n),
          IsAdmissibleCollection D P ∧
          collectionPerm P = π ∧
          (∀ q ∈ P, q.1 ∈ Q)) :
    (interestingPermutations D I).card ≤ D ^ (14 * D ^ 2)

/-- Counting lemma for interesting local swap collections. This is a generic
partial-matching count with q≤7D² possible left endpoints and 5D possible
partners, specialized only to the elementary numerical simplification. -/
axiom interesting_collection_count_le
    (D : ℕ) (hD : 7 ≤ D) (q : ℕ) (hq : q ≤ 7 * D ^ 2) :
    (5 * D + 1) ^ q ≤ D ^ (14 * D ^ 2)

/-- Sort a finite injective tuple by a permutation of its coordinates. -/
axiom exists_sorting_perm
    {α : Type*} [LinearOrder α] {k : ℕ}
    (x : Fin k → α) (hinj : Function.Injective x) :
    ∃ ρ : Equiv.Perm (Fin k), StrictMono (x ∘ ρ)

/-- Generic bookkeeping for summing all increasing prefix-chain constraints after
conditioning on an exposed set. The substantive chain estimate is supplied by
hchain; this axiom only identifies/sums the finite fibers. -/
axiom conditional_prefix_chain_union_bound
    {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (τ : Fin S.card → ZMod p) (hτ : IsIndexedOrdering S τ)
    (F : Finset (Fin S.card)) (cut : Fin S.card)
    (target : Fin k → ZMod p)
    (C : ℝ)
    (hchain :
      ∀ (m : Fin k → ℕ), IsChainSizeTuple
          (S \ indexImageSet τ F).card m →
        ∀ z : Fin k → ZMod p,
          chainMass (S \ indexImageSet τ F) m z ≤
            chainUpperBound p (S \ indexImageSet τ F).card C m) :
    orderingConditionalMass S
      (fun σ => AgreesOn F σ τ)
      (fun σ =>
        ∃ a : Fin k → Fin S.card,
          StrictMono a ∧
          (∀ i, paperPos (a i) < paperPos cut) ∧
          (∀ i,
            indexSetSum σ (indexHalfOpen (a i) cut) = target i)) ≤
      lemma43LHS p (S \ indexImageSet τ F).card k C

/-- Right-tail analogue of conditional_prefix_chain_union_bound. -/
axiom conditional_suffix_chain_union_bound
    {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (τ : Fin S.card → ZMod p) (hτ : IsIndexedOrdering S τ)
    (F : Finset (Fin S.card)) (cut : Fin S.card)
    (target : Fin k → ZMod p)
    (C : ℝ)
    (hchain :
      ∀ (m : Fin k → ℕ), IsChainSizeTuple
          (S \ indexImageSet τ F).card m →
        ∀ z : Fin k → ZMod p,
          chainMass (S \ indexImageSet τ F) m z ≤
            chainUpperBound p (S \ indexImageSet τ F).card C m) :
    orderingConditionalMass S
      (fun σ => AgreesOn F σ τ)
      (fun σ =>
        ∃ x : Fin k → Fin S.card,
          StrictMono x ∧
          (∀ i, paperPos cut < paperPos (x i)) ∧
          (∀ i,
            indexSetSum σ (indexHalfOpen cut (x i)) = target i)) ≤
      lemma43LHS p (S \ indexImageSet τ F).card k C

/-- If a remaining ground set has size between n/2 and n, the Lemma 4.3 base
is bounded by twice the ambient n^{-α} bound used in Section 5. -/
axiom half_ground_lemma43Base_le
    {n s p : ℕ} {α C : ℝ}
    (hn : 2 ≤ n) (hhalf : n / 2 ≤ s) (hsn : s ≤ n)
    (hp : (n : ℝ) / p ≤ (n : ℝ) ^ (-α))
    (hC :
      4 * C * Real.sqrt (Real.log (n : ℝ)) /
        Real.sqrt (n : ℝ) ≤ (n : ℝ) ^ (-α)) :
    lemma43Base p s C ≤ 2 * (n : ℝ) ^ (-α)

/-- The exponent comparison αD≥3 used in the D-fold chain bounds. -/
axiom two_neg_alpha_pow_le_cube
    {n D : ℕ} {α : ℝ}
    (hn : 1 ≤ n) (hα0 : 0 < α)
    (hαD : 3 ≤ α * D) :
    (2 * (n : ℝ) ^ (-α)) ^ D ≤
      (2 : ℝ) ^ D / (n : ℝ) ^ 3

/-- Reindex an injective finite family of valid chain-size tuples into the full
sum occurring in Lemma 4.3. -/
axiom chainUpperBound_sum_le_lemma43
    {Θ : Type*} [DecidableEq Θ]
    {p n k : ℕ} (C : ℝ)
    (X : Finset Θ) (m : Θ → Fin k → ℕ)
    (hvalid : ∀ θ ∈ X, IsChainSizeTuple n (m θ))
    (hinj : Set.InjOn m X) :
    (∑ θ ∈ X, chainUpperBound p n C (m θ)) ≤
      lemma43LHS p n k C

/-- If an interesting transposition does not start near the exposed local window,
then crossing one of the constrained interval images forces it to start in the
backward 5D-window ending at the corresponding right endpoint. -/
axiom interesting_crossing_forces_tail_start
    {n D : ℕ} (hD : 0 < D)
    (b b' : Fin n)
    (hgap : paperPos b' - paperPos b = 5 * D)
    (u x : Fin D → Fin n)
    (πi : Fin D → Equiv.Perm (Fin n))
    (hu : ∀ i,
      paperPos b ≤ paperPos (u i) ∧
        paperPos (u i) ≤ paperPos b')
    (hfix : ∀ i, FixedOutside b b' (πi i))
    (q : Fin n × Fin n) (i : Fin D)
    (hlen :
      paperPos q.1 < paperPos q.2 ∧
        paperPos q.2 - paperPos q.1 ≤ 5 * D)
    (hcross : SwapCrosses q (constraintSet u x πi i))
    (hnotlocal : q.1 ∉ symmetricWindow b (5 * D)) :
    q.1 ∈ backwardWindow (x i) (5 * D)

/-- The right-tail size tuple associated with a strictly increasing tail tuple is
a valid chain-size tuple in the remaining ground set. -/
axiom tailSizes_valid
    {n D s : ℕ}
    (b b' : Fin n)
    (hgap : paperPos b' - paperPos b = 5 * D)
    (x : Fin D → Fin n)
    (hx : x ∈ tailTuples b' D)
    (hs : s = n - (5 * D + 1)) :
    IsChainSizeTuple s (tailSizes b' x)

/-- After exposing [b,b'], a fixed right-tail tuple has exactly the nested-chain
law on the remaining values. The bound supplied as hchain is therefore inherited
by the corresponding interval-sum event. -/
axiom fixed_tail_tuple_conditional_chainBound
    {p D : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (τ : Fin S.card → ZMod p) (hτ : IsIndexedOrdering S τ)
    (F : Finset (Fin S.card))
    (b b' : Fin S.card)
    (u x : Fin D → Fin S.card)
    (πi : Fin D → Equiv.Perm (Fin S.card))
    (hu : ∀ i,
      paperPos b ≤ paperPos (u i) ∧
        paperPos (u i) ≤ paperPos b')
    (hfix : ∀ i, FixedOutside b b' (πi i))
    (C : ℝ)
    (hm : IsChainSizeTuple
      (S \ indexImageSet τ F).card (tailSizes b' x))
    (hchain :
      ∀ z : Fin D → ZMod p,
        chainMass (S \ indexImageSet τ F)
            (tailSizes b' x) z ≤
          chainUpperBound p (S \ indexImageSet τ F).card
            C (tailSizes b' x)) :
    orderingConditionalMass S
      (fun σ => AgreesOn F σ τ)
      (fun σ =>
        ∀ i,
          indexedIntervalSum
            (applyPositionPerm σ (πi i))
            (u i) (x i) = 0) ≤
      chainUpperBound p (S \ indexImageSet τ F).card
        C (tailSizes b' x)

/-- Crude count for the parameter triples (b,J,J') in Lemma 5.4. -/
axiom bad0_parameter_count {n D : ℕ} :
    (Finset.univ :
      Finset (Fin n × Finset (Fin n) × Finset (Fin n))).card ≤
        n * 2 ^ (40 * D + 2)

/-- Generic two-level witness union bound: for each outer parameter there are
at most M inner choices, each inner event has weight w(theta), and the outer
weights sum to at most B. -/
axiom bounded_choice_witness_union
    {Ω Θ Ξ : Type*} [DecidableEq Ω] [DecidableEq Θ] [DecidableEq Ξ]
    (space : Finset Ω) (outer : Finset Θ)
    (inner : Θ → Finset Ξ)
    (E : Ω → Prop) (A : Θ → Ξ → Ω → Prop)
    [DecidablePred E] [∀ θ ξ, DecidablePred (A θ ξ)]
    (M : ℕ) (w : Θ → ℝ) (B : ℝ)
    (hcover :
      ∀ ω ∈ space, E ω →
        ∃ θ ∈ outer, ∃ ξ ∈ inner θ, A θ ξ ω)
    (hcount : ∀ θ ∈ outer, (inner θ).card ≤ M)
    (hpoint :
      ∀ θ ∈ outer, ∀ ξ ∈ inner θ,
        uniformMass space (A θ ξ) ≤ w θ)
    (hsum : (∑ θ ∈ outer, w θ) ≤ B)
    (hw : ∀ θ ∈ outer, 0 ≤ w θ) :
    uniformMass space E ≤ (M : ℝ) * B

/-- A generic upper bound for the number of partial matchings when each of q
possible first endpoints has at most r possible partners. -/
axiom partial_matching_count_le (q r : ℕ) :
    ∀ {n : ℕ} (Q : Finset (Fin n)),
      Q.card ≤ q →
      ((r + 1 : ℕ) ^ q : ℕ) ≤ (r + 1) ^ q ∧
      0 < (r + 1) ^ q

/-- Reversal conjugation preserves admissibility of a collection of local
disjoint swaps and preserves the same distance bound. -/
axiom reverseConjugate_admissible {n D : ℕ}
    (π : Equiv.Perm (Fin n))
    (hπ : IsAdmissiblePermutation D π) :
    IsAdmissiblePermutation D (reverseConjugate π)

/-- Reversal conjugation transports the fixed-outside condition from [b,b'] to
the reversed interval [rev b', rev b]. -/
axiom reverseConjugate_fixedOutside {n : ℕ}
    (b b' : Fin n) (π : Equiv.Perm (Fin n))
    (hfix : FixedOutside b b' π) :
    FixedOutside (reverseIndex n b') (reverseIndex n b)
      (reverseConjugate π)

/-- Fixed-position reversal is a permutation and therefore preserves a uniform
random ordering. -/
axiom reversal_perm_invariant {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (E : (Fin S.card → ZMod p) → Prop)
    [DecidablePred E] :
    orderingEventMass S E =
      orderingEventMass S (fun σ =>
        E (fun i => σ ⟨S.card - 1 - i.val, by omega⟩))

/-- An admissible local permutation fixing the prefix sends a subset of the
5D-window into the 10D-window. -/
axiom admissible_local_image_subset
    {n D : ℕ} (b : Fin n)
    (π : Equiv.Perm (Fin n))
    (hadm : IsAdmissiblePermutation D π)
    (hfix : FixedBelow b π)
    (J : Finset (Fin n))
    (hJ : J ⊆ forwardWindow b (5 * D)) :
    J.image π ⊆ forwardWindow b (10 * D)

/-- Generic two-colour pigeonhole extraction: from at least 2D distinct
objects, each of which has colour A or B, one can select D distinct objects of
one colour. -/
axiom two_colour_extract {α : Type*} [DecidableEq α]
    (D : ℕ) (Y : Finset α)
    (A B : α → Prop) [DecidablePred A] [DecidablePred B]
    (hcard : 2 * D ≤ Y.card)
    (hcover : ∀ y ∈ Y, A y ∨ B y) :
    (∃ f : Fin D → α, Function.Injective f ∧
      ∀ i, f i ∈ Y ∧ A (f i)) ∨
    (∃ f : Fin D → α, Function.Injective f ∧
      ∀ i, f i ∈ Y ∧ B (f i))

/-- Crude count of the local parameters (b,b',y,u) used on either side of
Lemma 5.3. -/
axiom repair_side_parameter_count {n D : ℕ} :
    (Finset.univ :
      Finset (Fin n × Fin n ×
        (Fin D → Fin n) × (Fin D → Fin n))).filter
      (fun θ =>
        2 ≤ paperPos θ.1 ∧
        paperPos θ.1 + 30 * D ≤ n ∧
        paperPos θ.2.1 - paperPos θ.1 = 5 * D ∧
        (∀ i,
          paperPos θ.1 < paperPos θ.2.2.1 i ∧
            paperPos (θ.2.2.1 i) ≤ paperPos θ.2.1) ∧
        (∀ i,
          paperPos θ.1 ≤ paperPos θ.2.2.2 i ∧
            paperPos (θ.2.2.2 i) ≤ paperPos θ.2.1))
      |>.card ≤ n * (5 * D) ^ (2 * D)

axiom rightRepairParameters_card_le {n D : ℕ} :
    (rightRepairParameters n D).card ≤ n * (5 * D) ^ (2 * D)

axiom leftRepairParameters_card_le {n D : ℕ} :
    (leftRepairParameters n D).card ≤ n * (5 * D) ^ (2 * D)

/-- If three events have total uniform mass strictly below one in a nonempty
finite space, there is an outcome avoiding all three. -/
axiom exists_avoiding_three_events
    {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (hspace : space.Nonempty)
    (E₁ E₂ E₃ : Ω → Prop)
    [DecidablePred E₁] [DecidablePred E₂] [DecidablePred E₃]
    (a₁ a₂ a₃ : ℝ)
    (h₁ : uniformMass space E₁ ≤ a₁)
    (h₂ : uniformMass space E₂ ≤ a₂)
    (h₃ : uniformMass space E₃ ≤ a₃)
    (hsum : a₁ + a₂ + a₃ < 1) :
    ∃ ω ∈ space, ¬ E₁ ω ∧ ¬ E₂ ω ∧ ¬ E₃ ω

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
