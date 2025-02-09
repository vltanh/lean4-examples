import Mathlib

open Set Topology

def KTopologicalSpace [StdTopo : TopologicalSpace X] (K : Set X) : TopologicalSpace X where
  IsOpen s :=
    -- An open set in the K-topology can be written in the form U \ B
    -- where U is open in the standard topology and B ⊆ K.
    ∃ U B, (IsOpen[StdTopo] U) ∧ (B ⊆ K) ∧ (s = U \ B)
  isOpen_univ := by
    -- Let U = ℝ and B = ∅.
    use univ, ∅
    -- We have:
    --   U = ℝ is open in the standard topology,
    --   B = ∅ ⊆ K, and
    --   ℝ = ℝ \ ∅ = U \ B.
    -- Thus, ℝ is open in the K-topology.
    exact ⟨StdTopo.isOpen_univ, empty_subset K, diff_empty.symm⟩
  isOpen_inter := by
    -- Suppose two sets Uₛ \ Bₛ and Uₜ \ Bₜ are open in the K-topology
    -- where Uₛ, Uₜ be open sets in the standard topology
    -- and Bₛ, Bₜ ⊆ K.
    rintro s t ⟨Us, Bs, hUs, hBsK, rfl⟩ ⟨Ut, Bt, hUt, hBtK, rfl⟩
    -- Let U = Us ∩ Ut and B = Bs ∪ Bt.
    use Us ∩ Ut, Bs ∪ Bt
    constructor
    · -- Since a finite intersection of open sets is open,
      -- U = Uₛ ∩ Uₜ is open in the standard topology
      exact StdTopo.isOpen_inter Us Ut hUs hUt
    · constructor
      · -- Since Bₛ, Bₜ ⊆ K, B = Bₛ ∪ Bₜ ⊆ K.
        exact union_subset hBsK hBtK
      · -- (Uₛ \ Bₛ) ∩ (Uₜ \ Bₜ) = (Uₛ ∩ Bₛᶜ) ∩ (Uₜ ∩ Bₜᶜ)
        --                       = (Uₛ ∩ Uₜ) ∩ (Bₛᶜ ∩ Bₜᶜ)
        --                       = (Uₛ ∩ Uₜ) ∩ (Bₛ ∪ Bₜ)ᶜ
        --                       = (Uₛ ∩ Uₜ) \ (Bₛ ∪ Bₜ)
        rw [diff_eq, diff_eq, inter_inter_inter_comm, ← compl_union, ← diff_eq]
  isOpen_sUnion := by
    -- Let S be a collection of subsets of ℝ.
    -- Suppose each s ∈ S is of the form Uₛ \ Bₛ
    -- for some open set Uₛ and some subset Bₛ ⊆ K.
    intro S hS
    choose! U B hU hB hUB using hS
    -- Let U = ⋃ s ∈ S, Uₛ and B = K \ ⋃ S.
    use (⋃ s ∈ S, U s), K \ (⋃₀ S)
    -- We need to show 3 things:
    --   1. U is open in the standard topology.
    --   2. B ⊆ K.
    --   3. ⋃ S = U \ B.
    constructor
    · -- 1. Show: U is open in the standard topology.
      -- Since each Uₛ is open in the standard topology,
      -- U = ⋃ s ∈ S, Uₛ is open in the standard topology.
      rw [← sUnion_image]
      apply StdTopo.isOpen_sUnion
      rintro V ⟨U', hU'S, rfl⟩
      exact hU U' hU'S
    · constructor
      · -- 2. Show: B ⊆ K.
        -- B = K \ ⋃ S, so B ⊆ K.
        exact diff_subset
      · -- 3. Show: ⋃ S = U \ B.
        -- U \ B = (⋃ s ∈ S, Uₛ) \ (K \ ⋃ S)
        --       = (⋃ s ∈ S, Uₛ) ∩ (K \ ⋃ S)ᶜ
        --       = (⋃ s ∈ S, Uₛ) ∩ (K ∩ (⋃ S)ᶜ)ᶜ
        --       = (⋃ s ∈ S, Uₛ) ∩ (Kᶜ ∪ (⋃ S)ᶜᶜ)
        --       = (⋃ s ∈ S, Uₛ) ∩ (Kᶜ ∪ ⋃ S)
        --       = (⋃ s ∈ S, Uₛ) ∩ Kᶜ ∪ (⋃ s ∈ S, Uₛ) ∩ ⋃ S
        --       = (⋃ s ∈ S, Uₛ) \ K ∪ (⋃ s ∈ S, Uₛ) ∩ ⋃ S
        rw [diff_eq, diff_eq, compl_inter, compl_compl, inter_union_distrib_left, ← diff_eq]

        -- Show: ⋃ S ⊆ ⋃ s ∈ S, Uₛ
        have h₁ : ⋃₀ S ⊆ ⋃ s ∈ S, U s := by
          -- Let x ∈ ⋃ S. Then, ∃ s ∈ S, x ∈ Uₛ \ Bₛ.
          rintro x ⟨s, hsS, hxs⟩
          rw [hUB s hsS] at hxs
          -- Then, ∃ s ∈ S, x ∈ Uₛ. Thus, x ∈ ⋃ s ∈ S, Uₛ.
          rw [← sUnion_image]
          use U s, mem_image_of_mem U hsS, mem_of_mem_diff hxs
        -- U \ B = (⋃ s ∈ S, Uₛ) \ K ∪ ⋃ S
        rw [inter_eq_self_of_subset_right h₁]

        -- Show: (⋃ s ∈ S, Uₛ) \ K ⊆ ⋃ S
        have h₂ : (⋃ s ∈ S, U s) \ K ⊆ ⋃₀ S := by
          -- Let x ∈ (⋃ s ∈ S, Uₛ) \ K. Then, x ∈ ⋃ s ∈ S, Uₛ and x ∉ K.
          -- Thus, ∃ s ∈ S, x ∈ Uₛ. Consider this s.
          intro x hx
          rw [← sUnion_image] at hx
          rcases hx with ⟨⟨_, ⟨s, hsS, rfl⟩, hxUs⟩, hnxK⟩
          -- We can show that x ∉ Bₛ since x ∉ K and Bₛ ⊆ K.
          have hxnBs : x ∉ B s := fun hxBs ↦ hnxK (hB s hsS hxBs)
          -- Thus, x ∈ Uₛ \ Bₛ.
          -- In other words, ∃ s ∈ S, x ∈ Uₛ \ Bₛ ∈ S.
          -- Therefore, x ∈ ⋃ S.
          use s, hsS
          rw [hUB s hsS]
          exact mem_diff_of_mem hxUs hxnBs
        -- U \ B = ⋃ S
        rw [union_eq_self_of_subset_left h₂]

-- The K-topology on ℝ is Hausdorff.
example [StdTopo: TopologicalSpace X] [StdT2: T2Space X] (K : Set X)
  : @T2Space X (KTopologicalSpace K) := by
  -- A topological space is Hausdorff if for any two distinct points x, y ∈ X,
  -- there exist disjoint open sets U, V ∈ X such that x ∈ U and y ∈ V.
  rw [t2Space_iff]
  -- Let x, y ∈ X be distinct points.
  -- Show: there exist disjoint sets U, V ∈ X such that
  -- U, V are open with respect to the K-topology and
  -- x ∈ U and y ∈ V.
  intro x y hxy
  -- Since X with the standard topology is Hausdorff,
  -- there exist disjoint sets U, V ∈ X such that
  -- U, V are open with respect to the standard topology and
  -- x ∈ U and y ∈ V.
  rcases StdT2.t2 hxy with ⟨U, V, hU, hV, hxU, hyV, hUV⟩
  -- Since U, V are open with respect to the standard topology,
  -- U, V are open with respect to the K-topology.
  have hK {S : Set X} (h : IsOpen[StdTopo] S) : IsOpen[KTopologicalSpace K] S :=
    ⟨S, ∅, h, empty_subset K, diff_empty.symm⟩
  -- Thus, U, V are the sets we are looking for.
  use U, V, hK hU, hK hV, hxU, hyV, hUV

-- Define K = {1 / (n + 1) : n ∈ ℕ}.
def K : Set ℝ := range (fun (n : ℕ) => 1 / (n + 1))

-- Show that there is no irrational number in K.
lemma Irrat_notin_K : ∀ x : ℝ, Irrational x → x ∉ K := by
  -- Let x ∈ ℝ be an irrational number.
  intro x hx
  -- Suppose x ∈ K.
  by_contra! hxK
  -- Then, x can be written as 1 / (n + 1) for some natural number n.
  rcases mem_range.mp hxK with ⟨n, rfl⟩
  -- Then, 1 / (n + 1) is irrational. This is a contradiction.
  rw [Irrational] at hx
  apply hx
  use 1 / (n + 1)
  rw [Rat.cast_div, Rat.cast_one, Rat.cast_add, Rat.cast_one, Rat.cast_natCast]

example : ¬ @RegularSpace ℝ (KTopologicalSpace K) := by
  -- We prove by contradiction.
  -- Suppose the K-topology on ℝ is regular.
  by_contra! h
  -- Then, for all closed set F in the K-topology and all x ∉ F,
  -- x and F admit disjoint neighborhoods.
  rw [regularSpace_iff] at h

  -- We show that K is closed in the K-topology.
  have hK : IsClosed[KTopologicalSpace K] K := by
    -- Note that Kᶜ = ℝ \ K =: U \ B.
    -- We have
    --   U = ℝ is open in the standard topology,
    --   K ⊆ K, and
    --   Kᶜ = ℝ \ K.
    -- Thus, Kᶜ is open in the K-topology,
    -- which implies K is closed in the K-topology.
    use univ, K
    exact ⟨isOpen_univ, refl K, compl_eq_univ_diff K⟩

  -- We show that 0 is not in K.
  have h0nK : 0 ∉ K := by
    -- Suppose 0 ∈ K.
    by_contra! h0K
    -- Then, 0 can be written as 1 / (n + 1) for some natural number n.
    rcases mem_range.mp h0K with ⟨n, hn⟩
    -- Since 1 / (n + 1) = 0, either 1 = 0 or n + 1 = 0.
    rcases (div_eq_zero_iff.mp hn) with (h' | h')
    · -- 1 = 0 is contradictory.
      exact one_ne_zero h'
    · -- n + 1 is the successor of a natural number.
      -- Thus, n + 1 ≠ 0. So n + 1 = 0 is contradictory.
      rw [← Nat.cast_succ, Nat.cast_eq_zero] at h'
      exact Nat.succ_ne_zero n h'

  -- Since K is closed in the K-topology and 0 ∉ K,
  -- 0 and K admit disjoint neighborhoods.
  -- Then, there exist disjoint sets U, V
  -- such that K is in the neighborhood of U
  -- and 0 is in the neighborhood of V.
  rcases Filter.disjoint_iff.mp (h hK h0nK) with ⟨U, hU, ⟨V, hV, hUV⟩⟩

  -- We show that if a set U is in the neighborhood of a point x,
  -- then there exists a radius ε > 0 such that the open interval (x - ε, x + ε)
  -- excluding points of K, i.e. (x - ε, x + ε) \ K, is a subset of U.
  have aux {x : ℝ} {U : Set ℝ} (hUx : U ∈ @nhds ℝ (KTopologicalSpace K) x) :
    ∃ ε > 0, Ioo (x - ε) (x + ε) \ K ⊆ U := by
    -- Let U be in the neighborhood of x.
    -- Then, there exists an open set U' ⊆ U in the K-topology such that x ∈ U'.
    rw [@mem_nhds_iff ℝ x U (KTopologicalSpace K)] at hUx
    rcases hUx with ⟨U', hU'U, hU', hxU'⟩
    -- Since U' is open in the K-topology,
    -- there exists an open set U'' in the standard topology
    -- and a subset B'' ⊆ K such that U' = U'' \ B''.
    rw [isOpen_mk] at hU'
    rcases hU' with ⟨U'', B'', hU'', hB''K, rfl⟩
    -- We show that there exists ε > 0 such that (x - ε, x + ε) ⊆ U''.
    have : ∃ ε > 0, Ioo (x - ε) (x + ε) ⊆ U'' := by
      -- Since x ∈ U' = U'' \ B'', x ∈ U''.
      -- Since U'' is open in the standard topology and x ∈ U'',
      -- U'' is in the neighborhood of x.
      have : U'' ∈ 𝓝 x := (IsOpen.mem_nhds_iff hU'').mpr (mem_of_mem_diff hxU')
      -- On ℝ, this implies there exists l < u
      -- such that x ∈ (l, u) ⊆ U''.
      rw [mem_nhds_iff_exists_Ioo_subset] at this
      rcases this with ⟨l, u, ⟨hl, hu⟩, hIluU'⟩
      -- Let ε = min {x - l, u - x}. Then ε ≤ x - l and ε ≤ u - x.
      use min (x - l) (u - x)
      constructor
      · -- Since l < x, x - l > 0. Similarly, u - x > 0. Thus, ε > 0.
        exact lt_min (sub_pos.mpr hl) (sub_pos.mpr hu)
      · -- Let y ∈ (x - ε, x + ε).
        rintro y ⟨hyleft, hyright⟩
        -- Then, l = x - (x - l) ≤ x - ε < y.
        have hly := calc
          l = x - (x - l) := (sub_sub_self x l).symm
          _ ≤ x - min (x - l) (u - x) := sub_le_sub_left (min_le_left (x - l) (u - x)) x
          _ < y := hyleft
        -- On the other hand, y < x + ε ≤ x + (u - x) = u.
        have hyu := calc
          y < x + min (x - l) (u - x) := hyright
          _ ≤ x + (u - x) := add_le_add_left (min_le_right (x - l) (u - x)) x
          _ = u := add_sub_cancel x u
        -- Thus, y ∈ (l, u) ⊆ U''.
        exact hIluU' ⟨hly, hyu⟩
    rcases this with ⟨ε, hε, hIU''⟩
    -- Use this ε as the radius.
    use ε, hε
    -- Let y ∈ (x - ε, x + ε) \ K. Then, y ∈ (x - ε, x + ε) and y ∉ K.
    rintro y ⟨hyI, hynK⟩
    -- Since y ∈ (x - ε, x + ε), y ∈ U''.
    -- Since y ∉ K ⊇ B'', y ∉ B''.
    -- Thus, y ∈ U'' \ B'' = U' ⊆ U.
    exact hU'U (mem_diff_of_mem (hIU'' hyI) (fun hyB'' ↦ hynK (hB''K hyB'')))

  -- Apply the auxiliary lemma to V, which is in the neighborhood of 0.
  -- Then, there exists ε > 0 such that
  -- (-ε, ε) \ K ⊆ V.
  rcases aux hV with ⟨ε, hε, hIdKV⟩
  rw [zero_sub, zero_add] at hIdKV
  -- Since ε > 0, there exists a natural number n such that 1 / (n + 1) < ε.
  rcases exists_nat_one_div_lt hε with ⟨n, hn⟩
  -- Let x = 1 / (n + 1).
  let x := 1 / ((n : ℝ) + 1)
  -- Then, x ∈ K.
  have hxK : x ∈ K := mem_range.mpr ⟨n, rfl⟩

  -- Since U is in the neighborhood of K,
  -- there exists an open set U' in the K-topology such that
  -- K ⊆ U' ⊆ U.
  rw [@mem_nhdsSet_iff_exists ℝ (KTopologicalSpace K) U K] at hU
  rcases hU with ⟨U', hU', hKU', hU'U⟩
  -- Since U' is open in the K-topology,
  -- for every point y ∈ U', U' is in the neighborhood of y.
  rw [@isOpen_iff_mem_nhds] at hU'
  -- Since x ∈ K ⊆ U' ⊆ U, x ∈ U. Thus, U' is in the neighborhood of x.
  -- Apply the auxiliary lemma to U', there exists ε' > 0 such that
  -- (x - ε', x + ε') \ K ⊆ U'.
  rcases aux (hU' x (hKU' hxK)) with ⟨ε', hε', hIdKU'⟩

  -- If (x - ε', x + ε') and (-ε, ε) intersect
  -- at a point t that is not in K, i.e.,
  -- ∃ t ∈ (x - ε', x + ε') ∩ (-ε, ε) \ K, then
  -- t ∈ (x - ε', x + ε') \ K ⊆ U' ⊆ U and
  -- t ∈ (-ε, ε) \ K ⊆ V and so
  -- U and V are not disjoint, which is a contradiction.
  have aux2 {t : ℝ} (htnK : t ∉ K) :
    ¬ (t ∈ Ioo (x - ε') (x + ε') ∧ t ∈ Ioo (-ε) ε) := by
    push_neg
    intro htUK htVK
    rw [disjoint_left] at hUV
    apply hUV
      (hU'U (hIdKU' (mem_diff_of_mem htUK htnK)))
      (hIdKV (mem_diff_of_mem htVK htnK))

  -- We show that such a point t exists.
  -- Consider two cases: x - ε' ≤ -ε and x - ε' > -ε.
  by_cases hεε' : x - ε' ≤ -ε
  · -- Case 1: x - ε' ≤ -ε.
    -- We know that 0 ∉ K.
    -- Since x - ε' ≤ -ε < 0, x - ε' < 0.
    -- Since x = 1 / (n + 1) > 0, x + ε' > 0.
    -- Thus, 0 ∈ (x - ε', x + ε').
    -- On the other hand, it is obvious that 0 ∈ (-ε, ε).
    -- Thus, 0 ∈ (x - ε', x + ε') ∩ (-ε, ε) and 0 ∉ K.
    exact aux2 h0nK ⟨
      ⟨
        lt_of_le_of_lt hεε' (neg_neg_iff_pos.mpr hε),
        gt_trans (lt_add_of_pos_right x hε') (Nat.one_div_pos_of_nat)
      ⟩,
      ⟨neg_neg_iff_pos.mpr hε, hε⟩
    ⟩
  · -- Cases 2: x - ε' > -ε.
    push_neg at hεε'
    -- Since x - ε' < x, there exists an irrational number r ∈ (x - ε', x).
    rcases exists_irrational_btwn (sub_lt_self x hε') with ⟨r, hr, h1r, hr1⟩
    -- An irrational number cannot be in the form 1 / (n + 1). Thus, r ∉ K.
    -- Since r ∈ (x - ε', x) ⊆ (x - ε', x + ε'), r ∈ (x - ε', x + ε').
    -- Since r > x - ε' > -ε, r > -ε. On the other hand, r < x < ε. Thus, r ∈ (-ε, ε).
    -- Therefore, r ∈ (x - ε', x + ε') ∩ (-ε, ε) and r ∉ K.
    exact aux2 (Irrat_notin_K r hr) ⟨
      ⟨h1r, lt_add_of_lt_of_pos hr1 hε'⟩,
      ⟨gt_trans h1r hεε', gt_trans hn hr1⟩
    ⟩
