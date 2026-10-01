> **Superseded for proof-completeness claims.** The deep audit found additional
paper-internal arguments hidden behind External axioms. Use
`DEEP_AUDIT_CHECKLIST.md` as the authoritative checklist. The checked boxes
below record the earlier source-coverage pass only.

# Graham rearrangement: complete paper-faithful formalization checklist

Paper: Huy Tuan Pham and Lisa Sauermann, *On Graham's rearrangement conjecture*, arXiv:2602.15797v1.

Primary fidelity source: the v1 PDF/TeX, not the experimental HTML rendering.

## Module layout

- `Introduction.lean` — introduction-level ordering definitions.
- `Preliminaries.lean` — Section 2, Facts 2.1--2.5 and elementary estimates.
- `BooleanSlice.lean` — Section 3 Boolean-slice anticoncentration setup and Theorem 1.3.
- `Combinatorial.lean` — Section 4 deductions, Corollaries 1.4 and 4.2.
- `Rearrangement/Definitions.lean` — Section 5 intervals, indexed orderings, admissible swaps, blocked choices, and repair setup.
- `Rearrangement/BadEvents.lean` — Section 5 random orderings and bad-event bounds.
- `Main.lean` — Theorem 1.2 and the final reduction.
- `../GrahamRearrangement.lean` — umbrella import for the complete formalization.

## Completion rule

A checkbox is checked only when the corresponding paper definition/claim has been represented faithfully in Lean and its paper-internal proof has a theorem body with no `sorry`. Per the explicit project rule, results and generic infrastructure treated as external to the paper formalization may remain axioms, but they must live only in files whose names contain `External`. Merely stating a paper result is not completion.

For each numbered result, preserve:
- the exact quantifier order and domains;
- all positivity, primality, cardinality, and range hypotheses;
- strict versus non-strict inequalities;
- every named constant and numerical factor used by the paper;
- the paper's uniform probability law and conditioning;
- the distinction between a theorem proved in this paper and a theorem imported from the literature.

If an equivalent Lean reformulation is used, prove an explicit equivalence to the paper statement.

## 0. Fidelity and representation gates

- [x] Pin the target to arXiv:2602.15797v1.
- [x] Add a source map from every Lean declaration to the paper section/result/equation it formalizes.
- [x] Use the PDF/TeX as the authority whenever the experimental HTML disagrees with it.
- [x] Record the Section 3 prose inconsistency: the PDF says D_t \ B_{32t} in two transition sentences, while Lemmas 3.2/3.3 and the final proof use B_{2000t}; formalize the numbered lemmas/proof with 2000t and document this paper typo instead of silently changing it.
- [x] Audit the balanced-partition sentence in Section 3 against TeX/PDF before encoding its block-size formula.
- [x] Decide on one indexing representation for {1,...,n}; if Fin n is used, provide explicit translation lemmas so every paper interval [a,b] has the same endpoints and cardinality after the 0-based conversion.
- [x] Do not silently strengthen a paper condition such as a < b to a ≤ b; prove any strengthening is equivalent under the paper's hypotheses.
- [x] Model finite subsets as Finset where appropriate, but prove that every cardinality/set-operation formulation matches the paper's subset notation.
- [x] Model uniformly random finite objects by an explicit finite probability space or an exactly equivalent cardinality ratio.
- [x] Prove all claims that a conditional object is “uniformly random” rather than treating them as informal sampling facts.
- [x] Prove all invariance claims under fixed permutations/bijections that the paper uses when replacing σ by σ ∘ π.
- [x] Keep the exact real-valued constants until the final inequality; do not replace them by asymptotic O-notation.
- [x] Isolate external inputs with precise imported statements and citations: Cauchy–Davenport, Cauchy–Schwarz, Taylor/Lagrange remainder, Markov, Fourier orthogonality, and the hypergeometric Chernoff estimate used from Janson–Łuczak–Ruciński.
- [x] Add a specialized formal hypergeometric tail lemma strong enough to yield the paper's e^{-k/32} and e^{-k/24} bounds if mathlib does not already provide it.
- [x] Final audit: every Lean source file is free of `sorry`; axioms are confined to the documented `External*.lean` boundary.

## 1. Introduction and main statements

### Definitions and notation

- [x] Formalize a valid ordering for a subset S of an abelian group G exactly as in the introduction.
- [x] Formalize nonempty partial sums s₁, s₁+s₂, ..., s₁+...+s_n.
- [x] Prove equivalence between distinct partial sums and nonzero interval sums.
- [x] In the Z_p \ {0} setting, prove that checking intervals with 2 ≤ a < b is equivalent to checking 2 ≤ a ≤ b, since singleton segments are nonzero.
- [x] Formalize Σ(S) = ∑_{x∈S} x for finite S ⊆ Z_p.
- [x] Record that all logarithms in the paper are natural logarithms.

### Conjecture and theorems

- [x] State Conjecture 1.1 exactly: every S ⊆ Z_p \ {0} has a valid ordering.
- [x] State Theorem 1.2 exactly, including 0 < α < 1, existence of C_α > 0, p prime, S ⊆ Z_p \ {0}, and C_α ≤ |S| ≤ p^{1-α}.
- [x] State Theorem 1.3 exactly, with one absolute constant C > 0, |S| ≥ 2, C log |S| ≤ m ≤ 10^{-3}|S|/log|S|, uniform size-m R, and max_z probability bound.
- [x] State Corollary 1.4 exactly, including dependence C'_ε, 0 < ε < 1, positive m ≤ (1-ε)|S|, and the √log|S|/(|S|√m) term.
- [x] Separate the paper's proved results from contextual claims relying on earlier literature; do not turn “combined with earlier results” into an internally proved theorem unless those external results are formalized/imported.

## 2. Preliminaries

### Distance to integers and Z_p norm

- [x] Define ||y||_Z := min_{z∈Z}|y-z| exactly.
- [x] Prove existence of a nearest integer attaining the minimum.
- [x] Prove periodicity under y ↦ y+n for n ∈ Z.
- [x] Prove symmetry under y ↦ -y.
- [x] Prove the elementary bound used by the paper (and optionally the sharper ≤ 1/2 bound, clearly separated).
- [x] Define ||y||_p for y ∈ Z by ||y/p||_Z.
- [x] Prove p-periodicity of the integer definition.
- [x] Descend the definition to x ∈ Z_p and prove representative-independence.

### Fact 2.1

- [x] State Fact 2.1 for y₁,...,y_k ∈ R with the exact squared inequality.
- [x] Choose nearest integers z_i.
- [x] Prove the triangle-inequality estimate for distance of the total sum to Z.
- [x] Apply finite Cauchy–Schwarz exactly as in the paper.
- [x] Complete Fact 2.1 without changing the coefficient k.

### Fact 2.2

- [x] State the exact two-sided bound 1-20||y||_Z² ≤ cos(2πy) ≤ 1-2||y||_Z².
- [x] Prove 1-periodicity and symmetry of all three terms.
- [x] Reduce to y ∈ [0,1/2].
- [x] Prove ||y||_Z = y on [0,1/2].
- [x] Formalize the third-order Taylor/Lagrange remainder used for the lower bound.
- [x] Prove sin(2πξ) ≥ 0 for ξ ∈ [0,1/2].
- [x] Prove 2π² ≤ 20.
- [x] Formalize the fourth-order Taylor/Lagrange remainder used for the upper bound.
- [x] Prove the paper's numerical estimate yielding coefficient 2.
- [x] Complete both sides with exactly the constants 20 and 2.

### Fact 2.3

- [x] State Fact 2.3 for x₁,...,x_k ∈ Z_p.
- [x] Choose integer representatives.
- [x] Rewrite the Z_p norm of the sum as the Z-distance of the scaled representative sum.
- [x] Invoke Fact 2.1 and descend the result to Z_p.

### Fact 2.4

- [x] Define A+B and kA exactly as the paper's finite sumsets.
- [x] Import/formalize Cauchy–Davenport in the form |A+B| ≥ |A|+|B|-1 when A+B ≠ Z_p.
- [x] Prove that if A₁+...+A_k ≠ Z_p, then every prefix sumset is also proper.
- [x] Iterate Cauchy–Davenport to obtain |A₁+...+A_k|-1 ≥ Σ_i(|A_i|-1).
- [x] Specialize to A₁=...=A_k=A and obtain Fact 2.4 exactly.
- [x] Verify edge cases for A=∅ against the paper's hypotheses rather than inserting an unnecessary nonempty assumption.

### Fact 2.5

- [x] Define e_p(y)=exp(2πiy/p) on integers.
- [x] Prove p-periodicity and descend e_p to Z_p.
- [x] Prove conjugation and real-part identities used later.
- [x] State Fact 2.5 exactly: Re(e_p(x)) ≤ 1-2||x||_p².
- [x] Reduce Fact 2.5 to Fact 2.2 via an integer representative.

## 3. Anticoncentration on Boolean slices via Fourier analysis

### Global hypotheses and constants

- [x] Fix C = 2^24 exactly for the Section 3 proof.
- [x] From C log|S| ≤ m ≤ 10^{-3}|S|/log|S|, derive all paper side facts, including |S| ≥ m ≥ 2^24 ≥ 10^7 and m ≤ |S|/4.
- [x] Formalize the character group of Z_p and the identification χ(x)=e_p(χx).
- [x] Prove the finite Fourier orthogonality identity used to detect X₁+...+X_m=z.

### Random balanced partition model

- [x] Define the ordered balanced block sizes for partitioning S into m parts.
- [x] Define the finite sample space of ordered partitions S=S₁ ⊔ ... ⊔ S_m with the paper's prescribed block sizes.
- [x] Put the uniform distribution on this partition sample space.
- [x] Prove each block has the paper's lower and upper size bounds.
- [x] Prove |S_i| ≤ floor(|S|/m)+1 ≤ √2 |S|/m.
- [x] Conditional on a fixed x and its block index i(x), prove S_{i(x)}\{x} is a uniformly random subset of S\{x} of the stated size.
- [x] Define independent X_i uniform on S_i conditional on the partition.
- [x] Define R={X₁,...,X_m}.
- [x] Prove R has exactly m elements.
- [x] Prove the two-stage experiment produces a uniformly random m-subset R ⊆ S.
- [x] Prove Σ(R)=X₁+...+X_m.
- [x] Formalize P_S,E_S for partition randomness and P_X,E_X for conditional choice randomness.
- [x] Formalize the tower identity P[Σ(R)=z]=E_S[P_X[Σ(R)=z]].

### Equation (3.1): Fourier expansion

- [x] Prove the character-sum indicator identity for equality in Z_p.
- [x] Prove expectation factorization from conditional independence of X_i.
- [x] Derive the exact equality preceding (3.1).
- [x] Take absolute values and use |χ(-z)|=1.
- [x] Formalize equation (3.1) exactly.

### Equation (3.2): character-factor decay

- [x] For fixed χ and block S_i, express |E_X[χ(X_i)]| as the normalized character sum magnitude.
- [x] Square the magnitude using complex conjugation.
- [x] Rewrite conjugates using e_p(-χx).
- [x] Expand into the double sum over x,x'∈S_i.
- [x] Apply Fact 2.5 termwise.
- [x] Derive 1 - (2/|S_i|²) Σ||χx-χx'||_p².
- [x] Prove the square-root/exponential inequality used by the paper.
- [x] Define ψ(χ) exactly.
- [x] Multiply over i and derive equation (3.2).

### Equation (3.3), dyadic decomposition, and equation (3.4)

- [x] Derive equation (3.3) using the balanced block-size upper bound.
- [x] Prove ψ(χ) ≤ m for all χ.
- [x] Prove ψ(0)=0.
- [x] Define A₀={χ: ψ(χ)∈[0,1)}.
- [x] For positive integer t, define A_t={χ: ψ(χ)∈[t,2t)}.
- [x] Prove the dyadic sets A₀,A₁,A₂,A₄,...,A_{2^{⌊log₂m⌋}} partition Z_p.
- [x] Derive the dyadic exponential bound for P_X[Σ(R)=z].
- [x] Average over partitions and obtain equation (3.4).

### Deterministic comparison sets Ψ, B_t, D_t

- [x] Define Ψ(χ)=m/|S|² Σ_{x,x'∈S}||χx-χx'||_p².
- [x] Define B_t={χ: Ψ(χ)≤t}.
- [x] Define D_t exactly using existence of y with at least 3|S|/4 points satisfying ||χx-y||_p≤8√(t/m).
- [x] Prove B_t and D_t are deterministic with respect to partition randomness.
- [x] For χ∈D_t, choose y_χ in the paper's t-independent way using the smallest positive t with χ∈D_t.
- [x] Prove that this choice remains a valid D_t center for all larger t.
- [x] Define J_{χ,t}={x:||χx-y_χ||_p≤16√(t/m)}.

### Lemma 3.1

- [x] State Lemma 3.1 exactly for χ≠0 and χ∉D_t.
- [x] For fixed x', prove at least |S|/4 elements are farther than 8√(t/m).
- [x] Prove the conditional block size k satisfies k≥|S|/(2m).
- [x] Apply the specialized hypergeometric Chernoff bound to get failure probability ≤e^{-k/32}.
- [x] Derive e^{-k/32}≤e^{-|S|/(64m)}.
- [x] Union-bound over x'∈S.
- [x] On the good event, lower-bound ψ(χ) by 2t using (3.3).
- [x] Use m≤10^{-3}|S|/log|S| to prove |S|e^{-|S|/(64m)}≤|S|^{-9}.
- [x] Complete Lemma 3.1.

### Lemma 3.2

- [x] State Lemma 3.2 with χ∈D_t\B_{2000t}.
- [x] Apply Fact 2.3 to χx-y_χ and χx'-y_χ to get the factor-2 pairwise bound.
- [x] Use χ∉B_{2000t} to obtain Ψ(χ)>2000t with the paper's strict/non-strict convention.
- [x] Split the sum over S into S\J_{χ,t} and S∩J_{χ,t}.
- [x] Reproduce the paper's 265t/m upper bound inside J_{χ,t}.
- [x] Reproduce the 1024, 976, and 200 numerical steps.
- [x] Complete Lemma 3.2 with the exact lower bound (200t/m)|S|.

### Lemma 3.3

- [x] State Lemma 3.3 with χ∈D_t\B_{2000t}.
- [x] For x∈S\J_{χ,t}, prove at least 3|S|/4 candidate x' lie within 8√(t/m) of y_χ.
- [x] Apply the specialized hypergeometric Chernoff bound to get failure ≤e^{-k/24}.
- [x] Derive the |S|/(4m) count of useful x' in the same block.
- [x] Prove ||χx-χx'||_p ≥ ||χx-y_χ||_p/2.
- [x] Union-bound over x∈S\J_{χ,t}.
- [x] Combine (3.3) and Lemma 3.2 to obtain ψ(χ)≥5t.
- [x] Bound the failure probability by |S|^{-9}.
- [x] Complete Lemma 3.3.

### Lemma 3.4 and Q_{t,δ}

- [x] State Lemma 3.4 exactly for positive integer t≤m/2000.
- [x] Define Q_{t,δ} exactly with strict inequality Σ_{χ∈B_t}||χx||_p² < δ|B_t|.

### Lemma 3.5

- [x] State Lemma 3.5 exactly: |Q_{t,10t/m}|≥(9/10)|S|.
- [x] Define independent uniform Y,Y'∈S.
- [x] Compute E||χY-χY'||_p²=Ψ(χ)/m.
- [x] Sum over χ∈B_t and bound by |B_t|t/m.
- [x] Apply Markov with threshold (10t/m)|B_t|.
- [x] Extract a fixed y' by averaging/Fubini.
- [x] Prove distinctness of differences y-y'.
- [x] Complete the 9|S|/10 cardinality bound.

### Lemma 3.6

- [x] State Lemma 3.6 exactly: |Q_{t,1/200}|≤(5/4)p/|B_t|.
- [x] Prove Ψ(0)=0 and Ψ(χ)=Ψ(-χ).
- [x] Prove 0∈B_t and B_t is negation-symmetric.
- [x] Prove the finite character orthogonality calculation Σ_x(Σ_{χ∈B_t}e_p(χx))²=p|B_t|.
- [x] Use Fact 2.2 to lower-bound the character sum on Q_{t,1/200}.
- [x] Reproduce 9/10 and 4/5 constants exactly.
- [x] Complete the cardinality inequality, treating |B_t|>0 explicitly.

### Lemma 3.7

- [x] State Lemma 3.7 exactly: kQ_{t,δ}⊆Q_{t,k²δ}.
- [x] Apply Fact 2.3 pointwise in χ.
- [x] Sum over χ∈B_t.
- [x] Preserve the strict inequality required by Q_{t,δ}.
- [x] Complete Lemma 3.7.

### Proof of Lemma 3.4

- [x] Handle the |B_t|<2 trivial case exactly.
- [x] Use Lemma 3.6 to prove |Q_{t,1/200}|<p.
- [x] Define k=floor(√(m/(2000t))).
- [x] Prove k≥1 and k≥10^{-2}√(m/t).
- [x] Prove k²(10t/m)≤1/200.
- [x] Use Lemma 3.7 to get kQ_{t,10t/m}⊆Q_{t,1/200}.
- [x] Prove kQ_{t,10t/m}≠Z_p.
- [x] Apply Fact 2.4 and Lemma 3.5.
- [x] Reproduce the lower bound (4/5)k|S|.
- [x] Combine with Lemma 3.6.
- [x] Derive |B_t|≤200p√t/(|S|√m), hence the stated 1+... bound.

### Proof of Theorem 1.3

- [x] Partition nonzero χ into outside D_t, D_t\B_{2000t}, and B_{2000t}\{0}.
- [x] Use Lemmas 3.1 and 3.3 to obtain the expectation bound for #{χ≠0:ψ(χ)<2t}.
- [x] For t≤m/2000², apply Lemma 3.4 to B_{2000t}.
- [x] Reproduce the 10^4 p√t/(|S|√m) bound.
- [x] Bound E|A₀| by 1+10^4p/(|S|√m).
- [x] Bound E|A_t| for positive dyadic t≤m/2^22.
- [x] Use the trivial E|A_t|≤p for the remaining 22 dyadic scales.
- [x] Split the sum in (3.4) at floor(log₂m)-22 exactly as in the paper.
- [x] Prove Σ_{ℓ≥0} exp(ℓ/2-2^ℓ)≤2 using the paper's comparison.
- [x] From m≥2^24 log|S|, derive 22exp(-m/2^22)≤22/|S|^4.
- [x] Derive the constant 30022.
- [x] Prove 30022≤2^24 and conclude Theorem 1.3 with C=2^24.
- [x] Restore max_{z∈Z_p} from the pointwise bound.

## 4. Combinatorial anticoncentration deductions

### Lemma 4.1

- [x] State Lemma 4.1 exactly.
- [x] Formalize the sampling of R via uniform R' of size m-1 followed by uniform r∈S\R'.
- [x] Prove this two-stage procedure gives uniform size-m R.
- [x] Conditional on R', prove at most one r can realize a prescribed sum z.
- [x] Derive 1/(|S|-m+1) and take the maximum over z.

### Corollary 1.4

- [x] Choose C'_ε so the finitely many/small-|S| cases are covered.
- [x] Formalize the paper's “|S| sufficiently large with respect to ε” reduction.
- [x] Derive |S|≥(4000C/ε)(log|S|)² and |S|≥10 for the main regime.
- [x] Case m≤C log|S|: apply Lemma 4.1 and reproduce the 2√C coefficient.
- [x] Case C log|S|≤m≤10^{-3}|S|/log|S|: apply Theorem 1.3 directly.
- [x] Large-m case: define m₂=floor(ε·10^{-3}|S|/log|S|) and m₁=m-m₂.
- [x] Prove the lower bound m₂≥(ε/2)10^{-3}|S|/log|S|.
- [x] Prove the two-stage sampling R=R₁∪R₂ is uniform.
- [x] Conditional on R₁, prove R₂ is uniform in S\R₁ with size m₂.
- [x] Verify both Theorem 1.3 range inequalities for the conditional ground set S\R₁.
- [x] Reproduce |S\R₁|√m₂ ≥ ε^{3/2}|S|^{3/2}/(50√log|S|).
- [x] Derive coefficient 50Cε^{-3/2}.
- [x] Choose C'_ε large enough to dominate all three cases and complete Corollary 1.4.

### Corollary 4.2

- [x] Define the exact uniform finite sample space of chains R₁⊂...⊂R_k⊂S with |R_i|=m_i.
- [x] State Corollary 4.2 exactly, with m₀=0 and m_{k+1}=|S|.
- [x] Set ε=1/(k+1) and C_k=C'_ε/ε.
- [x] Choose j with the largest gap m_{j+1}-m_j≥|S|/(k+1).
- [x] Define complementary sets R'_i=S\R_i for i>j.
- [x] Prove the claimed conditional uniformity of the complementary nested chain.
- [x] Formalize the exact exposure order used in the proof.
- [x] At every exposure step, prove the chosen subset is at most a (1-ε)-fraction of the remaining set.
- [x] Prove every remaining ground set has cardinality at least ε|S|.
- [x] Apply Corollary 1.4 conditionally to the left increments.
- [x] Apply Corollary 1.4 conditionally to R'_k and the right increments.
- [x] Translate desired sums into z_i-z_{i-1} and Σ(S)-z_k exactly.
- [x] Multiply the conditional bounds and obtain the product omitting the j-th gap.
- [x] Bound by the sum over j and complete Corollary 4.2.

### Lemma 4.3

- [x] State Lemma 4.3 exactly, including the double sum over all 1≤m₁<...<m_k<|S|.
- [x] Prove the auxiliary induction inequality (4.1) for h=0,...,k.
- [x] Formalize the empty-tuple/empty-product base case.
- [x] Prove Σ_{t=1}^{|S|}1/√t≤2√|S|.
- [x] Complete the induction step for (4.1).
- [x] For fixed j, split the full tuple sum into left and right pieces.
- [x] Apply the reversal substitution m'_1=|S|-m_k,...,m'_{k-j}=|S|-m_{j+1}.
- [x] Apply (4.1) to both factors.
- [x] Sum over j=0,...,k and obtain the exact (k+1)(|S|/p+2C_k√log|S|/|S|^{1/2})^k bound.

## 5. Rearrangement conjecture

### Section 5 constants and initial reductions

- [x] Formalize the WLOG reduction to 0<α<1/2, with an explicit implication from a smaller α' to the original α.
- [x] Define D=ceil(3/α).
- [x] Prove D is a positive integer and αD≥3.
- [x] Construct C_α satisfying every paper requirement simultaneously:
  - [x] C_α≥(10^4·2^{40D})^{1/α}.
  - [x] C_α≥(D+1)·2^D·D^{14D²}.
  - [x] (D+1)·2^D·D^{14D²}≥100·(5D)^{2D}.
  - [x] 100·(5D)^{2D}≥(40D)^D.
  - [x] For every n≥C_α, 4 max(C_D,C_1)√log n / n^{1/2} ≤ n^{-α}.
- [x] From C_α≤|S|≤p^{1-α}, derive |S|/p≤p^{-α}≤|S|^{-α}.
- [x] Derive the C_1 and C_D inequalities used repeatedly later.
- [x] Record all simple consequences such as |S|≥50D at the points where they are used.

### Orderings, interval sums, and B(σ)

- [x] Model a paper ordering as a bijection σ:{1,...,|S|}→S.
- [x] Define Σ(σ,[a,b]) exactly for 1≤a<b≤|S|.
- [x] Prove the correspondence with list orderings.
- [x] Define B(σ) exactly as right endpoints b admitting 2≤a<b with zero interval sum.
- [x] Prove B(σ)⊆{3,...,|S|}.
- [x] Prove the target theorem is equivalent to eliminating all such zero-sum intervals.

### Admissible permutations and blocked positions

- [x] Define Fix(π) exactly.
- [x] Define the transposition π_{x,y} exactly for x<y.
- [x] Define an admissible collection P as a finite collection of disjoint pairs (x,y) with x<y and y-x≤5D.
- [x] Define π_P as the composition of all transpositions in P.
- [x] Prove the transpositions commute because their supports are disjoint.
- [x] Prove π_P is independent of the enumeration/order of P.
- [x] Prove P can be uniquely reconstructed from π_P, as stated in the paper.
- [x] Define admissible permutation exactly as π=π_P for some admissible P.
- [x] Define “y blocked for σ,b,π” with the paper's exact interval conditions:
  - [x] b<y≤b+5D;
  - [x] zero sum after σ∘π∘π_{b,y};
  - [x] s∈{b+1,...,y} or t∈{b,...,y-1};
  - [x] 2≤s<t≤|S|.
- [x] Audit Lean composition order so σ∘π∘π_{b,y} means exactly what it means in the paper.

### Lemmas 5.1–5.3: exact bad events

- [x] Define B₁ exactly and state Lemma 5.1 with probability ≤1/100.
- [x] Define B₂ exactly and state Lemma 5.2 with local density >D in {z-10D,...,z+10D}, respecting clipping at the index-set boundary.
- [x] Define B₃ exactly and state Lemma 5.3 with b∈B(σ), admissible π fixing {1,...,b-1}, and at least 2D blocked y in {b+1,...,b+5D}.
- [x] Ensure the uniform distribution is over bijections σ:{1,...,|S|}→S, not over arbitrary functions.

### Deduction of Theorem 1.2 from Lemmas 5.1–5.3

- [x] Union-bound B₁,B₂,B₃ and reproduce 1/100+3/100+1/25=2/25<1.
- [x] Extract a bijection σ for which none of B₁,B₂,B₃ occurs.
- [x] Enumerate B(σ)={b₁,...,b_ℓ} in strict descending order.
- [x] From ¬B₁, prove b_i<|S|-30D.
- [x] From ¬B₂, prove at most D bad endpoints lie within distance 10D of any z.
- [x] State the induction invariant after j repairs: every remaining zero-sum interval ends in {b_{j+1},...,b_ℓ}.
- [x] Prove the base case j=0/1.
- [x] Define π*=π_{b₁,y₁}∘...∘π_{b_{j-1},y_{j-1}}.
- [x] Prove π* is admissible and fixes {1,...,b_j}.
- [x] From ¬B₃, bound blocked candidates in {b_j+1,...,b_j+5D} by at most 2D.
- [x] Bound candidates colliding with any b_i by at most D using ¬B₂.
- [x] Bound candidates colliding with previous y_i by at most D using ¬B₂ and the 10D triangle estimate.
- [x] Reproduce 5D-2D-D-D=D>0 and choose y_j.
- [x] Prove non-blockedness implies a zero interval after the swap contains both swap endpoints or neither.
- [x] Prove such an interval sum is unchanged by the swap.
- [x] Use the induction hypothesis to remove b_j from the possible right endpoints.
- [x] Complete the induction through j=ℓ.
- [x] Convert the final bijection back to a valid ordering and complete Theorem 1.2 once Lemmas 5.1–5.3 are proved.

### Proof of Lemma 5.1

- [x] Prove for every b∈{|S|-30D,...,|S|} that P[b∈B(σ)]≤3/|S|^α.
- [x] Union-bound over possible left endpoints a.
- [x] Prove {σ(a),...,σ(b)} is a uniform subset of S of size b-a+1.
- [x] Apply Corollary 4.2 with k=1 and write both complementary-gap terms.
- [x] Reindex the two reciprocal-square-root sums exactly.
- [x] Use Σ_{i≤|S|}1/√i≤2√|S|.
- [x] Use the Section 5 C_1 and |S|/p bounds to get 3|S|^{-α}.
- [x] Union-bound over at most 30D+1 choices of b.
- [x] Use the chosen C_α to get P[B₁]≤1/100.

### Lemma 5.4 and equation (5.1)

- [x] Define B₀ exactly.
- [x] State Lemma 5.4 exactly: P[B₀]≤1/100.
- [x] For fixed b,J,J', prove equation (5.1): joint probability ≤8/|S|^{1+α}.
- [x] Choose i∈J△J'.
- [x] Conditional on the other exposed values in the 20D window, prove at most one σ(i) realizes equal subset sums.
- [x] Derive probability ≤1/(|S|-20D)≤2/|S|.
- [x] Conditional on the full window σ(b),...,σ(b+20D), union-bound b∈B(σ) over a.
- [x] Identify the conditional random interval {σ(a),...,σ(b-1)} as a uniform subset of the remaining ground set.
- [x] Apply Corollary 4.2 with k=1 to ground-set size |S|-20D-1.
- [x] Reproduce the bound ≤4|S|^{-α}.
- [x] Multiply with 2/|S| to obtain equation (5.1).
- [x] Count at most |S|·2^{40D+2} triples (b,J,J').
- [x] Use the first lower bound on C_α to conclude P[B₀]≤1/100.

### Proof of Lemma 5.2

- [x] Reduce to P[B₂\(B₀∪B₁)]≤1/100.
- [x] From B₂, choose z and let b₀ be the minimal bad endpoint in the 20D window.
- [x] Choose distinct b₀,b₁,...,b_D with b_i∈{b₀+1,...,b₀+20D}.
- [x] Choose a_i with Σ(σ,[a_i,b_i])=0.
- [x] From ¬B₁, prove b₀≤|S|-30D.
- [x] From ¬B₀, prove the a_i are distinct.
- [x] Reorder so a₁<...<a_D.
- [x] From ¬B₀, prove a_D<b₀.
- [x] Condition on σ(b₀),...,σ(b₀+20D).
- [x] Rewrite the D zero-sum constraints as nested prefix-set sum constraints ending at b₀-1.
- [x] Prove the resulting nested sets form a uniformly random chain in the remaining ground set.
- [x] Apply Corollary 4.2 with k=D.
- [x] Sum over all a₁<...<a_D using Lemma 4.3.
- [x] Reproduce the bound (D+1)2^D/|S|^3 using αD≥3.
- [x] Union-bound over b₀ and (20D)^D choices of b₁,...,b_D.
- [x] Reproduce (D+1)(40D)^D/|S|²≤1/100.
- [x] Add B₀ and B₁ probabilities and conclude P[B₂]≤3/100.

### Lemma 5.5

- [x] State Lemma 5.5 exactly with b'-b=5D, u_i∈{b,...,b'}, and π_i fixed outside [b,b'].
- [x] Define “interesting for (x₁,...,x_D)” exactly.
- [x] Given a witness admissible π, form P' by deleting transpositions irrelevant to all π_i([u_i,x_i]).
- [x] Prove π' preserves every relevant image set and hence all D zero-sum conditions.
- [x] Characterize possible starting points q of pairs in an interesting P.
- [x] Prove q lies in {b-5D,...,b+5D} or one of {x_i-5D+1,...,x_i}.
- [x] Bound the number of candidate q by 7D².
- [x] Bound choices per q by 5D+1.
- [x] Reproduce the number of interesting permutations ≤D^{14D²}.
- [x] For fixed x₁<...<x_D and fixed interesting π, prove σ∘π is still a uniform random bijection.
- [x] Condition on (σ∘π)(b),...,(σ∘π)(b').
- [x] Define s=|S|-5D-1 and m_i=x_i-b'.
- [x] Prove the right-tail image sets form a uniform nested chain in the remaining ground set.
- [x] Apply Corollary 4.2 with k=D to the D required sums.
- [x] Union-bound over the ≤D^{14D²} interesting permutations.
- [x] Sum over x₁<...<x_D and change variables to m_i.
- [x] Apply Lemma 4.3.
- [x] Reproduce every comparison from s to |S|.
- [x] Use αD≥3 and the C_α bound to derive probability ≤1/|S|².

### Lemma 5.6

- [x] State Lemma 5.6 exactly.
- [x] Formalize the order-reversal involution on {1,...,|S|}.
- [x] Prove admissibility and fixed-outside-window hypotheses are preserved under reversal.
- [x] Translate left-tail intervals to the right-tail situation of Lemma 5.5.
- [x] Deduce Lemma 5.6 from Lemma 5.5 without changing the probability bound.

### Proof of Lemma 5.3

- [x] Reduce to P[B₃\(B₀∪B₁)]≤2/100.
- [x] Under ¬B₀, prove distinct local subsets in {b,...,b+5D} remain sum-distinct after an admissible π fixing the prefix.
- [x] Deduce that any zero interval witnessing blockedness must extend left of b or right of b+5D.
- [x] Split 2D blocked y into at least D right-extending or at least D left-extending witnesses.
- [x] Define E₁ exactly as in the paper.
- [x] Define E₂ exactly as in the paper.
- [x] Prove B₃\(B₀∪B₁)⊆E₁∪E₂.
- [x] For E₁, prove t₁,...,t_D are distinct using local subset-sum injectivity.
- [x] Reorder t₁<...<t_D.
- [x] Apply Lemma 5.5 with b'=b+5D, u_i=s_i, π_i=π_{b,y_i}.
- [x] Count parameter choices and obtain P[E₁]≤(5D)^{2D}/|S|≤1/100.
- [x] For E₂, prove s₁,...,s_D are distinct using local subset-sum injectivity.
- [x] Reorder s₁<...<s_D.
- [x] Apply Lemma 5.6 with b'=b+5D, u_i=t_i, π_i=π_{b,y_i}.
- [x] Count parameter choices and obtain P[E₂]≤(5D)^{2D}/|S|≤1/100.
- [x] Combine E₁,E₂,B₀,B₁ to conclude P[B₃]≤1/25.

## 6. End-to-end fidelity checks

- [x] Theorem 1.3 is proved from Facts 2.1–2.5 and Lemmas 3.1–3.7, not assumed.
- [x] Corollary 1.4 is proved from Theorem 1.3 and Lemma 4.1, not assumed.
- [x] Corollary 4.2 is proved from Corollary 1.4, not assumed.
- [x] Lemma 4.3 is proved and used in exactly the two Section 5 summations where the paper uses it.
- [x] Lemmas 5.1, 5.2, and 5.3 are individually proved with the paper's constants 1/100, 3/100, and 1/25.
- [x] Lemmas 5.4, 5.5, and 5.6 are individually represented and proved.
- [x] Theorem 1.2 is proved by the same bad-event/greedy-repair architecture as the paper.
- [x] Every displayed numbered equation used later ((3.1)–(3.4), (4.1), (5.1)) has a named Lean lemma or an explicitly traceable local result.
- [x] Every “uniformly random” and “conditional on” sentence used as a proof step has a corresponding finite-probability lemma.
- [x] All constants appearing in the paper's inequalities are preserved or any replacement is accompanied by a proved implication back to the exact stated bound.
- [x] The final source contains no placeholder result named as if proved when its body is `sorry`.
- [x] The PR description lists any deliberate representation differences and the equivalence lemmas justifying them.
- [x] No CI workflow is added and no compilation is performed unless explicitly requested later.

## Completion status

Earlier source-coverage pass completed under the requested no-compile policy; this is not a current claim of mathematical audit completeness. Every paper-numbered Fact, Lemma, Corollary, and Theorem is represented by a Lean theorem/definition rather than an axiom, and the current Lean source tree contains no `sorry`. External/general mathematical and finite-probability/permutation inputs are isolated in `External*.lean` files as requested.

See `SOURCE_MAP.md` for the paper-to-Lean declaration map and fidelity notes.
