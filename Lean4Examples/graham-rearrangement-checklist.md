# Graham rearrangement: complete paper-faithful formalization checklist

Paper: Huy Tuan Pham and Lisa Sauermann, *On Graham's rearrangement conjecture*, arXiv:2602.15797v1.

Primary fidelity source: the v1 PDF/TeX, not the experimental HTML rendering.

## Completion rule

A checkbox is checked only when the corresponding paper definition/claim has been represented faithfully in Lean and every proof obligation for that item is discharged without `sorry`, `axiom`, or an unproved replacement hypothesis. Merely stating a proposition is not completion.

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
- [ ] Add a source map from every Lean declaration to the paper section/result/equation it formalizes.
- [ ] Use the PDF/TeX as the authority whenever the experimental HTML disagrees with it.
- [ ] Record the Section 3 prose inconsistency: the PDF says D_t \ B_{32t} in two transition sentences, while Lemmas 3.2/3.3 and the final proof use B_{2000t}; formalize the numbered lemmas/proof with 2000t and document this paper typo instead of silently changing it.
- [ ] Audit the balanced-partition sentence in Section 3 against TeX/PDF before encoding its block-size formula.
- [ ] Decide on one indexing representation for {1,...,n}; if Fin n is used, provide explicit translation lemmas so every paper interval [a,b] has the same endpoints and cardinality after the 0-based conversion.
- [ ] Do not silently strengthen a paper condition such as a < b to a ≤ b; prove any strengthening is equivalent under the paper's hypotheses.
- [ ] Model finite subsets as Finset where appropriate, but prove that every cardinality/set-operation formulation matches the paper's subset notation.
- [ ] Model uniformly random finite objects by an explicit finite probability space or an exactly equivalent cardinality ratio.
- [ ] Prove all claims that a conditional object is “uniformly random” rather than treating them as informal sampling facts.
- [ ] Prove all invariance claims under fixed permutations/bijections that the paper uses when replacing σ by σ ∘ π.
- [ ] Keep the exact real-valued constants until the final inequality; do not replace them by asymptotic O-notation.
- [ ] Isolate external inputs with precise imported statements and citations: Cauchy–Davenport, Cauchy–Schwarz, Taylor/Lagrange remainder, Markov, Fourier orthogonality, and the hypergeometric Chernoff estimate used from Janson–Łuczak–Ruciński.
- [ ] Add a specialized formal hypergeometric tail lemma strong enough to yield the paper's e^{-k/32} and e^{-k/24} bounds if mathlib does not already provide it.
- [ ] Final audit: every occurrence of `sorry` or custom axiom in the paper formalization has been eliminated.

## 1. Introduction and main statements

### Definitions and notation

- [ ] Formalize a valid ordering for a subset S of an abelian group G exactly as in the introduction.
- [ ] Formalize nonempty partial sums s₁, s₁+s₂, ..., s₁+...+s_n.
- [ ] Prove equivalence between distinct partial sums and nonzero interval sums.
- [ ] In the Z_p \ {0} setting, prove that checking intervals with 2 ≤ a < b is equivalent to checking 2 ≤ a ≤ b, since singleton segments are nonzero.
- [ ] Formalize Σ(S) = ∑_{x∈S} x for finite S ⊆ Z_p.
- [ ] Record that all logarithms in the paper are natural logarithms.

### Conjecture and theorems

- [ ] State Conjecture 1.1 exactly: every S ⊆ Z_p \ {0} has a valid ordering.
- [ ] State Theorem 1.2 exactly, including 0 < α < 1, existence of C_α > 0, p prime, S ⊆ Z_p \ {0}, and C_α ≤ |S| ≤ p^{1-α}.
- [ ] State Theorem 1.3 exactly, with one absolute constant C > 0, |S| ≥ 2, C log |S| ≤ m ≤ 10^{-3}|S|/log|S|, uniform size-m R, and max_z probability bound.
- [ ] State Corollary 1.4 exactly, including dependence C'_ε, 0 < ε < 1, positive m ≤ (1-ε)|S|, and the √log|S|/(|S|√m) term.
- [ ] Separate the paper's proved results from contextual claims relying on earlier literature; do not turn “combined with earlier results” into an internally proved theorem unless those external results are formalized/imported.

## 2. Preliminaries

### Distance to integers and Z_p norm

- [ ] Define ||y||_Z := min_{z∈Z}|y-z| exactly.
- [ ] Prove existence of a nearest integer attaining the minimum.
- [ ] Prove periodicity under y ↦ y+n for n ∈ Z.
- [ ] Prove symmetry under y ↦ -y.
- [ ] Prove the elementary bound used by the paper (and optionally the sharper ≤ 1/2 bound, clearly separated).
- [ ] Define ||y||_p for y ∈ Z by ||y/p||_Z.
- [ ] Prove p-periodicity of the integer definition.
- [ ] Descend the definition to x ∈ Z_p and prove representative-independence.

### Fact 2.1

- [ ] State Fact 2.1 for y₁,...,y_k ∈ R with the exact squared inequality.
- [ ] Choose nearest integers z_i.
- [ ] Prove the triangle-inequality estimate for distance of the total sum to Z.
- [ ] Apply finite Cauchy–Schwarz exactly as in the paper.
- [ ] Complete Fact 2.1 without changing the coefficient k.

### Fact 2.2

- [ ] State the exact two-sided bound 1-20||y||_Z² ≤ cos(2πy) ≤ 1-2||y||_Z².
- [ ] Prove 1-periodicity and symmetry of all three terms.
- [ ] Reduce to y ∈ [0,1/2].
- [ ] Prove ||y||_Z = y on [0,1/2].
- [ ] Formalize the third-order Taylor/Lagrange remainder used for the lower bound.
- [ ] Prove sin(2πξ) ≥ 0 for ξ ∈ [0,1/2].
- [ ] Prove 2π² ≤ 20.
- [ ] Formalize the fourth-order Taylor/Lagrange remainder used for the upper bound.
- [ ] Prove the paper's numerical estimate yielding coefficient 2.
- [ ] Complete both sides with exactly the constants 20 and 2.

### Fact 2.3

- [ ] State Fact 2.3 for x₁,...,x_k ∈ Z_p.
- [ ] Choose integer representatives.
- [ ] Rewrite the Z_p norm of the sum as the Z-distance of the scaled representative sum.
- [ ] Invoke Fact 2.1 and descend the result to Z_p.

### Fact 2.4

- [ ] Define A+B and kA exactly as the paper's finite sumsets.
- [ ] Import/formalize Cauchy–Davenport in the form |A+B| ≥ |A|+|B|-1 when A+B ≠ Z_p.
- [ ] Prove that if A₁+...+A_k ≠ Z_p, then every prefix sumset is also proper.
- [ ] Iterate Cauchy–Davenport to obtain |A₁+...+A_k|-1 ≥ Σ_i(|A_i|-1).
- [ ] Specialize to A₁=...=A_k=A and obtain Fact 2.4 exactly.
- [ ] Verify edge cases for A=∅ against the paper's hypotheses rather than inserting an unnecessary nonempty assumption.

### Fact 2.5

- [ ] Define e_p(y)=exp(2πiy/p) on integers.
- [ ] Prove p-periodicity and descend e_p to Z_p.
- [ ] Prove conjugation and real-part identities used later.
- [ ] State Fact 2.5 exactly: Re(e_p(x)) ≤ 1-2||x||_p².
- [ ] Reduce Fact 2.5 to Fact 2.2 via an integer representative.

## 3. Anticoncentration on Boolean slices via Fourier analysis

### Global hypotheses and constants

- [ ] Fix C = 2^24 exactly for the Section 3 proof.
- [ ] From C log|S| ≤ m ≤ 10^{-3}|S|/log|S|, derive all paper side facts, including |S| ≥ m ≥ 2^24 ≥ 10^7 and m ≤ |S|/4.
- [ ] Formalize the character group of Z_p and the identification χ(x)=e_p(χx).
- [ ] Prove the finite Fourier orthogonality identity used to detect X₁+...+X_m=z.

### Random balanced partition model

- [ ] Define the ordered balanced block sizes for partitioning S into m parts.
- [ ] Define the finite sample space of ordered partitions S=S₁ ⊔ ... ⊔ S_m with the paper's prescribed block sizes.
- [ ] Put the uniform distribution on this partition sample space.
- [ ] Prove each block has the paper's lower and upper size bounds.
- [ ] Prove |S_i| ≤ floor(|S|/m)+1 ≤ √2 |S|/m.
- [ ] Conditional on a fixed x and its block index i(x), prove S_{i(x)}\{x} is a uniformly random subset of S\{x} of the stated size.
- [ ] Define independent X_i uniform on S_i conditional on the partition.
- [ ] Define R={X₁,...,X_m}.
- [ ] Prove R has exactly m elements.
- [ ] Prove the two-stage experiment produces a uniformly random m-subset R ⊆ S.
- [ ] Prove Σ(R)=X₁+...+X_m.
- [ ] Formalize P_S,E_S for partition randomness and P_X,E_X for conditional choice randomness.
- [ ] Formalize the tower identity P[Σ(R)=z]=E_S[P_X[Σ(R)=z]].

### Equation (3.1): Fourier expansion

- [ ] Prove the character-sum indicator identity for equality in Z_p.
- [ ] Prove expectation factorization from conditional independence of X_i.
- [ ] Derive the exact equality preceding (3.1).
- [ ] Take absolute values and use |χ(-z)|=1.
- [ ] Formalize equation (3.1) exactly.

### Equation (3.2): character-factor decay

- [ ] For fixed χ and block S_i, express |E_X[χ(X_i)]| as the normalized character sum magnitude.
- [ ] Square the magnitude using complex conjugation.
- [ ] Rewrite conjugates using e_p(-χx).
- [ ] Expand into the double sum over x,x'∈S_i.
- [ ] Apply Fact 2.5 termwise.
- [ ] Derive 1 - (2/|S_i|²) Σ||χx-χx'||_p².
- [ ] Prove the square-root/exponential inequality used by the paper.
- [ ] Define ψ(χ) exactly.
- [ ] Multiply over i and derive equation (3.2).

### Equation (3.3), dyadic decomposition, and equation (3.4)

- [ ] Derive equation (3.3) using the balanced block-size upper bound.
- [ ] Prove ψ(χ) ≤ m for all χ.
- [ ] Prove ψ(0)=0.
- [ ] Define A₀={χ: ψ(χ)∈[0,1)}.
- [ ] For positive integer t, define A_t={χ: ψ(χ)∈[t,2t)}.
- [ ] Prove the dyadic sets A₀,A₁,A₂,A₄,...,A_{2^{⌊log₂m⌋}} partition Z_p.
- [ ] Derive the dyadic exponential bound for P_X[Σ(R)=z].
- [ ] Average over partitions and obtain equation (3.4).

### Deterministic comparison sets Ψ, B_t, D_t

- [ ] Define Ψ(χ)=m/|S|² Σ_{x,x'∈S}||χx-χx'||_p².
- [ ] Define B_t={χ: Ψ(χ)≤t}.
- [ ] Define D_t exactly using existence of y with at least 3|S|/4 points satisfying ||χx-y||_p≤8√(t/m).
- [ ] Prove B_t and D_t are deterministic with respect to partition randomness.
- [ ] For χ∈D_t, choose y_χ in the paper's t-independent way using the smallest positive t with χ∈D_t.
- [ ] Prove that this choice remains a valid D_t center for all larger t.
- [ ] Define J_{χ,t}={x:||χx-y_χ||_p≤16√(t/m)}.

### Lemma 3.1

- [ ] State Lemma 3.1 exactly for χ≠0 and χ∉D_t.
- [ ] For fixed x', prove at least |S|/4 elements are farther than 8√(t/m).
- [ ] Prove the conditional block size k satisfies k≥|S|/(2m).
- [ ] Apply the specialized hypergeometric Chernoff bound to get failure probability ≤e^{-k/32}.
- [ ] Derive e^{-k/32}≤e^{-|S|/(64m)}.
- [ ] Union-bound over x'∈S.
- [ ] On the good event, lower-bound ψ(χ) by 2t using (3.3).
- [ ] Use m≤10^{-3}|S|/log|S| to prove |S|e^{-|S|/(64m)}≤|S|^{-9}.
- [ ] Complete Lemma 3.1.

### Lemma 3.2

- [ ] State Lemma 3.2 with χ∈D_t\B_{2000t}.
- [ ] Apply Fact 2.3 to χx-y_χ and χx'-y_χ to get the factor-2 pairwise bound.
- [ ] Use χ∉B_{2000t} to obtain Ψ(χ)>2000t with the paper's strict/non-strict convention.
- [ ] Split the sum over S into S\J_{χ,t} and S∩J_{χ,t}.
- [ ] Reproduce the paper's 265t/m upper bound inside J_{χ,t}.
- [ ] Reproduce the 1024, 976, and 200 numerical steps.
- [ ] Complete Lemma 3.2 with the exact lower bound (200t/m)|S|.

### Lemma 3.3

- [ ] State Lemma 3.3 with χ∈D_t\B_{2000t}.
- [ ] For x∈S\J_{χ,t}, prove at least 3|S|/4 candidate x' lie within 8√(t/m) of y_χ.
- [ ] Apply the specialized hypergeometric Chernoff bound to get failure ≤e^{-k/24}.
- [ ] Derive the |S|/(4m) count of useful x' in the same block.
- [ ] Prove ||χx-χx'||_p ≥ ||χx-y_χ||_p/2.
- [ ] Union-bound over x∈S\J_{χ,t}.
- [ ] Combine (3.3) and Lemma 3.2 to obtain ψ(χ)≥5t.
- [ ] Bound the failure probability by |S|^{-9}.
- [ ] Complete Lemma 3.3.

### Lemma 3.4 and Q_{t,δ}

- [ ] State Lemma 3.4 exactly for positive integer t≤m/2000.
- [ ] Define Q_{t,δ} exactly with strict inequality Σ_{χ∈B_t}||χx||_p² < δ|B_t|.

### Lemma 3.5

- [ ] State Lemma 3.5 exactly: |Q_{t,10t/m}|≥(9/10)|S|.
- [ ] Define independent uniform Y,Y'∈S.
- [ ] Compute E||χY-χY'||_p²=Ψ(χ)/m.
- [ ] Sum over χ∈B_t and bound by |B_t|t/m.
- [ ] Apply Markov with threshold (10t/m)|B_t|.
- [ ] Extract a fixed y' by averaging/Fubini.
- [ ] Prove distinctness of differences y-y'.
- [ ] Complete the 9|S|/10 cardinality bound.

### Lemma 3.6

- [ ] State Lemma 3.6 exactly: |Q_{t,1/200}|≤(5/4)p/|B_t|.
- [ ] Prove Ψ(0)=0 and Ψ(χ)=Ψ(-χ).
- [ ] Prove 0∈B_t and B_t is negation-symmetric.
- [ ] Prove the finite character orthogonality calculation Σ_x(Σ_{χ∈B_t}e_p(χx))²=p|B_t|.
- [ ] Use Fact 2.2 to lower-bound the character sum on Q_{t,1/200}.
- [ ] Reproduce 9/10 and 4/5 constants exactly.
- [ ] Complete the cardinality inequality, treating |B_t|>0 explicitly.

### Lemma 3.7

- [ ] State Lemma 3.7 exactly: kQ_{t,δ}⊆Q_{t,k²δ}.
- [ ] Apply Fact 2.3 pointwise in χ.
- [ ] Sum over χ∈B_t.
- [ ] Preserve the strict inequality required by Q_{t,δ}.
- [ ] Complete Lemma 3.7.

### Proof of Lemma 3.4

- [ ] Handle the |B_t|<2 trivial case exactly.
- [ ] Use Lemma 3.6 to prove |Q_{t,1/200}|<p.
- [ ] Define k=floor(√(m/(2000t))).
- [ ] Prove k≥1 and k≥10^{-2}√(m/t).
- [ ] Prove k²(10t/m)≤1/200.
- [ ] Use Lemma 3.7 to get kQ_{t,10t/m}⊆Q_{t,1/200}.
- [ ] Prove kQ_{t,10t/m}≠Z_p.
- [ ] Apply Fact 2.4 and Lemma 3.5.
- [ ] Reproduce the lower bound (4/5)k|S|.
- [ ] Combine with Lemma 3.6.
- [ ] Derive |B_t|≤200p√t/(|S|√m), hence the stated 1+... bound.

### Proof of Theorem 1.3

- [ ] Partition nonzero χ into outside D_t, D_t\B_{2000t}, and B_{2000t}\{0}.
- [ ] Use Lemmas 3.1 and 3.3 to obtain the expectation bound for #{χ≠0:ψ(χ)<2t}.
- [ ] For t≤m/2000², apply Lemma 3.4 to B_{2000t}.
- [ ] Reproduce the 10^4 p√t/(|S|√m) bound.
- [ ] Bound E|A₀| by 1+10^4p/(|S|√m).
- [ ] Bound E|A_t| for positive dyadic t≤m/2^22.
- [ ] Use the trivial E|A_t|≤p for the remaining 22 dyadic scales.
- [ ] Split the sum in (3.4) at floor(log₂m)-22 exactly as in the paper.
- [ ] Prove Σ_{ℓ≥0} exp(ℓ/2-2^ℓ)≤2 using the paper's comparison.
- [ ] From m≥2^24 log|S|, derive 22exp(-m/2^22)≤22/|S|^4.
- [ ] Derive the constant 30022.
- [ ] Prove 30022≤2^24 and conclude Theorem 1.3 with C=2^24.
- [ ] Restore max_{z∈Z_p} from the pointwise bound.

## 4. Combinatorial anticoncentration deductions

### Lemma 4.1

- [ ] State Lemma 4.1 exactly.
- [ ] Formalize the sampling of R via uniform R' of size m-1 followed by uniform r∈S\R'.
- [ ] Prove this two-stage procedure gives uniform size-m R.
- [ ] Conditional on R', prove at most one r can realize a prescribed sum z.
- [ ] Derive 1/(|S|-m+1) and take the maximum over z.

### Corollary 1.4

- [ ] Choose C'_ε so the finitely many/small-|S| cases are covered.
- [ ] Formalize the paper's “|S| sufficiently large with respect to ε” reduction.
- [ ] Derive |S|≥(4000C/ε)(log|S|)² and |S|≥10 for the main regime.
- [ ] Case m≤C log|S|: apply Lemma 4.1 and reproduce the 2√C coefficient.
- [ ] Case C log|S|≤m≤10^{-3}|S|/log|S|: apply Theorem 1.3 directly.
- [ ] Large-m case: define m₂=floor(ε·10^{-3}|S|/log|S|) and m₁=m-m₂.
- [ ] Prove the lower bound m₂≥(ε/2)10^{-3}|S|/log|S|.
- [ ] Prove the two-stage sampling R=R₁∪R₂ is uniform.
- [ ] Conditional on R₁, prove R₂ is uniform in S\R₁ with size m₂.
- [ ] Verify both Theorem 1.3 range inequalities for the conditional ground set S\R₁.
- [ ] Reproduce |S\R₁|√m₂ ≥ ε^{3/2}|S|^{3/2}/(50√log|S|).
- [ ] Derive coefficient 50Cε^{-3/2}.
- [ ] Choose C'_ε large enough to dominate all three cases and complete Corollary 1.4.

### Corollary 4.2

- [ ] Define the exact uniform finite sample space of chains R₁⊂...⊂R_k⊂S with |R_i|=m_i.
- [ ] State Corollary 4.2 exactly, with m₀=0 and m_{k+1}=|S|.
- [ ] Set ε=1/(k+1) and C_k=C'_ε/ε.
- [ ] Choose j with the largest gap m_{j+1}-m_j≥|S|/(k+1).
- [ ] Define complementary sets R'_i=S\R_i for i>j.
- [ ] Prove the claimed conditional uniformity of the complementary nested chain.
- [ ] Formalize the exact exposure order used in the proof.
- [ ] At every exposure step, prove the chosen subset is at most a (1-ε)-fraction of the remaining set.
- [ ] Prove every remaining ground set has cardinality at least ε|S|.
- [ ] Apply Corollary 1.4 conditionally to the left increments.
- [ ] Apply Corollary 1.4 conditionally to R'_k and the right increments.
- [ ] Translate desired sums into z_i-z_{i-1} and Σ(S)-z_k exactly.
- [ ] Multiply the conditional bounds and obtain the product omitting the j-th gap.
- [ ] Bound by the sum over j and complete Corollary 4.2.

### Lemma 4.3

- [ ] State Lemma 4.3 exactly, including the double sum over all 1≤m₁<...<m_k<|S|.
- [ ] Prove the auxiliary induction inequality (4.1) for h=0,...,k.
- [ ] Formalize the empty-tuple/empty-product base case.
- [ ] Prove Σ_{t=1}^{|S|}1/√t≤2√|S|.
- [ ] Complete the induction step for (4.1).
- [ ] For fixed j, split the full tuple sum into left and right pieces.
- [ ] Apply the reversal substitution m'_1=|S|-m_k,...,m'_{k-j}=|S|-m_{j+1}.
- [ ] Apply (4.1) to both factors.
- [ ] Sum over j=0,...,k and obtain the exact (k+1)(|S|/p+2C_k√log|S|/|S|^{1/2})^k bound.

## 5. Rearrangement conjecture

### Section 5 constants and initial reductions

- [ ] Formalize the WLOG reduction to 0<α<1/2, with an explicit implication from a smaller α' to the original α.
- [ ] Define D=ceil(3/α).
- [ ] Prove D is a positive integer and αD≥3.
- [ ] Construct C_α satisfying every paper requirement simultaneously:
  - [ ] C_α≥(10^4·2^{40D})^{1/α}.
  - [ ] C_α≥(D+1)·2^D·D^{14D²}.
  - [ ] (D+1)·2^D·D^{14D²}≥100·(5D)^{2D}.
  - [ ] 100·(5D)^{2D}≥(40D)^D.
  - [ ] For every n≥C_α, 4 max(C_D,C_1)√log n / n^{1/2} ≤ n^{-α}.
- [ ] From C_α≤|S|≤p^{1-α}, derive |S|/p≤p^{-α}≤|S|^{-α}.
- [ ] Derive the C_1 and C_D inequalities used repeatedly later.
- [ ] Record all simple consequences such as |S|≥50D at the points where they are used.

### Orderings, interval sums, and B(σ)

- [ ] Model a paper ordering as a bijection σ:{1,...,|S|}→S.
- [ ] Define Σ(σ,[a,b]) exactly for 1≤a<b≤|S|.
- [ ] Prove the correspondence with list orderings.
- [ ] Define B(σ) exactly as right endpoints b admitting 2≤a<b with zero interval sum.
- [ ] Prove B(σ)⊆{3,...,|S|}.
- [ ] Prove the target theorem is equivalent to eliminating all such zero-sum intervals.

### Admissible permutations and blocked positions

- [ ] Define Fix(π) exactly.
- [ ] Define the transposition π_{x,y} exactly for x<y.
- [ ] Define an admissible collection P as a finite collection of disjoint pairs (x,y) with x<y and y-x≤5D.
- [ ] Define π_P as the composition of all transpositions in P.
- [ ] Prove the transpositions commute because their supports are disjoint.
- [ ] Prove π_P is independent of the enumeration/order of P.
- [ ] Prove P can be uniquely reconstructed from π_P, as stated in the paper.
- [ ] Define admissible permutation exactly as π=π_P for some admissible P.
- [ ] Define “y blocked for σ,b,π” with the paper's exact interval conditions:
  - [ ] b<y≤b+5D;
  - [ ] zero sum after σ∘π∘π_{b,y};
  - [ ] s∈{b+1,...,y} or t∈{b,...,y-1};
  - [ ] 2≤s<t≤|S|.
- [ ] Audit Lean composition order so σ∘π∘π_{b,y} means exactly what it means in the paper.

### Lemmas 5.1–5.3: exact bad events

- [ ] Define B₁ exactly and state Lemma 5.1 with probability ≤1/100.
- [ ] Define B₂ exactly and state Lemma 5.2 with local density >D in {z-10D,...,z+10D}, respecting clipping at the index-set boundary.
- [ ] Define B₃ exactly and state Lemma 5.3 with b∈B(σ), admissible π fixing {1,...,b-1}, and at least 2D blocked y in {b+1,...,b+5D}.
- [ ] Ensure the uniform distribution is over bijections σ:{1,...,|S|}→S, not over arbitrary functions.

### Deduction of Theorem 1.2 from Lemmas 5.1–5.3

- [ ] Union-bound B₁,B₂,B₃ and reproduce 1/100+3/100+1/25=2/25<1.
- [ ] Extract a bijection σ for which none of B₁,B₂,B₃ occurs.
- [ ] Enumerate B(σ)={b₁,...,b_ℓ} in strict descending order.
- [ ] From ¬B₁, prove b_i<|S|-30D.
- [ ] From ¬B₂, prove at most D bad endpoints lie within distance 10D of any z.
- [ ] State the induction invariant after j repairs: every remaining zero-sum interval ends in {b_{j+1},...,b_ℓ}.
- [ ] Prove the base case j=0/1.
- [ ] Define π*=π_{b₁,y₁}∘...∘π_{b_{j-1},y_{j-1}}.
- [ ] Prove π* is admissible and fixes {1,...,b_j}.
- [ ] From ¬B₃, bound blocked candidates in {b_j+1,...,b_j+5D} by at most 2D.
- [ ] Bound candidates colliding with any b_i by at most D using ¬B₂.
- [ ] Bound candidates colliding with previous y_i by at most D using ¬B₂ and the 10D triangle estimate.
- [ ] Reproduce 5D-2D-D-D=D>0 and choose y_j.
- [ ] Prove non-blockedness implies a zero interval after the swap contains both swap endpoints or neither.
- [ ] Prove such an interval sum is unchanged by the swap.
- [ ] Use the induction hypothesis to remove b_j from the possible right endpoints.
- [ ] Complete the induction through j=ℓ.
- [ ] Convert the final bijection back to a valid ordering and complete Theorem 1.2 once Lemmas 5.1–5.3 are proved.

### Proof of Lemma 5.1

- [ ] Prove for every b∈{|S|-30D,...,|S|} that P[b∈B(σ)]≤3/|S|^α.
- [ ] Union-bound over possible left endpoints a.
- [ ] Prove {σ(a),...,σ(b)} is a uniform subset of S of size b-a+1.
- [ ] Apply Corollary 4.2 with k=1 and write both complementary-gap terms.
- [ ] Reindex the two reciprocal-square-root sums exactly.
- [ ] Use Σ_{i≤|S|}1/√i≤2√|S|.
- [ ] Use the Section 5 C_1 and |S|/p bounds to get 3|S|^{-α}.
- [ ] Union-bound over at most 30D+1 choices of b.
- [ ] Use the chosen C_α to get P[B₁]≤1/100.

### Lemma 5.4 and equation (5.1)

- [ ] Define B₀ exactly.
- [ ] State Lemma 5.4 exactly: P[B₀]≤1/100.
- [ ] For fixed b,J,J', prove equation (5.1): joint probability ≤8/|S|^{1+α}.
- [ ] Choose i∈J△J'.
- [ ] Conditional on the other exposed values in the 20D window, prove at most one σ(i) realizes equal subset sums.
- [ ] Derive probability ≤1/(|S|-20D)≤2/|S|.
- [ ] Conditional on the full window σ(b),...,σ(b+20D), union-bound b∈B(σ) over a.
- [ ] Identify the conditional random interval {σ(a),...,σ(b-1)} as a uniform subset of the remaining ground set.
- [ ] Apply Corollary 4.2 with k=1 to ground-set size |S|-20D-1.
- [ ] Reproduce the bound ≤4|S|^{-α}.
- [ ] Multiply with 2/|S| to obtain equation (5.1).
- [ ] Count at most |S|·2^{40D+2} triples (b,J,J').
- [ ] Use the first lower bound on C_α to conclude P[B₀]≤1/100.

### Proof of Lemma 5.2

- [ ] Reduce to P[B₂\(B₀∪B₁)]≤1/100.
- [ ] From B₂, choose z and let b₀ be the minimal bad endpoint in the 20D window.
- [ ] Choose distinct b₀,b₁,...,b_D with b_i∈{b₀+1,...,b₀+20D}.
- [ ] Choose a_i with Σ(σ,[a_i,b_i])=0.
- [ ] From ¬B₁, prove b₀≤|S|-30D.
- [ ] From ¬B₀, prove the a_i are distinct.
- [ ] Reorder so a₁<...<a_D.
- [ ] From ¬B₀, prove a_D<b₀.
- [ ] Condition on σ(b₀),...,σ(b₀+20D).
- [ ] Rewrite the D zero-sum constraints as nested prefix-set sum constraints ending at b₀-1.
- [ ] Prove the resulting nested sets form a uniformly random chain in the remaining ground set.
- [ ] Apply Corollary 4.2 with k=D.
- [ ] Sum over all a₁<...<a_D using Lemma 4.3.
- [ ] Reproduce the bound (D+1)2^D/|S|^3 using αD≥3.
- [ ] Union-bound over b₀ and (20D)^D choices of b₁,...,b_D.
- [ ] Reproduce (D+1)(40D)^D/|S|²≤1/100.
- [ ] Add B₀ and B₁ probabilities and conclude P[B₂]≤3/100.

### Lemma 5.5

- [ ] State Lemma 5.5 exactly with b'-b=5D, u_i∈{b,...,b'}, and π_i fixed outside [b,b'].
- [ ] Define “interesting for (x₁,...,x_D)” exactly.
- [ ] Given a witness admissible π, form P' by deleting transpositions irrelevant to all π_i([u_i,x_i]).
- [ ] Prove π' preserves every relevant image set and hence all D zero-sum conditions.
- [ ] Characterize possible starting points q of pairs in an interesting P.
- [ ] Prove q lies in {b-5D,...,b+5D} or one of {x_i-5D+1,...,x_i}.
- [ ] Bound the number of candidate q by 7D².
- [ ] Bound choices per q by 5D+1.
- [ ] Reproduce the number of interesting permutations ≤D^{14D²}.
- [ ] For fixed x₁<...<x_D and fixed interesting π, prove σ∘π is still a uniform random bijection.
- [ ] Condition on (σ∘π)(b),...,(σ∘π)(b').
- [ ] Define s=|S|-5D-1 and m_i=x_i-b'.
- [ ] Prove the right-tail image sets form a uniform nested chain in the remaining ground set.
- [ ] Apply Corollary 4.2 with k=D to the D required sums.
- [ ] Union-bound over the ≤D^{14D²} interesting permutations.
- [ ] Sum over x₁<...<x_D and change variables to m_i.
- [ ] Apply Lemma 4.3.
- [ ] Reproduce every comparison from s to |S|.
- [ ] Use αD≥3 and the C_α bound to derive probability ≤1/|S|².

### Lemma 5.6

- [ ] State Lemma 5.6 exactly.
- [ ] Formalize the order-reversal involution on {1,...,|S|}.
- [ ] Prove admissibility and fixed-outside-window hypotheses are preserved under reversal.
- [ ] Translate left-tail intervals to the right-tail situation of Lemma 5.5.
- [ ] Deduce Lemma 5.6 from Lemma 5.5 without changing the probability bound.

### Proof of Lemma 5.3

- [ ] Reduce to P[B₃\(B₀∪B₁)]≤2/100.
- [ ] Under ¬B₀, prove distinct local subsets in {b,...,b+5D} remain sum-distinct after an admissible π fixing the prefix.
- [ ] Deduce that any zero interval witnessing blockedness must extend left of b or right of b+5D.
- [ ] Split 2D blocked y into at least D right-extending or at least D left-extending witnesses.
- [ ] Define E₁ exactly as in the paper.
- [ ] Define E₂ exactly as in the paper.
- [ ] Prove B₃\(B₀∪B₁)⊆E₁∪E₂.
- [ ] For E₁, prove t₁,...,t_D are distinct using local subset-sum injectivity.
- [ ] Reorder t₁<...<t_D.
- [ ] Apply Lemma 5.5 with b'=b+5D, u_i=s_i, π_i=π_{b,y_i}.
- [ ] Count parameter choices and obtain P[E₁]≤(5D)^{2D}/|S|≤1/100.
- [ ] For E₂, prove s₁,...,s_D are distinct using local subset-sum injectivity.
- [ ] Reorder s₁<...<s_D.
- [ ] Apply Lemma 5.6 with b'=b+5D, u_i=t_i, π_i=π_{b,y_i}.
- [ ] Count parameter choices and obtain P[E₂]≤(5D)^{2D}/|S|≤1/100.
- [ ] Combine E₁,E₂,B₀,B₁ to conclude P[B₃]≤1/25.

## 6. End-to-end fidelity checks

- [ ] Theorem 1.3 is proved from Facts 2.1–2.5 and Lemmas 3.1–3.7, not assumed.
- [ ] Corollary 1.4 is proved from Theorem 1.3 and Lemma 4.1, not assumed.
- [ ] Corollary 4.2 is proved from Corollary 1.4, not assumed.
- [ ] Lemma 4.3 is proved and used in exactly the two Section 5 summations where the paper uses it.
- [ ] Lemmas 5.1, 5.2, and 5.3 are individually proved with the paper's constants 1/100, 3/100, and 1/25.
- [ ] Lemmas 5.4, 5.5, and 5.6 are individually represented and proved.
- [ ] Theorem 1.2 is proved by the same bad-event/greedy-repair architecture as the paper.
- [ ] Every displayed numbered equation used later ((3.1)–(3.4), (4.1), (5.1)) has a named Lean lemma or an explicitly traceable local result.
- [ ] Every “uniformly random” and “conditional on” sentence used as a proof step has a corresponding finite-probability lemma.
- [ ] All constants appearing in the paper's inequalities are preserved or any replacement is accompanied by a proved implication back to the exact stated bound.
- [ ] The final source contains no placeholder result named as if proved when its body is `sorry`.
- [ ] The PR description lists any deliberate representation differences and the equivalence lemmas justifying them.
- [ ] No CI workflow is added and no compilation is performed unless explicitly requested later.
