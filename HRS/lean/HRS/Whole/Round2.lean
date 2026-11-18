import HRS.Whole.Moving

/-!
# Whole-space supplement, Section 9 (`W:sec:round2-moment-transfer`, `W:sec:round2-weighted-moments`,
`W:sec:r2-interacting-static`): singular moment transfer, integrated quadratic limits, weighted field moments,
the interacting static field correction -- statements S9.1-S9.10

Source: HRS whole-space supplement (S), lines 6772-7693.

| row | Lean declaration | TeX lines |
|---|---|---|
| S9.1 `W:lem:round2-approximation` | `round2_approximation` | 6797-6810 |
| S9.2 `W:prop:round2-moment-transfer` | `round2_moment_transfer` | 6862-6885 |
| S9.3 `W:cor:round2-quench-transfer` | `round2_quench_transfer` | 6954-6960 |
| S9.4 `W:prop:round2-integrated-chaos` | `round2_integrated_chaos` | 6991-7026 |
| S9.5 `W:prop:round2-polynomial-moments` | `round2_polynomial_moments` | 7137-7163 |
| S9.6 `W:cor:round2-polynomial-integrated` | `round2_polynomial_integrated` | 7231-7238 |
| S9.7 `W:cor:round2-weighted-field-moments` | `round2_weighted_field_moments` | 7256-7282 |
| S9.8 `W:lem:r2-screened` | `r2_screened` | 7391-7402 |
| S9.9 `W:thm:r2-static-edgeworth` | `r2_static_edgeworth` (`R2StaticEdgeworth`) | 7452-7470 |
| S9.10 `W:cor:r2-static-observation-family` | `r2_static_observation_family`, `r2_static_observation_path` | 7637-7664 |

Standing assumptions of S9.1-S9.7 (S L6786-6794): `d ≥ 2`, `0 ≤ σ < d/2` (the source writes `σ`, here `s`),
`μ = ρ dx` a probability measure with bounded density (and, for `σ = 0`, a finite logarithmic moment);
`g(x) = |x|^{-σ}` (`σ > 0`), `-log|x|` (`σ = 0`) with the deleted-diagonal normalisation
`W:eq:euclidean-F`; `W_σ(z) = 1 + |z|^{-σ}` (`σ > 0`), `W_0(z) = 1 + (-log|z|)_+`; `Q_{N,b} = Q^g_{N,b}(μ)`.
Standing assumptions of S9.8-S9.10 (S L7355-7389): `d ≥ 2`, `a, β > 0`, `0 ≤ σ < d/2`, `V = a|x|²/2`, `μ = ρ dx` the thermal
equilibrium (`IsThermalEquilibrium`), preparation `Q_{N,γ}(μ)` with `γ > 0`, `R_γ = (I+γK)^{-1}` on `L²_0(μ)`.

## Representation decisions

* `W_σ` is `1 + rieszWeight s z` (`Static.lean`), and "a real measurable symmetric kernel `h` with
  `|h(x,y)| ≤ B W_σ(x-y)` off the diagonal" is `IsBoundedPairKernel s B h` (the diagonal is excluded:
  Lean's junk `‖0‖^(-s) = 0`).
* `F_N^h(X_N, μ)` is `pairEnergy h X μ` (`W:eq:euclidean-F`), `Q_{N,b}` is `modulatedGibbs (rieszKernel d s) N b μ`.
* `L^r(P)` norms are `eLpNorm` (values in `ℝ≥0∞`, `⊤` if not in `L^r`), so "bounded", "tends to zero" and
  "`L^r` convergence" never use a junk value.  `‖dP/dQ‖_{L^p(Q)}` is `eLpNorm` of `(rnDeriv P Q).toReal`, and
  `P ≪ Q` is part of the hypothesis.
* The finite-rank kernels of S9.1 are `r2FiniteRankKernel c u = ∑_{a,b} c_{ab} u_a ⊗ u_b` with `c` symmetric and `u_a ∈ C_c^∞`;
  the conclusion of S9.1 is the structure `IsRound2Approx` (it is also the hypothesis "for `h`, `h_j` as in S9.1" of S9.2).
* A family of particle laws `P_N` (`N ≥ 2`) is `P : ∀ N, Measure (EucConfig d N)`; the hypotheses/conclusions of S9.2, S9.3
  are written for a family indexed by an auxiliary type `ι` (`ι = Unit` for S9.2, times `ℝ≥0` for S9.3) so that
  "uniformly in the time `t`" is expressed by common constants and by suprema over `ι`.
* `N ≥ 2` is imposed everywhere (technical: the pressure estimate and the rates are stated for `N ≥ 2`).
* S9.4/S9.6: convergence in law is Mathlib's `TendstoInDistribution` (sequence of probability spaces `Ω : ℕ → Type`), Wasserstein
  distances are `HRS.wassersteinE` on normed product spaces; `L²([0,T])` is the type synonym `R2L2 T` with its Borel `σ`-algebra.  The
  Gaussian chaos `I_2^{Cov(ξ^t)}(k)` is the `L²`-limit of Wick sections in an orthonormal basis `(P_μ a_i)` of `L²_0(μ)` (`IsR2WickChaos`; it is
  basis independent, so the statement quantifies over all bases) and `B(t) = ½ I_2(h_c)`.  The leading limit `ξ` is a family `ξ a : Ω' → C([0,T])`
  indexed by test functions; the covariance hypothesis is `E ξ^t(a)² ≤ Λ‖P_μ a‖²` (boundedness of the covariance extended to `L²_0(μ)`).
* S9.7: `‖T‖_{-m,P}` is the dual norm of the weighted `H^m` (computed on Schwartz tests), `ℝ≥0∞`-valued.
* S9.9/S9.10: the Gaussian `G ∈ B_m` is a probability measure with `IsCenteredGaussianOsc` (covariance on the Hermite basis, which determines the
  law); the pairing `⟨D³Φ(G),𝒦_{γ,μ}⟩` with the Bochner projective tensor `𝒦 = ∫ℓ_x^{⊗3}dμ` is `∫D³Φ(G)[ℓ_x,ℓ_x,ℓ_x]dμ(x)` and the tensor
  itself is asserted to exist in `projTensor` (exactly the representation of the torus Proposition 7.7); `ℓ_x(φ) = (R_γP_μφ)(x)` uses the continuous
  representative `responseRepW` (a.e.-defined `responseInverse` would make point values meaningless).  The supremum over the unit ball of `C_b^5` tending to `0`
  is `∀ ε, ∃ N₀, ∀ N ≥ N₀, ∀ Φ, |…| ≤ ε`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole

variable {d : ℕ}

/-! ### The setting of S9 -/

/-- The standing assumption of S9 on the reference measure (S L6786-6788): `μ = ρ dx` a probability measure with
density bounded by `M` and, for `σ = 0`, logarithmic moment `∫ log(2+|x|) dμ ≤ L` (`HasLogMoment`). -/
structure IsRound2Density (d : ℕ) (s M L : ℝ) (ρ : Euc d → ℝ) : Prop where
  prob : IsProbDensity ρ
  bdd : ∀ x, ρ x ≤ M
  logMoment : s = 0 → HasLogMoment (withDensityReal ρ) L

/-- The finite-rank kernel `h(x,y) = ∑_{a,b=1}^m c_{ab} u_a(x) u_b(y)` of S L6803. -/
def r2FiniteRankKernel {m : ℕ} (c : Fin m → Fin m → ℝ) (u : Fin m → Euc d → ℝ) (x y : Euc d) : ℝ :=
  ∑ a, ∑ b, c a b * u a x * u b y

/-- The finite-rank data of S9.1: `c_{ab} = c_{ba}` and `u_a ∈ C_c^∞(ℝ^d)` (S L6804-6805). -/
structure IsR2FiniteRankData {m : ℕ} (c : Fin m → Fin m → ℝ) (u : Fin m → Euc d → ℝ) : Prop where
  symm : ∀ a b, c a b = c b a
  smooth : ∀ a, ContDiff ℝ ∞ (u a)
  compactSupport : ∀ a, HasCompactSupport (u a)

/-- The conclusion of Lemma S9.1 (S L6802-6809), also the hypothesis "`h_j` as in Lemma S9.1" of S9.2: `h_j` is a finite-rank
kernel of the above form, `|h_j(x,y)| ≤ C B W_σ(x-y)` (`x ≠ y`) uniformly in `j`, and `h_j → h` in `L^r(μ^{⊗2})`
for every finite `r ≥ 1` with `rσ < d` (for `σ = 0`, every finite `r`). -/
structure IsRound2Approx (s C B : ℝ) (μ : Measure (Euc d)) (h : Euc d → Euc d → ℝ)
    (hj : ℕ → Euc d → Euc d → ℝ) : Prop where
  finiteRank : ∀ j, ∃ (m : ℕ) (c : Fin m → Fin m → ℝ) (u : Fin m → Euc d → ℝ),
    IsR2FiniteRankData c u ∧ hj j = r2FiniteRankKernel c u
  envelope : ∀ j x y, x ≠ y → |hj j x y| ≤ C * B * (1 + rieszWeight s (x - y))
  converges : ∀ r : ℝ, 1 ≤ r → r * s < d →
    Tendsto (fun j => eLpNorm (fun p : Euc d × Euc d => hj j p.1 p.2 - h p.1 p.2)
      (ENNReal.ofReal r) (μ.prod μ)) atTop (𝓝 0)

/-- Lemma 9.1 (S:W:lem:round2-approximation, TeX S L6797-6810): finite-rank approximation without a lower density bound.
`d ≥ 2`, `0 ≤ σ < d/2`, `μ = ρ dx` a probability measure with bounded density (log moment for `σ = 0`).  For every real
measurable symmetric kernel `h` with `|h(x,y)| ≤ B W_σ(x-y)` off the diagonal there are finite-rank symmetric kernels `h_j`
with `|h_j| ≤ C B W_σ` uniformly in `j` and `h_j → h` in `L^r(μ^{⊗2})` for every finite `r` with `rσ < d`.
The envelope constant `C` depends only on `d, σ` (proof, S L6826-6834: the mollification averages of `W_σ`), hence is
quantified before `μ` and `h`.  Technical: `r ≥ 1` (so that `L^r` is a norm, as in S9.2). -/
theorem round2_approximation (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) :
    ∃ C : ℝ, ∀ (M L : ℝ) (ρ : Euc d → ℝ), IsRound2Density d s M L ρ → ∀ (B : ℝ) (h : Euc d → Euc d → ℝ),
      IsBoundedPairKernel s B h → ∃ hj : ℕ → Euc d → Euc d → ℝ,
        IsRound2Approx s C B (withDensityReal ρ) h hj := by
  sorry

/-! ### Actual-law moment bounds (S9.2, S9.3) -/

/-- The hypothesis `W:eq:round2-actual-density` (S L6866-6867) for one law: `P` is a probability measure,
`P ≪ Q_{N,b}(μ)` and `‖dP/dQ_{N,b}‖_{L^p(Q_{N,b})} ≤ K`. -/
def HasR2ActualDensity (s b p K : ℝ) (μ : Measure (Euc d)) {N : ℕ} (P : Measure (EucConfig d N)) : Prop :=
  IsProbabilityMeasure P ∧ P ≪ modulatedGibbs (rieszKernel d s) N b μ ∧
    eLpNorm (fun X => ((P.rnDeriv (modulatedGibbs (rieszKernel d s) N b μ)) X).toReal) (ENNReal.ofReal p)
      (modulatedGibbs (rieszKernel d s) N b μ) ≤ ENNReal.ofReal K

/-- The second bound of `W:eq:round2-actual-tail` (S L6875) and its centered version ("subtract the actual `P_N`
expectations", S L6877): `‖N F_N^h(·,μ)‖_{L^r(P_N)} ≤ C` and `‖N{F_N^h - E_{P_N}F_N^h}‖_{L^r(P_N)} ≤ C`, for all
`N ≥ 2` and all members `i` of the family. -/
def R2ActualFBound {ι : Type*} (μ : ι → Measure (Euc d)) (r C : ℝ) (h : Euc d → Euc d → ℝ)
    (P : ι → ∀ N, Measure (EucConfig d N)) : Prop :=
  ∀ i : ι, ∀ N : ℕ, 2 ≤ N →
    eLpNorm (fun X => (N : ℝ) * pairEnergy h X (μ i)) (ENNReal.ofReal r) (P i N) ≤ ENNReal.ofReal C ∧
    eLpNorm (fun X => (N : ℝ) * (pairEnergy h X (μ i) - ∫ Y, pairEnergy h Y (μ i) ∂(P i N)))
      (ENNReal.ofReal r) (P i N) ≤ ENNReal.ofReal C

/-- The first bound of `W:eq:round2-actual-tail` (S L6873) and its centered version:
`lim_{j→∞} sup_{N≥2} ‖N F_N^{h_j - h}(·,μ)‖_{L^r(P_N)} = 0` (supremum also over the members `i` of the family). -/
def R2ActualFTail {ι : Type*} (μ : ι → Measure (Euc d)) (r : ℝ) (h : Euc d → Euc d → ℝ)
    (hj : ℕ → Euc d → Euc d → ℝ) (P : ι → ∀ N, Measure (EucConfig d N)) : Prop :=
  Tendsto (fun j => ⨆ (i : ι) (N : {N : ℕ // 2 ≤ N}),
    eLpNorm (fun X => ((N : ℕ) : ℝ) * pairEnergy (fun x y => hj j x y - h x y) X (μ i))
      (ENNReal.ofReal r) (P i N)) atTop (𝓝 0) ∧
  Tendsto (fun j => ⨆ (i : ι) (N : {N : ℕ // 2 ≤ N}),
    eLpNorm (fun X => ((N : ℕ) : ℝ) * (pairEnergy (fun x y => hj j x y - h x y) X (μ i) -
        ∫ Y, pairEnergy (fun x y => hj j x y - h x y) Y (μ i) ∂(P i N)))
      (ENNReal.ofReal r) (P i N)) atTop (𝓝 0)

/-- `W:eq:round2-actual-linear` (S L6880-6881): for every bounded real (measurable) test `a`,
`‖√N(μ_N(a) - μ(a))‖_{L^r(P_N)} ≤ C ‖a‖_∞` (`‖a‖_∞ ≤ A` is written pointwise). -/
def R2ActualLinearBound {ι : Type*} (μ : ι → Measure (Euc d)) (r C : ℝ)
    (P : ι → ∀ N, Measure (EucConfig d N)) : Prop :=
  ∀ i : ι, ∀ N : ℕ, 2 ≤ N → ∀ (a : Euc d → ℝ) (A : ℝ), Measurable a → (∀ x, |a x| ≤ A) →
    eLpNorm (fun X => Real.sqrt N * (pair (empirical X) a - pair (μ i) a)) (ENNReal.ofReal r) (P i N) ≤
      ENNReal.ofReal (C * A)

/-- Proposition 9.2 (S:W:prop:round2-moment-transfer, TeX S L6862-6885): actual-law singular moment transfer.
Fix `b > 0`; `P_N` probability laws with `sup_N ‖dP_N/dQ_{N,b}‖_{L^p(Q_{N,b})} ≤ K` for some fixed `p > 1`.
For `h`, `h_j` as in S9.1 (`IsRound2Approx`) and every finite `r ≥ 1`: `lim_j sup_N ‖N F_N^{h_j-h}‖_{L^r(P_N)} = 0`,
`sup_N ‖N F_N^h‖_{L^r(P_N)} < ∞`, both also after subtracting the actual `P_N`-expectations; and for every bounded real test
`a`, `sup_N ‖√N(μ_N(a)-μ(a))‖_{L^r(P_N)} ≤ C_{p,r,b}‖a‖_∞`.  "All constants are uniform over a family of laws satisfying the
same bound": `C` is quantified after `(d,σ,M,L,b,p,K,B,r)` and before `ρ` and `P`; the finiteness of `sup_N ‖N F_N^h‖`
is the explicit bound `≤ C` (for the class `IsBoundedPairKernel s B`, `B` fixed).  The limit assertion has no constant.
Technical hypotheses: `N ≥ 2`; `r ≥ 1`. -/
theorem round2_moment_transfer (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (M L b p K B : ℝ) (hb : 0 < b) (hp : 1 < p) (r : ℝ) (hr : 1 ≤ r) :
    ∃ C : ℝ, ∀ ρ : Euc d → ℝ, IsRound2Density d s M L ρ → ∀ P : ∀ N, Measure (EucConfig d N),
      (∀ N, 2 ≤ N → HasR2ActualDensity s b p K (withDensityReal ρ) (P N)) →
      (∀ h : Euc d → Euc d → ℝ, IsBoundedPairKernel s B h →
        R2ActualFBound (ι := Unit) (fun _ => withDensityReal ρ) r C h (fun _ => P)) ∧
      R2ActualLinearBound (ι := Unit) (fun _ => withDensityReal ρ) r C (fun _ => P) ∧
      ∀ (C₁ : ℝ) (h : Euc d → Euc d → ℝ) (hj : ℕ → Euc d → Euc d → ℝ), IsBoundedPairKernel s B h →
        IsRound2Approx s C₁ B (withDensityReal ρ) h hj →
        R2ActualFTail (ι := Unit) (fun _ => withDensityReal ρ) r h hj (fun _ => P) := by
  sorry

/-- A Markov particle semigroup on `(ℝ^d)^N`: Markov kernels `K_t`, `K_0 = id`, `K_{s+t} = K_t ∘ K_s`. -/
structure IsR2ParticleSemigroup {α : Type*} [MeasurableSpace α] (K : ℝ≥0 → Kernel α α) : Prop where
  markov : ∀ t, IsMarkovKernel (K t)
  zero : K 0 = Kernel.id
  add : ∀ s t, K (s + t) = K t ∘ₖ K s

/-- Corollary 9.3 (S:W:cor:round2-quench-transfer, TeX S L6954-6960): every fixed positive preparation temperature.
A Markov particle semigroup `(K_t^N)` preserving `Q_{N,b}` and started from `Q_{N,b₀}`, `b, b₀ > 0` fixed; then all the
conclusions of Proposition 9.2 hold for the actual time marginals `P_N^t = Q_{N,b₀} K_t^N`, uniformly over all `t ≥ 0`
(common constant `C`, suprema over `t ≥ 0` in the tail).  Under the standing assumptions of S9 (`IsRound2Density`).  The
exponent `p` and the bound `K` of `W:eq:round2-actual-density` are produced by the proof (`p` close to one with
`b' = p b₀ - (p-1) b > 0`), so `C` depends on `(d,σ,M,L,b,b₀,B,r)`. -/
theorem round2_quench_transfer (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (M L b b₀ B : ℝ) (hb : 0 < b) (hb₀ : 0 < b₀) (r : ℝ) (hr : 1 ≤ r) :
    ∃ C : ℝ, ∀ ρ : Euc d → ℝ, IsRound2Density d s M L ρ →
      ∀ K : ∀ N, ℝ≥0 → Kernel (EucConfig d N) (EucConfig d N), (∀ N, IsR2ParticleSemigroup (K N)) →
      (∀ N, 2 ≤ N → ∀ t, (modulatedGibbs (rieszKernel d s) N b (withDensityReal ρ)).bind (K N t) =
        modulatedGibbs (rieszKernel d s) N b (withDensityReal ρ)) →
      let P : ℝ≥0 → ∀ N, Measure (EucConfig d N) := fun t N =>
        (modulatedGibbs (rieszKernel d s) N b₀ (withDensityReal ρ)).bind (K N t)
      (∀ h : Euc d → Euc d → ℝ, IsBoundedPairKernel s B h → R2ActualFBound (fun _ => withDensityReal ρ) r C h P) ∧
      R2ActualLinearBound (fun _ => withDensityReal ρ) r C P ∧
      ∀ (C₁ : ℝ) (h : Euc d → Euc d → ℝ) (hj : ℕ → Euc d → Euc d → ℝ), IsBoundedPairKernel s B h →
        IsRound2Approx s C₁ B (withDensityReal ρ) h hj → R2ActualFTail (fun _ => withDensityReal ρ) r h hj P := by
  sorry


/-! ### S9.4: integrated quadratic limits -/

section IntegratedChaos

/-- A test function: `a ∈ C_c^∞(ℝ^d)`. -/
def IsR2Test (a : Euc d → ℝ) : Prop := ContDiff ℝ ∞ a ∧ HasCompactSupport a

/-- `L²([0,T])` (real valued), a type synonym of `Lp ℝ 2 (volume|_{[0,T]})` carrying its Borel `σ`-algebra
(not provided by Mathlib; needed for convergence in law and Wasserstein distances). -/
def R2L2 (T : ℝ) : Type := Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) T))

namespace R2L2

variable {T : ℝ}

instance : NormedAddCommGroup (R2L2 T) :=
  inferInstanceAs (NormedAddCommGroup (Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) T))))

instance : NormedSpace ℝ (R2L2 T) :=
  inferInstanceAs (NormedSpace ℝ (Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) T))))

instance : SecondCountableTopology (R2L2 T) :=
  inferInstanceAs (SecondCountableTopology (Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) T))))

instance : MeasurableSpace (R2L2 T) := borel _

instance : BorelSpace (R2L2 T) := ⟨rfl⟩

end R2L2

open Classical in
/-- The element of `L²([0,T])` given by a function of time (`0` if it is not in `L²`; used only for
realisations, where the conclusions assert membership). -/
def r2L2Path (T : ℝ) (f : ℝ → ℝ) : R2L2 T :=
  if h : MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) T)) then
    (show Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) T)) from h.toLp f) else 0

open Classical in
/-- The element of `C([0,T])` given by a function of time (`0` if it is not continuous on `[0,T]`). -/
def r2ContPath (T : ℝ) (f : ℝ → ℝ) : C(Set.Icc (0 : ℝ) T, ℝ) :=
  if h : Continuous fun t : Set.Icc (0 : ℝ) T => f t then ⟨fun t => f t, h⟩ else 0

/-- The value `w(t)` of `w ∈ C([0,T])` at a real time (`0` outside `[0,T]`). -/
def r2PathEval (T : ℝ) (w : C(Set.Icc (0 : ℝ) T, ℝ)) (t : ℝ) : ℝ :=
  open Classical in if h : t ∈ Set.Icc (0 : ℝ) T then w ⟨t, h⟩ else 0

/-- The integrated process `u ↦ ∫_0^u f(t) dt` as an element of `C([0,T])`. -/
def r2IntPath (T : ℝ) (f : ℝ → ℝ) : C(Set.Icc (0 : ℝ) T, ℝ) :=
  r2ContPath T fun u => ∫ t in (0 : ℝ)..u, f t

/-- The empirical fluctuation `ξ_N^t(a) = √N(μ_N^t(a) - μ(a))` of the particle path `X`. -/
def r2EmpFluct {Ω : Type*} {N : ℕ} (μ : Measure (Euc d)) (a : Euc d → ℝ) (X : ℝ≥0 → Ω → EucConfig d N)
    (ζ : Ω) (t : ℝ) : ℝ :=
  Real.sqrt N * (pair (empirical (X t.toNNReal ζ)) a - pair μ a)

/-- The centered quadratic process `B_N(t) = N{F_N^{h_t}(X_N^t,μ) - E F_N^{h_t}(X_N^t,μ)}`
(`W:eq:round2-time-quadratic`, S L7006-7007). -/
def r2QuadFluct {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (μ : Measure (Euc d)) (h : ℝ → Euc d → Euc d → ℝ)
    (P : Measure Ω) (X : ℝ≥0 → Ω → EucConfig d N) (t : ℝ) (ζ : Ω) : ℝ :=
  N * (pairEnergy (h t) (X t.toNNReal ζ) μ - ∫ ζ', pairEnergy (h t) (X t.toNNReal ζ') μ ∂P)

/-- Centering of a pair kernel in both variables under `μ`: `k_c(x,y) = k(x,y) - ∫k(x,·)dμ - ∫k(·,y)dμ + ∬k dμ dμ`. -/
def r2CenterKernel (μ : Measure (Euc d)) (k : Euc d → Euc d → ℝ) (x y : Euc d) : ℝ :=
  k x y - ∫ y', k x y' ∂μ - ∫ x', k x' y ∂μ + ∫ x', ∫ y', k x' y' ∂μ ∂μ

/-- `(P_μ a_i)_i` is an orthonormal basis of `L²_0(μ)` consisting of projections of test functions:
`a_i ∈ C_c^∞`, `⟨P_μ a_i, P_μ a_j⟩_{L²(μ)} = δ_{ij}`, and every `f ∈ L²_0(μ)` orthogonal to all `a_i` vanishes. -/
def IsR2ZeroMeanONB (μ : Measure (Euc d)) (a : ℕ → Euc d → ℝ) : Prop :=
  (∀ i, IsR2Test (a i)) ∧
    (∀ i j, ∫ x, projMean μ (a i) x * projMean μ (a j) x ∂μ = if i = j then 1 else 0) ∧
    ∀ f : Euc d → ℝ, MemLp f 2 μ → ∫ x, f x ∂μ = 0 → (∀ i, ∫ x, f x * a i x ∂μ = 0) → f =ᵐ[μ] 0

/-- The coefficients `A_{ij} = ∬ k(x,y) (P_μ a_i)(x) (P_μ a_j)(y) dμ dμ` of a pair kernel in the basis `(P_μ a_i)`. -/
def r2WickCoeff (μ : Measure (Euc d)) (a : ℕ → Euc d → ℝ) (k : Euc d → Euc d → ℝ) (i j : ℕ) : ℝ :=
  ∫ x, ∫ y, k x y * projMean μ (a i) x * projMean μ (a j) y ∂μ ∂μ

/-- `Q = I_2^{Cov(z)}(k)`: the centered quadratic Gaussian chaos (Wick quadratic form) of the kernel `k` on the
Gaussian space of the field `ξ` with coordinates `z_i = ξ(a_i)` (`E z_i z_j = Cov(ξ(a_i),ξ(a_j))`): the `L²(P')`-limit
of `∑_{i,j<n} A_{ij}(z_i z_j - E z_i z_j)` (the second chaos is `I_2(k) = (ξ⊗ξ)(k) - E`; so `N F_N^h ≈ ½ I_2(h)`). -/
def IsR2WickChaos {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (μ : Measure (Euc d)) (a : ℕ → Euc d → ℝ) (z : ℕ → Ω' → ℝ) (k : Euc d → Euc d → ℝ) (Q : Ω' → ℝ) : Prop :=
  HRS.TendstoL2 P' (fun n ζ => ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
    r2WickCoeff μ a k i j * (z i ζ * z j ζ - ∫ ζ', z i ζ' * z j ζ' ∂P')) Q

/-- The hypotheses of S9.4 (S L6993-7001) on the particle paths and their leading limit, for a fixed reference
`μ`, horizon `T`, and actual-density data `(b,p,K)`: `P_N^t = Law(X_N^t)` satisfy `W:eq:round2-actual-density` uniformly in
`N ≥ 2`, `t ∈ [0,T]`; for every finite family of tests in `C_c^∞` the empirical fluctuation paths
`ξ_N^t(a)` converge jointly in `C([0,T])` to a centered Gaussian process `ξ^t(a)` (`ξ a ζ : C([0,T])`); and the fixed-time
covariance of `ξ^t` extends to `L²_0(μ)` with operator norm at most `Λ`, uniformly in `t ∈ [0,T]`
(`E ξ^t(a)² ≤ Λ ‖P_μ a‖²_{L²(μ)}`).  Technical: the particle process is jointly measurable with a.s. continuous paths
(particle paths) and each `P N` is a probability measure; `ξ a` is measurable. -/
structure IsRound2PathSetting (d : ℕ) (s T b p K : ℝ) (μ : Measure (Euc d))
    {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (X : ∀ N, ℝ≥0 → Ω N → EucConfig d N)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (ξ : (Euc d → ℝ) → Ω' → C(Set.Icc (0 : ℝ) T, ℝ)) : Prop where
  measX : ∀ N, Measurable fun q : ℝ≥0 × Ω N => X N q.1 q.2
  contX : ∀ N, ∀ᵐ ζ ∂(P N), ∀ i, Continuous fun t : ℝ≥0 => X N t ζ i
  density : ∀ N, 2 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) T,
    HasR2ActualDensity s b p K μ ((P N).map (X N t.toNNReal))
  measξ : ∀ a, Measurable (ξ a)
  gaussian : ∀ (k : ℕ) (a : Fin k → Euc d → ℝ), (∀ i, IsR2Test (a i)) →
    IsCenteredGaussian (P'.map fun ζ i => ξ (a i) ζ)
  conv : ∀ (k : ℕ) (a : Fin k → Euc d → ℝ), (∀ i, IsR2Test (a i)) →
    TendstoInDistribution (fun N ζ => fun i => r2ContPath T (r2EmpFluct μ (a i) (X N) ζ)) atTop
      (fun ζ i => ξ (a i) ζ) P P'
  cov : ∃ Λ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ a, IsR2Test a →
    ∫ ζ, (r2PathEval T (ξ a ζ) t) ^ 2 ∂P' ≤ Λ * ∫ x, (projMean μ a x) ^ 2 ∂μ

/-- The conclusions of S9.4 (S L7005-7025) for a time-dependent kernel family `h_t` in the setting
`IsRound2PathSetting`: there is a jointly measurable version `F` of `B(t) = ½ I_2^{Cov(ξ^t)}((h_t)_c)` (for every orthonormal
basis `(P_μ a_i)` of `L²_0(μ)`, `2F(t,·)` is the Wick chaos of `(h_t)_c` on the Gaussian space of `ξ^t`), with `B ∈ L²([0,T])`
a.s., such that for every finite family `aa` of tests: (i) `(B_N, ξ_N(aa))` converges in law in `L²([0,T]) × C([0,T])^k` to
`(B, ξ(aa))` (joint with the leading observation paths); (ii) `(B_N, ∫_0^· B_N, ξ_N(aa))` converges in law in
`L²([0,T]) × C([0,T]) × C([0,T])^k` to `(B, ∫_0^· B, ξ(aa))` (the integrated processes converge in `C([0,T])`); (iii) for
every finite `r ≥ 1` the law of `(ξ_N(aa), B_N, ∫_0^·B_N)` converges in `r`-Wasserstein distance on
`L²([0,T])^k × L²([0,T]) × C([0,T])` (observation and quadratic coordinates in `L²` in time, integrated coordinate in
`C([0,T])`; the product norm is the max norm, equivalent to the "sum of their norm metrics" of the source).
No convergence of the unintegrated singular process in the continuous-path norm is claimed. -/
def IntegratedChaosConclusion (d : ℕ) (T : ℝ) (μ : Measure (Euc d)) (h : ℝ → Euc d → Euc d → ℝ)
    {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (X : ∀ N, ℝ≥0 → Ω N → EucConfig d N)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (ξ : (Euc d → ℝ) → Ω' → C(Set.Icc (0 : ℝ) T, ℝ)) : Prop :=
  ∃ F : ℝ → Ω' → ℝ, (Measurable fun q : ℝ × Ω' => F q.1 q.2) ∧
    (∀ ζ, MemLp (fun t => F t ζ) 2 (volume.restrict (Set.Icc (0 : ℝ) T))) ∧
    (∀ a : ℕ → Euc d → ℝ, IsR2ZeroMeanONB μ a → ∀ t ∈ Set.Icc (0 : ℝ) T,
      IsR2WickChaos P' μ a (fun i ζ => r2PathEval T (ξ (a i) ζ) t) (r2CenterKernel μ (h t))
        (fun ζ => 2 * F t ζ)) ∧
    ∀ (k : ℕ) (aa : Fin k → Euc d → ℝ), (∀ i, IsR2Test (aa i)) →
      TendstoInDistribution (fun N ζ => (r2L2Path T (fun t => r2QuadFluct μ h (P N) (X N) t ζ),
          fun i => r2ContPath T (r2EmpFluct μ (aa i) (X N) ζ))) atTop
        (fun ζ' => (r2L2Path T (fun t => F t ζ'), fun i => ξ (aa i) ζ')) P P' ∧
      TendstoInDistribution (fun N ζ => (r2L2Path T (fun t => r2QuadFluct μ h (P N) (X N) t ζ),
          r2IntPath T (fun t => r2QuadFluct μ h (P N) (X N) t ζ),
          fun i => r2ContPath T (r2EmpFluct μ (aa i) (X N) ζ))) atTop
        (fun ζ' => (r2L2Path T (fun t => F t ζ'), r2IntPath T (fun t => F t ζ'),
          fun i => ξ (aa i) ζ')) P P' ∧
      ∀ r : ℝ, 1 ≤ r →
        Tendsto (fun N => wassersteinE r
          (law (P N) fun ζ => ((fun i => r2L2Path T (r2EmpFluct μ (aa i) (X N) ζ)),
            r2L2Path T (fun t => r2QuadFluct μ h (P N) (X N) t ζ),
            r2IntPath T (fun t => r2QuadFluct μ h (P N) (X N) t ζ)))
          (law P' fun ζ' => ((fun i => r2L2Path T (fun t => r2PathEval T (ξ (aa i) ζ') t)),
            r2L2Path T (fun t => F t ζ'), r2IntPath T (fun t => F t ζ'))))
          atTop (𝓝 0)

/-- Proposition 9.4 (S:W:prop:round2-integrated-chaos, TeX S L6991-7026): joint integrated quadratic limits under the actual
law.  Setting of S9 (`IsRound2Density`, `0 ≤ σ < d/2`), `T < ∞` (`T > 0`), the particle time marginals satisfy
`W:eq:round2-actual-density` uniformly in `N, t` and their empirical fluctuation paths converge jointly to a centered
Gaussian process with uniformly bounded fixed-time covariance (`IsRound2PathSetting`).  For every jointly measurable
family `h_t` of symmetric kernels with `|h_t(x,y)| ≤ B W_σ(x-y)` (`t ∈ [0,T]`), the conclusions of `IntegratedChaosConclusion`
hold.  The family index `N` runs over all `N ∈ ℕ` (convergence is as `N → ∞`; only `N ≥ 2` enters the hypotheses). -/
theorem round2_integrated_chaos (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (M L b p K B T : ℝ) (hb : 0 < b) (hp : 1 < p) (hT : 0 < T)
    (ρ : Euc d → ℝ) (hρ : IsRound2Density d s M L ρ)
    {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (X : ∀ N, ℝ≥0 → Ω N → EucConfig d N)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (ξ : (Euc d → ℝ) → Ω' → C(Set.Icc (0 : ℝ) T, ℝ))
    (hset : IsRound2PathSetting d s T b p K (withDensityReal ρ) P X P' ξ)
    (h : ℝ → Euc d → Euc d → ℝ)
    (hmeas : Measurable fun q : ℝ × Euc d × Euc d => h q.1 q.2.1 q.2.2)
    (hker : ∀ t ∈ Set.Icc (0 : ℝ) T, IsBoundedPairKernel s B (h t)) :
    IntegratedChaosConclusion d T (withDensityReal ρ) h P X P' ξ := by
  sorry

/-! ### S9.5, S9.6: polynomially weighted moments -/

/-- The polynomial envelope `W:eq:round2-polynomial-envelope` (S L7143-7144): `h` real measurable symmetric with
`|h(x,y)| ≤ B(⟨x⟩+⟨y⟩)^P W_σ(x-y)` off the diagonal (`⟨x⟩ = (1+|x|²)^{1/2}`). -/
structure IsR2PolyPairKernel (s Pw B : ℝ) (h : Euc d → Euc d → ℝ) : Prop where
  measurable : Measurable fun p : Euc d × Euc d => h p.1 p.2
  symm : ∀ x y, h x y = h y x
  bound : ∀ x y, x ≠ y →
    |h x y| ≤ B * (jbracket x + jbracket y) ^ Pw * (1 + rieszWeight s (x - y))

/-- The Gaussian density upper bound `ρ(x) ≤ C₀ e^{-c₀|x|²}` of S9.5 (S L7140), with `c₀ > 0`.  Statement change
(2026-10-22, approved): the positivity `0 < c₀` is part of the definition (it is implicit in the source); without it
S9.5-S9.7 are false (`c₀ = 0`, `ρ` uniform on a large ball). -/
def HasR2GaussianUpper (C₀ c₀ : ℝ) (ρ : Euc d → ℝ) : Prop :=
  0 < c₀ ∧ ∀ x, ρ x ≤ C₀ * Real.exp (-c₀ * ‖x‖ ^ 2)

/-- Proposition 9.5 (S:W:prop:round2-polynomial-moments, TeX S L7137-7163): polynomially weighted actual-law moments.
In the setting of S9.2 (`IsRound2Density`, `HasR2ActualDensity` for `N ≥ 2`) with also `ρ ≤ C₀e^{-c₀|x|²}` and a fixed
`Pw ≥ 0` (the source's `P`): for every symmetric measurable kernel with the polynomial envelope and every finite `r ≥ 1`,
`sup_N ‖N F_N^h‖_{L^r(P_N)} ≤ C_{P,r} B`; if `h_j` satisfy the same bound (same `B`) and `h_j → h` in `L^{2+ε}(μ^{⊗2})`
for some `ε` with `(2+ε)σ < d`, then `lim_j sup_N ‖N F_N^{h_j-h}‖_{L^r(P_N)} = 0`; all assertions also after subtracting the
actual expectation; and for every measurable `a` with `|a(x)| ≤ B⟨x⟩^P`,
`sup_N ‖√N(μ_N(a)-μ(a))‖_{L^r(P_N)} ≤ C_{P,r} B`.  The constant `C = C_{P,r}` is uniform ("in any additional parameters
for which the hypotheses, in particular the actual density bound, are uniform"): it is quantified before `ρ`
and `P_N` and does not depend on `B ≥ 0` (the bound is linear in `B`) nor on `h`. -/
theorem round2_polynomial_moments (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (M L C₀ c₀ b p K Pw : ℝ) (hb : 0 < b) (hp : 1 < p) (hPw : 0 ≤ Pw) (r : ℝ) (hr : 1 ≤ r) :
    ∃ C : ℝ, ∀ ρ : Euc d → ℝ, IsRound2Density d s M L ρ → HasR2GaussianUpper C₀ c₀ ρ →
      ∀ P : ∀ N, Measure (EucConfig d N),
      (∀ N, 2 ≤ N → HasR2ActualDensity s b p K (withDensityReal ρ) (P N)) →
      (∀ (B : ℝ), 0 ≤ B → ∀ h : Euc d → Euc d → ℝ, IsR2PolyPairKernel s Pw B h →
        R2ActualFBound (ι := Unit) (fun _ => withDensityReal ρ) r (C * B) h (fun _ => P)) ∧
      (∀ (B : ℝ), 0 ≤ B → ∀ (h : Euc d → Euc d → ℝ) (hj : ℕ → Euc d → Euc d → ℝ),
        IsR2PolyPairKernel s Pw B h → (∀ j, IsR2PolyPairKernel s Pw B (hj j)) →
        (∃ ε : ℝ, 0 < ε ∧ (2 + ε) * s < d ∧
          Tendsto (fun j => eLpNorm (fun q : Euc d × Euc d => hj j q.1 q.2 - h q.1 q.2)
            (ENNReal.ofReal (2 + ε)) ((withDensityReal ρ).prod (withDensityReal ρ))) atTop (𝓝 0)) →
        R2ActualFTail (ι := Unit) (fun _ => withDensityReal ρ) r h hj (fun _ => P)) ∧
      (∀ (B : ℝ), 0 ≤ B → ∀ N : ℕ, 2 ≤ N → ∀ a : Euc d → ℝ, Measurable a →
        (∀ x, |a x| ≤ B * jbracket x ^ Pw) →
        eLpNorm (fun X => Real.sqrt N * (pair (empirical X) a - pair (withDensityReal ρ) a))
          (ENNReal.ofReal r) (P N) ≤ ENNReal.ofReal (C * B)) := by
  sorry

/-- Corollary 9.6 (S:W:cor:round2-polynomial-integrated, TeX S L7231-7238): under the hypotheses of Proposition 9.4 and also
the Gaussian upper bound of Proposition 9.5, the conclusions of 9.4 remain valid for jointly measurable symmetric kernels
satisfying the polynomial envelope `W:eq:round2-polynomial-envelope` uniformly in time (`t ∈ [0,T]`, fixed `Pw ≥ 0`, `B`). -/
theorem round2_polynomial_integrated (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (M L C₀ c₀ b p K B Pw T : ℝ) (hb : 0 < b) (hp : 1 < p) (hPw : 0 ≤ Pw) (hT : 0 < T)
    (ρ : Euc d → ℝ) (hρ : IsRound2Density d s M L ρ) (hG : HasR2GaussianUpper C₀ c₀ ρ)
    {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (X : ∀ N, ℝ≥0 → Ω N → EucConfig d N)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (ξ : (Euc d → ℝ) → Ω' → C(Set.Icc (0 : ℝ) T, ℝ))
    (hset : IsRound2PathSetting d s T b p K (withDensityReal ρ) P X P' ξ)
    (h : ℝ → Euc d → Euc d → ℝ)
    (hmeas : Measurable fun q : ℝ × Euc d × Euc d => h q.1 q.2.1 q.2.2)
    (hker : ∀ t ∈ Set.Icc (0 : ℝ) T, IsR2PolyPairKernel s Pw B (h t)) :
    IntegratedChaosConclusion d T (withDensityReal ρ) h P X P' ξ := by
  sorry

end IntegratedChaos


/-! ### S9.7: weighted field moments -/

section WeightedField

/-- The random distribution `φ ↦ √N(μ_N(φ) - μ(φ))` of a configuration. -/
def r2EmpDistr {N : ℕ} (μ : Measure (Euc d)) (X : EucConfig d N) (φ : Euc d → ℝ) : ℝ :=
  Real.sqrt N * (pair (empirical X) φ - pair μ φ)

/-- The random distribution `φ ↦ ⟨𝓡_N, φ⟩ = N F_N^{h_φ}(X_N,μ)`, `h_φ(x,y) = (∇φ(x)-∇φ(y))·∇g(x-y)`
(`commutatorKernel d s (∇φ)`; S L7266-7269). -/
def r2CommDistr (d : ℕ) (s : ℝ) {N : ℕ} (μ : Measure (Euc d)) (X : EucConfig d N) (φ : Euc d → ℝ) : ℝ :=
  N * pairEnergy (commutatorKernel d s (fun x => gradient φ x)) X μ

/-- `‖T‖_{-m,P} = ‖⟨x⟩^P T‖_{H^{-m}(ℝ^d)}` (S L7261) of a distribution `T` given by its values on test functions:
`sup{|T(⟨x⟩^P ψ)| : ψ Schwartz, ‖ψ‖_{H^m} ≤ 1}` (`ℝ≥0∞`-valued; equal to the dual norm since Schwartz functions are
dense in `H^m`, and `⟨T, ⟨x⟩^Pψ⟩ = ⟨⟨x⟩^PT, ψ⟩`).  The dual test space is `{φ : ⟨x⟩^{-P}φ ∈ H^m}` (`φ = ⟨x⟩^Pψ`). -/
def r2NegSobNorm (m : ℕ) (Pw : ℝ) (T : (Euc d → ℝ) → ℝ) : ℝ≥0∞ :=
  ⨆ (ψ : SchwartzMap (Euc d) ℝ) (_ : sobolevNormE (m : ℝ) (fun x => ψ x) ≤ 1),
    ENNReal.ofReal |T (fun x => jbracket x ^ Pw * ψ x)|

/-- `W:eq:round2-weighted-field-bound` (S L7273-7275) and its centered version ("the same bound holds for the exactly
centered distributions"): `E[‖√N(μ_N-μ)‖^r_{-m,P} + ‖𝓡_N‖^r_{-m,P}] ≤ C` for all `N ≥ 2` and all members `i` of the family. -/
def R2WeightedFieldBound {ι : Type*} (s : ℝ) (m : ℕ) (Pw r C : ℝ) (μ : ι → Measure (Euc d))
    (P : ι → ∀ N, Measure (EucConfig d N)) : Prop :=
  ∀ i : ι, ∀ N : ℕ, 2 ≤ N →
    ∫⁻ X, (r2NegSobNorm m Pw (r2EmpDistr (μ i) X) ^ r + r2NegSobNorm m Pw (r2CommDistr d s (μ i) X) ^ r)
        ∂(P i N) ≤ ENNReal.ofReal C ∧
    ∫⁻ X, (r2NegSobNorm m Pw (fun φ => r2EmpDistr (μ i) X φ - ∫ Y, r2EmpDistr (μ i) Y φ ∂(P i N)) ^ r +
        r2NegSobNorm m Pw (fun φ => r2CommDistr d s (μ i) X φ - ∫ Y, r2CommDistr d s (μ i) Y φ ∂(P i N)) ^ r)
        ∂(P i N) ≤ ENNReal.ofReal C

/-- Corollary 9.7 (S:W:cor:round2-weighted-field-moments, TeX S L7256-7282): weighted field moments.  Under the hypotheses of
Proposition 9.5 (`IsRound2Density`, Gaussian upper bound, `HasR2ActualDensity` for `N ≥ 2`), for `Pw ≥ 0`, integers `k > d/2+2`,
`m > k + d/2` and every finite `r ≥ 1`: `sup_N E[‖√N(μ_N-μ)‖^r_{-m,P} + ‖𝓡_N‖^r_{-m,P}] < ∞`, and the same for the exactly
centered distributions; in the stationary-reference temperature-quench setting of Corollary 9.3 (Markov particle
semigroup preserving `Q_{N,b}`, initial law `Q_{N,b₀}`) it is uniform over all times.  (`k` is used only in the proof.)  The
constants depend on `(d,σ,M,L,C₀,c₀,b,p,K,Pw,m,r)` (and `b₀` in the quench clause).  AMBIGUITY: `‖·‖_{-m,P}` is the dual
norm of the weighted `H^m`, computed on Schwartz tests; for the (separable-Hilbert-valued) random distribution it is measurable
(source L7345-7346), so the lower integral `∫⁻` is the expectation. -/
theorem round2_weighted_field_moments (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (M L C₀ c₀ b p K Pw : ℝ) (hb : 0 < b) (hp : 1 < p) (hPw : 0 ≤ Pw) (k m : ℕ)
    (hk : (d : ℝ) / 2 + 2 < k) (hm : (k : ℝ) + (d : ℝ) / 2 < m) (r : ℝ) (hr : 1 ≤ r) :
    (∃ C : ℝ, ∀ ρ : Euc d → ℝ, IsRound2Density d s M L ρ → HasR2GaussianUpper C₀ c₀ ρ →
      ∀ P : ∀ N, Measure (EucConfig d N),
      (∀ N, 2 ≤ N → HasR2ActualDensity s b p K (withDensityReal ρ) (P N)) →
      R2WeightedFieldBound (ι := Unit) s m Pw r C (fun _ => withDensityReal ρ) (fun _ => P)) ∧
    ∀ b₀ : ℝ, 0 < b₀ → ∃ C : ℝ, ∀ ρ : Euc d → ℝ, IsRound2Density d s M L ρ → HasR2GaussianUpper C₀ c₀ ρ →
      ∀ Kt : ∀ N, ℝ≥0 → Kernel (EucConfig d N) (EucConfig d N), (∀ N, IsR2ParticleSemigroup (Kt N)) →
      (∀ N, 2 ≤ N → ∀ t, (modulatedGibbs (rieszKernel d s) N b (withDensityReal ρ)).bind (Kt N t) =
        modulatedGibbs (rieszKernel d s) N b (withDensityReal ρ)) →
      R2WeightedFieldBound s m Pw r C (fun _ : ℝ≥0 => withDensityReal ρ) (fun t N =>
        (modulatedGibbs (rieszKernel d s) N b₀ (withDensityReal ρ)).bind (Kt N t)) := by
  sorry

end WeightedField

/-! ### S9.8 - S9.10: the interacting static field correction -/

section InteractingStatic

variable {s : ℝ}

/-- The continuous representative `x ↦ (R_{γ,μ} P_μ ψ)(x)` of the response `R_{γ,μ}P_μψ`: `P_μψ(x) - γ (K_μ h)(x)`
with `h = responseInverse ..` (the response equation `h + γ K_μ h = P_μ ψ`, S L7378-7379); since `K_μ h` only depends on
the `μ`-class of `h` it is an everywhere-defined function equal to `h` `μ`-a.e. -/
def responseRepW (g : Euc d → ℝ) (μ : Measure (Euc d)) (γ : ℝ) (ψ : Euc d → ℝ) (x : Euc d) : ℝ :=
  projMean μ ψ x - γ * Kop g μ (responseInverse g μ γ ψ) x

/-- Lemma 9.8 (S:W:lem:r2-screened, TeX S L7391-7402): screened transport at the preparation parameter.  Standing assumptions of
S9.8-S9.10 (S L7358-7389): `d ≥ 2`, `a, β, γ > 0`, `0 ≤ σ < d/2`, `V = a|x|²/2`, `μ = ρ dx` the thermal equilibrium
(`IsThermalEquilibrium`), `g = |x|^{-σ}` or `-log|x|`.  For every integer `k ≥ 1` and integer `J > k+1+d/2` and every
`φ ∈ C_b^J` (resp. `φ ∈ H^J`) the function `a_φ = R_γ P_μ φ` (the response, `IsResponse`, in its continuous representative
`responseRepW`) admits a vector field `v_φ` with `-div(ρ v_φ) = ρ a_φ` and `‖a_φ‖_{C_b^k} + ‖v_φ‖_{C_b^k} ≤ C‖φ‖_{C_b^J}`
(resp. `≤ C‖φ‖_{H^J}`), `C` depending on the fixed physical and preparation parameters and `(k,J)` but not on the support of
`φ` (quantified before `φ`; `ρ` is the thermal density, determined by `(d,σ,a,β)`).  Technical: `ρ v_φ` is differentiable (so
that `div` is the derivative, not Lean's junk `0`); `‖a_φ‖_{C_b^k}` is real because `MemCb k a_φ` is part of the conclusion. -/
theorem r2_screened (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (a β γ : ℝ) (ha : 0 < a)
    (hβ : 0 < β) (hγ : 0 < γ) (k J : ℕ) (hk : 1 ≤ k) (hJ : (k : ℝ) + 1 + (d : ℝ) / 2 < J) :
    ∃ C : ℝ, ∀ ρ : Euc d → ℝ, IsThermalEquilibrium d s a β ρ →
      (∀ φ : Euc d → ℝ, MemCb J φ →
        ∃ v : Euc d → Euc d,
          IsResponse (rieszKernel d s) (withDensityReal ρ) γ φ
            (responseRepW (rieszKernel d s) (withDensityReal ρ) γ φ) ∧
          MemCb k (responseRepW (rieszKernel d s) (withDensityReal ρ) γ φ) ∧ ContDiff ℝ k v ∧
          Differentiable ℝ (fun y => ρ y • v y) ∧
          (∀ x, -movDiv (fun y => ρ y • v y) x =
            ρ x * responseRepW (rieszKernel d s) (withDensityReal ρ) γ φ x) ∧
          ENNReal.ofReal (cbNorm k (responseRepW (rieszKernel d s) (withDensityReal ρ) γ φ)) +
              cbNormVecE k v ≤ ENNReal.ofReal (C * cbNorm J φ)) ∧
      (∀ φ : Euc d → ℝ, MemHSmooth J φ →
        ∃ v : Euc d → Euc d,
          IsResponse (rieszKernel d s) (withDensityReal ρ) γ φ
            (responseRepW (rieszKernel d s) (withDensityReal ρ) γ φ) ∧
          MemCb k (responseRepW (rieszKernel d s) (withDensityReal ρ) γ φ) ∧ ContDiff ℝ k v ∧
          Differentiable ℝ (fun y => ρ y • v y) ∧
          (∀ x, -movDiv (fun y => ρ y • v y) x =
            ρ x * responseRepW (rieszKernel d s) (withDensityReal ρ) γ φ x) ∧
          ENNReal.ofReal (cbNorm k (responseRepW (rieszKernel d s) (withDensityReal ρ) γ φ)) +
              cbNormVecE k v ≤ ENNReal.ofReal (C * sobolevWNorm J 2 φ)) := by
  sorry

/-- The element `ℓ_x ∈ B_m` of `W:eq:r2-cubic-static` (S L7442-7443): `ℓ_x(φ) = (R_γ P_μ φ)(x)`, defined through its
values `ℓ_x(h_α) = (R_γ P_μ h_α)(x)` on the Hermite functions (continuous representative `responseRepW`). -/
def r2EllPt (g : Euc d → ℝ) (μ : Measure (Euc d)) (γ : ℝ) (m : ℕ) (x : Euc d) : OscDual d (m : ℝ) :=
  OscDual.ofSeq (m : ℝ) fun α => responseRepW g μ γ (hermiteFunD α) x

/-- The conclusion of Proposition 9.9 (S L7452-7470) for the thermal density `ρ`, preparation parameter `γ` and oscillator
index `m`: there is a centered Gaussian `G ∈ B_m` (law `G`) with `E[G(φ)G(ψ)] = μ((P_μφ)R_γP_μψ)` (`susceptibilityCov`); the
map `x ↦ ℓ_x` is bounded in `B_m` with continuous coordinates and `K_{γ,μ} = ∫ℓ_x^{⊗3}dμ(x)` is a Bochner projective tensor
in `B_m^{⊗̂π3}` (`projTensor`; its pairing with a trilinear form `T` is `∫T[ℓ_x,ℓ_x,ℓ_x]dμ`; claims of S L7444-7450);
`W_N = √N(μ_N - Eμ_N)` (`zetaB`, `X_N ∼ Q_{N,γ}(μ)`) is measurable; and
`lim_N sup_{‖Φ‖_{C_b^5(B_m)} ≤ 1} |√N{EΦ(W_N) - EΦ(G)} - (1/6)E D³Φ(G)[K_{γ,μ}]| = 0` (written `∀ ε > 0, ∃ N₀, ∀ N ≥ N₀, ∀ Φ`). -/
def R2StaticEdgeworth (d : ℕ) (s γ : ℝ) (m : ℕ) (ρ : Euc d → ℝ) : Prop :=
  ∃ G : Measure (OscDual d (m : ℝ)), IsProbabilityMeasure G ∧
    IsCenteredGaussianOsc (m : ℝ) G (susceptibilityCov (rieszKernel d s) (withDensityReal ρ) γ) ∧
    (∃ Kb : ℝ, ∀ x, ‖r2EllPt (rieszKernel d s) (withDensityReal ρ) γ m x‖ ≤ Kb) ∧
    (∀ α, Continuous fun x => OscDual.coord (r2EllPt (rieszKernel d s) (withDensityReal ρ) γ m x) α) ∧
    (∃ K : projTensor (OscDual d (m : ℝ)) 3, ∀ T : (OscDual d (m : ℝ)) [×3]→L[ℝ] ℝ,
      (K : TensorDual (OscDual d (m : ℝ)) 3) T =
        ∫ x, T ![r2EllPt (rieszKernel d s) (withDensityReal ρ) γ m x,
          r2EllPt (rieszKernel d s) (withDensityReal ρ) γ m x,
          r2EllPt (rieszKernel d s) (withDensityReal ρ) γ m x] ∂(withDensityReal ρ)) ∧
    (∀ N : ℕ, 2 ≤ N →
      Measurable (zetaB (m : ℝ) (modulatedGibbs (rieszKernel d s) N γ (withDensityReal ρ)))) ∧
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, 2 ≤ N → ∀ Φ ∈ CbUnitBall (OscDual d (m : ℝ)) 5,
      |Real.sqrt N *
          (∫ X, Φ (zetaB (m : ℝ) (modulatedGibbs (rieszKernel d s) N γ (withDensityReal ρ)) X)
              ∂(modulatedGibbs (rieszKernel d s) N γ (withDensityReal ρ)) - ∫ F, Φ F ∂G) -
        (1 / 6) * ∫ F, ∫ x, iteratedFDeriv ℝ 3 Φ F
            ![r2EllPt (rieszKernel d s) (withDensityReal ρ) γ m x,
              r2EllPt (rieszKernel d s) (withDensityReal ρ) γ m x,
              r2EllPt (rieszKernel d s) (withDensityReal ρ) γ m x] ∂(withDensityReal ρ) ∂G| ≤ ε

/-- Proposition 9.9 (S:W:thm:r2-static-edgeworth, TeX S L7452-7470): interacting static field Edgeworth expansion.  Fix
`d ≥ 2`, `a, β, γ > 0`, `0 ≤ σ < d/2` (including the logarithm with its whole-space normalisation), `μ = ρ dx` the thermal
equilibrium of `V = a|x|²/2` at inverse temperature `β`, `X_N ∼ Q_{N,γ}(μ)` (`W:eq:r2-static-law`; `γ = β` is the canonical
Gibbs ensemble) and the oscillator index `m` an integer with `m > J + 2d + 4`, `J = 4d + 40` (S L7431).  Then
`R2StaticEdgeworth` holds.  The statement for `ε → 0` is the tail form of the uniform limit over the unit ball of `C_b^5(B_m)`
(AMBIGUITY: the sup over `Φ` of a family bounded by `2√N + ...`; no junk).  Technical: `N ≥ 2`. -/
theorem r2_static_edgeworth (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (a β γ : ℝ) (ha : 0 < a)
    (hβ : 0 < β) (hγ : 0 < γ) (m : ℕ) (hm : ((4 * d + 40 : ℕ) : ℝ) + 2 * d + 4 < m) :
    ∀ ρ : Euc d → ℝ, IsThermalEquilibrium d s a β ρ → R2StaticEdgeworth d s γ m ρ := by
  sorry

/-- Static Edgeworth expansion at `γ = 0` for the independent preparation (`Supplement repair S11.6(c) at γ = 0`, docs/ISSUES.md;
needed by item (c) of `r2_log_path`, S11.6, TeX S L9578-9585, where Proposition 9.9 does not apply because it is stated for `γ > 0`):
for every probability density `ρ` on `ℝ^d` (measurable, nonnegative, `∫ρ = 1`), `d ≥ 2`, and every oscillator index `m > J + 2d + 4`,
`J = 4d + 40`, `R2StaticEdgeworth d 0 0 m ρ` holds.  At `γ = 0` the preparation is the product measure
`Q_{N,0}(μ) = μ^{⊗N}` (Gibbs normaliser `∫ 1 = 1`), `R_0 = I` so `responseRepW` is `P_μ` (`φ ↦ φ - μ(φ)`), `X ↦ zetaB m` is a sum of `N` iid
bounded `B_m`-valued centered summands `ℓ_x`, the Gaussian covariance is `μ((P_μφ)(P_μψ))` and the cubic tensor is `∫ℓ_x^{⊗3}dμ`; the
expansion is the Hilbert-space Edgeworth expansion of iid sums (`HRS.hilbert_edgeworth_C4`, using `CbUnitBall 5 ⊆ CbUnitBall 4`).
No thermal-equilibrium or Gaussian-tail assumption is needed.  Faithful to TeX S L9578-9585 (item (c) of S11.6); `s = 0` is the logarithmic
kernel of S11.6, but the statement does not depend on `s` at `γ = 0`. -/
theorem r2_static_edgeworth_iid (hd : 2 ≤ d) (m : ℕ) (hm : ((4 * d + 40 : ℕ) : ℝ) + 2 * d + 4 < m)
    (ρ : Euc d → ℝ) (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x = 1) :
    R2StaticEdgeworth d 0 0 m ρ := by
  sorry

end InteractingStatic


/-! ### S9.10: summable observation families and the initial path -/

section ObservationFamily

variable {s : ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- `ℓ_x = ∑_j (R_γP_μψ_j)(x) e_j ∈ H` (S L7648; continuous representatives `responseRepW`). -/
def r2EllH (e : HilbertBasis ℕ ℝ H) (ψ : ℕ → Euc d → ℝ) (g : Euc d → ℝ) (μ : Measure (Euc d)) (γ : ℝ)
    (x : Euc d) : H :=
  ∑' j, responseRepW g μ γ (ψ j) x • (e j)

/-- `W_N^H = ∑_j √N(μ_N - Eμ_N)(ψ_j) e_j` (S L7643), the centering `Eμ_N` being that of the law `P`. -/
def r2FieldH {N : ℕ} (e : HilbertBasis ℕ ℝ H) (ψ : ℕ → Euc d → ℝ) (P : Measure (EucConfig d N))
    (X : EucConfig d N) : H :=
  ∑' j, (Real.sqrt N * (pair (empirical X) (ψ j) - pair (meanEmpirical P) (ψ j))) • (e j)

/-- Corollary 9.10 (S:W:cor:r2-static-observation-family, TeX S L7637-7664), first assertion.  `H` a real separable Hilbert space
with orthonormal basis `(e_j)_{j∈ℕ}` (`HilbertBasis`; infinite-dimensional `H` is a technical restriction of the indexing),
`ψ_j` real smooth bounded functions (`MemCb (4d+40)`) with `∑_j ‖ψ_j‖_{C_b^{4d+40}} < ∞`.  Under the standing assumptions of S9.8-S9.10
(`d ≥ 2`, `a, β, γ > 0`, `0 ≤ σ < d/2`, `ρ` the thermal density, `X_N ∼ Q_{N,γ}(μ)`), `W_N^H = ∑_j√N(μ_N-Eμ_N)(ψ_j)e_j` satisfies
the uniform `C_b^5(H)` expansion of Proposition 9.9 with the centered Gaussian `G` in `H` of covariance
`E[⟨G,e_j⟩⟨G,e_k⟩] = μ((P_μψ_j)R_γP_μψ_k)` and the tensor `∫(∑_jR_γP_μψ_j(x)e_j)^{⊗3}dμ(x)` (a Bochner projective tensor
with bounded integrand). -/
theorem r2_static_observation_family (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (a β γ : ℝ)
    (ha : 0 < a) (hβ : 0 < β) (hγ : 0 < γ) (e : HilbertBasis ℕ ℝ H) (ψ : ℕ → Euc d → ℝ)
    (hψ : ∀ j, MemCb (4 * d + 40) (ψ j)) (hsum : Summable fun j => cbNorm (4 * d + 40) (ψ j)) :
    ∀ ρ : Euc d → ℝ, IsThermalEquilibrium d s a β ρ →
      ∃ G : Measure H, IsProbabilityMeasure G ∧ IsCenteredGaussian G ∧
        (∀ j k, Integrable (fun z : H => inner ℝ (e j) z * inner ℝ (e k) z) G ∧
          ∫ z, inner ℝ (e j) z * inner ℝ (e k) z ∂G =
            susceptibilityCov (rieszKernel d s) (withDensityReal ρ) γ (ψ j) (ψ k)) ∧
        (∃ Kb : ℝ, ∀ x, ‖r2EllH e ψ (rieszKernel d s) (withDensityReal ρ) γ x‖ ≤ Kb) ∧
        (∃ K : projTensor H 3, ∀ T : H [×3]→L[ℝ] ℝ, (K : TensorDual H 3) T =
          ∫ x, T ![r2EllH e ψ (rieszKernel d s) (withDensityReal ρ) γ x,
            r2EllH e ψ (rieszKernel d s) (withDensityReal ρ) γ x,
            r2EllH e ψ (rieszKernel d s) (withDensityReal ρ) γ x] ∂(withDensityReal ρ)) ∧
        (∀ N : ℕ, 2 ≤ N →
          Measurable (r2FieldH e ψ (modulatedGibbs (rieszKernel d s) N γ (withDensityReal ρ)))) ∧
        ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, 2 ≤ N → ∀ Φ ∈ CbUnitBall H 5,
          |Real.sqrt N *
              (∫ X, Φ (r2FieldH e ψ (modulatedGibbs (rieszKernel d s) N γ (withDensityReal ρ)) X)
                  ∂(modulatedGibbs (rieszKernel d s) N γ (withDensityReal ρ)) - ∫ F, Φ F ∂G) -
            (1 / 6) * ∫ F, ∫ x, iteratedFDeriv ℝ 3 Φ F
                ![r2EllH e ψ (rieszKernel d s) (withDensityReal ρ) γ x,
                  r2EllH e ψ (rieszKernel d s) (withDensityReal ρ) γ x,
                  r2EllH e ψ (rieszKernel d s) (withDensityReal ρ) γ x] ∂(withDensityReal ρ) ∂G| ≤ ε := by
  sorry

end ObservationFamily

section InitialPath

variable {s : ℝ}

/-- The cosine orthonormal basis `e_n` of `L²([0,T])`: `e_0 = T^{-1/2}`, `e_n = √(2/T) cos(nπt/T)` (S L3552). -/
def r2CosBasis (T : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  if n = 0 then 1 / Real.sqrt T else Real.sqrt (2 / T) * Real.cos (n * Real.pi * t / T)

/-- `f_{n,α}(x) = (1+n²)^{3/8} ∫_0^T e_n(t) U^{0,t}φ_α(x) dt` (S L3554), `φ_α = λ_α^{-m/2}h_α`,
`U^{0,t} = propagatorW C 0 t` the adjoint evolution along the coefficients `C`. -/
def r2CosOrbitTest (C : WholeCoeff d) (m : ℝ) (T : ℝ) (n : ℕ) (α : MultiIndex d) (x : Euc d) : ℝ :=
  (1 + (n : ℝ) ^ 2) ^ ((3 : ℝ) / 8) *
    ∫ t in Set.Icc (0 : ℝ) T, r2CosBasis T n t * propagatorW C 0 t (oscTestFun m α) x

/-- The initial orbit field `t ↦ (√N(μ_N - Eμ_N)(U^{0,t}φ_α))_α ∈ B_m` (S L7651-7653) as a function of `t`. -/
def r2InitFun (C : WholeCoeff d) (m : ℝ) {N : ℕ} (P : Measure (EucConfig d N)) (X : EucConfig d N)
    (t : ℝ) : OscDual d m :=
  ellVec m fun α =>
    Real.sqrt N * (pair (empirical X) (propagatorW C 0 t (oscTestFun m α)) -
      pair (meanEmpirical P) (propagatorW C 0 t (oscTestFun m α)))

/-- The initial orbit field as an element of `𝒳_T = C([0,T];B_m)` (`0` if the path is not continuous, which is excluded in the
conclusions). -/
def r2InitPath (C : WholeCoeff d) (m : ℝ) (T : ℝ) {N : ℕ} (P : Measure (EucConfig d N))
    (X : EucConfig d N) : OscPath d m T :=
  windowPathOf m T 0 (r2InitFun C m P X)

/-- The path `t ↦ ℓ_x^0(t)` with `ℓ_x^0(t)(φ_α) = (R_γP_μU^{0,t}φ_α)(x)` (`W:eq:r2-initial-path-tensor`, S L7660-7662), as a function of `t`. -/
def r2EllFun (C : WholeCoeff d) (g : Euc d → ℝ) (μ : Measure (Euc d)) (γ : ℝ) (m : ℝ) (x : Euc d)
    (t : ℝ) : OscDual d m :=
  ellVec m fun α => responseRepW g μ γ (propagatorW C 0 t (oscTestFun m α)) x

/-- The continuous path `ℓ_x^0 ∈ 𝒳_T` (`0` if not continuous, excluded in the conclusions). -/
def r2EllPath (C : WholeCoeff d) (g : Euc d → ℝ) (μ : Measure (Euc d)) (γ : ℝ) (m : ℝ) (T : ℝ)
    (x : Euc d) : OscPath d m T :=
  windowPathOf m T 0 (r2EllFun C g μ γ m x)

/-- The conclusion of the second assertion of S9.10 (S L7649-7663) for the coefficients `C` (adjoint `U^{0,t} = propagatorW C 0 t`),
reference density `ρ`, preparation `γ`, oscillator index `m` and horizon `T`: there is a centered Gaussian path `G` in
`𝒳 = C([0,T];B_m)` with `E[G^t(φ_α)G^{t'}(φ_{α'})] = μ((P_μU^{0,t}φ_α)R_γP_μU^{0,t'}φ_{α'})` (`susceptibilityCov`, coordinates), the paths `ℓ_x^0` are bounded
in `𝒳` and `𝒦_0^{path} = ∫(ℓ_x^0)^{⊗3}dμ` is a Bochner projective tensor, the initial orbit field `W_N^{path}` (`r2InitPath`) is measurable,
and `lim_N sup_{‖Φ‖_{C_b^5(𝒳)}≤1}|√N{EΦ(W_N^{path}) - EΦ(G)} - (1/6)E D³Φ(G)[𝒦_0^{path}]| = 0` for `X_N ∼ Q_{N,γ}(μ)`. -/
def R2InitPathEdgeworth (C : WholeCoeff d) (s γ : ℝ) (m : ℕ) (T : ℝ) (ρ : Euc d → ℝ) : Prop :=
  ∃ G : Measure (OscPath d (m : ℝ) T), IsProbabilityMeasure G ∧ IsCenteredGaussian G ∧
    (∀ (t t' : Set.Icc (0 : ℝ) T) (α α' : MultiIndex d),
      Integrable (fun w => OscDual.coord (OscPath.at' w t) α * OscDual.coord (OscPath.at' w t') α') G ∧
      ∫ w, OscDual.coord (OscPath.at' w t) α * OscDual.coord (OscPath.at' w t') α' ∂G =
        susceptibilityCov (rieszKernel d s) (withDensityReal ρ) γ
          (propagatorW C 0 t (oscTestFun (m : ℝ) α)) (propagatorW C 0 t' (oscTestFun (m : ℝ) α'))) ∧
    (∀ x, Continuous fun t : Set.Icc (0 : ℝ) T =>
      r2EllFun C (rieszKernel d s) (withDensityReal ρ) γ (m : ℝ) x t) ∧
    (∀ N : ℕ, 2 ≤ N → ∀ X, Continuous fun t : Set.Icc (0 : ℝ) T =>
      r2InitFun C (m : ℝ) (modulatedGibbs (rieszKernel d s) N γ (withDensityReal ρ)) X t) ∧
    (∃ Kb : ℝ, ∀ x, ‖r2EllPath C (rieszKernel d s) (withDensityReal ρ) γ (m : ℝ) T x‖ ≤ Kb) ∧
    (∃ K : projTensor (OscPath d (m : ℝ) T) 3, ∀ T' : (OscPath d (m : ℝ) T) [×3]→L[ℝ] ℝ,
      (K : TensorDual (OscPath d (m : ℝ) T) 3) T' =
        ∫ x, T' ![r2EllPath C (rieszKernel d s) (withDensityReal ρ) γ (m : ℝ) T x,
          r2EllPath C (rieszKernel d s) (withDensityReal ρ) γ (m : ℝ) T x,
          r2EllPath C (rieszKernel d s) (withDensityReal ρ) γ (m : ℝ) T x] ∂(withDensityReal ρ)) ∧
    (∀ N : ℕ, 2 ≤ N → Measurable (r2InitPath C (m : ℝ) T
      (modulatedGibbs (rieszKernel d s) N γ (withDensityReal ρ)))) ∧
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, 2 ≤ N → ∀ Φ ∈ CbUnitBall (OscPath d (m : ℝ) T) 5,
      |Real.sqrt N *
          (∫ X, Φ (r2InitPath C (m : ℝ) T (modulatedGibbs (rieszKernel d s) N γ (withDensityReal ρ)) X)
              ∂(modulatedGibbs (rieszKernel d s) N γ (withDensityReal ρ)) - ∫ F, Φ F ∂G) -
        (1 / 6) * ∫ F, ∫ x, iteratedFDeriv ℝ 3 Φ F
            ![r2EllPath C (rieszKernel d s) (withDensityReal ρ) γ (m : ℝ) T x,
              r2EllPath C (rieszKernel d s) (withDensityReal ρ) γ (m : ℝ) T x,
              r2EllPath C (rieszKernel d s) (withDensityReal ρ) γ (m : ℝ) T x] ∂(withDensityReal ρ) ∂G| ≤ ε

/-- Corollary 9.10 (S:W:cor:r2-static-observation-family, TeX S L7637-7664), second assertion ("in particular"): the entire initial
propagated path `t ↦ (√N(μ_N-Eμ_N)(U^{0,t}φ_j))_j ∈ C([0,T];B_m)` satisfies the uniform `C_b^5(𝒳)` expansion of Proposition 9.9
(`R2InitPathEdgeworth`): centered Gaussian path `G` of covariance `E[G^t(φ_α)G^{t'}(φ_{α'})] = μ((P_μU^{0,t}φ_α)R_γP_μU^{0,t'}φ_{α'})` on the dual-test coordinates `φ_α` (as `IsCenteredGaussianOsc`; this needs adjoint solutions only for the `φ_α`), continuity of the paths `t ↦ ℓ_x^0(t)` and of the initial orbit field (S L7658: "the continuous paths `ℓ_x^0`"), correction tensor
`𝒦_0^{path} = ∫(ℓ_x^0)^{⊗3}dμ(x)`, a Bochner projective tensor of the continuous paths `ℓ_x^0`.  Setting: the stationary quadratic
mean-field coefficients `(quadraticGradientDyn d s a β).coeff (fun _ => ρ)`, horizon `T > 0`, and the input
`W:r2:initial-orbit-summability` (S L3558-3560) at the index `k ≥ 4d+40` (`f_{n,α} ∈ C_b^k`, `∑_{n,α}‖f_{n,α}‖_{C_b^k} < ∞`,
supplied by the adjoint estimates of S5.1), existence of the classical adjoint solutions, and the "correspondingly increased"
oscillator index `m > k + 2d + 4` (AMBIGUITY: the source does not name the increased index; chosen as in S9.9 with `J := k`).
Technical hypotheses: the adjoint existence and summability inputs, `T > 0`; measurability of the initial path is part of the conclusion. -/
theorem r2_static_observation_path (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (a β γ : ℝ)
    (ha : 0 < a) (hβ : 0 < β) (hγ : 0 < γ) (T : ℝ) (hT : 0 < T) (k m : ℕ) (hk : 4 * d + 40 ≤ k)
    (hm : (k : ℝ) + 2 * d + 4 < m) :
    ∀ ρ : Euc d → ℝ, IsThermalEquilibrium d s a β ρ →
      (∀ α : MultiIndex d, ∀ t ∈ Set.Icc (0 : ℝ) T, ∃ f : ℝ → Euc d → ℝ,
        IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) t
          (oscTestFun (m : ℝ) α) f) →
      (∀ n α, MemCb k (r2CosOrbitTest ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) (m : ℝ) T n α)) →
      (Summable fun q : ℕ × MultiIndex d =>
        cbNorm k (r2CosOrbitTest ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) (m : ℝ) T q.1 q.2)) →
      R2InitPathEdgeworth ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) s γ m T ρ := by
  sorry

/-- Initial-path Edgeworth expansion at `γ = 0` and `s = 0` for the independent preparation (`Supplement repair S11.6(c) at γ = 0`,
docs/ISSUES.md): the path half of item (c) of `r2_log_path` (S11.6, TeX S L9578-9585), for which `r2_static_observation_path` does not apply
(`hγ : 0 < γ`).  The coefficients are the quadratic mean-field coefficients along an arbitrary trajectory `ρ` (`IsR2WindowTrajectory` gives
`IsProbDensity (ρ 0)`: in the stationary case from `IsThermalEquilibrium`, in the resulting-solution case from `IsWholeMeanFieldSolution.density` at `t = 0`),
with the same adjoint-existence and cosine-orbit summability inputs (`k ≥ 4d+40`, `m > k+2d+4`) as `r2_static_observation_path` and `r2_log_path` (c);
`Q_{N,0}(ρ 0) = (ρ 0)^{⊗N}` and `R_0 = I`.  The statement is `R2InitPathEdgeworth` at `(s, γ) = (0, 0)`.
Repair S11.6 (2026-10-22, approved): the hypothesis `hcont` (continuity on `[0,T]` of the initial orbit
`t ↦ U^{0,t}φ_α(x)`, tacit in S L3558-3570 (the `f_{n,j}` are cosine coefficients of the classical orbit) and S L7658 ("the continuous paths ℓ_x^0")) is added; it does not follow from the other
hypotheses (arbitrary coefficients `C`). -/
theorem r2_static_observation_path_iid (hd : 2 ≤ d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) (T : ℝ) (hT : 0 < T)
    (k m : ℕ) (hk : 4 * d + 40 ≤ k) (hm : (k : ℝ) + 2 * d + 4 < m) :
    ∀ ρ : ℝ → Euc d → ℝ, IsProbDensity (ρ 0) →
      (∀ α : MultiIndex d, ∀ t ∈ Set.Icc (0 : ℝ) T, ∃ f : ℝ → Euc d → ℝ,
        IsClassicalAdjointW ((quadraticGradientDyn d 0 a β).coeff ρ) t (oscTestFun (m : ℝ) α) f) →
      (∀ n α, MemCb k (r2CosOrbitTest ((quadraticGradientDyn d 0 a β).coeff ρ) (m : ℝ) T n α)) →
      (Summable fun q : ℕ × MultiIndex d =>
        cbNorm k (r2CosOrbitTest ((quadraticGradientDyn d 0 a β).coeff ρ) (m : ℝ) T q.1 q.2)) →
      (∀ (α : MultiIndex d) (x : Euc d),
        ContinuousOn (fun t => propagatorW ((quadraticGradientDyn d 0 a β).coeff ρ) 0 t
          (oscTestFun (m : ℝ) α) x) (Set.Icc (0 : ℝ) T)) →
      R2InitPathEdgeworth ((quadraticGradientDyn d 0 a β).coeff ρ) 0 0 m T (ρ 0) := by
  sorry

end InitialPath

end HRS.Whole
