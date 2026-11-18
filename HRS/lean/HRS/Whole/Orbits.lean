import HRS.Whole.Adjoint
import HRS.Whole.RegMF
import HRS.Energy.StaticLimitGauss
import HRS.Prob.HilbertMartingale

/-!
# Whole-field paths from bounded adjoint orbits: Sections S5.2, S5.4, S5.5, S5.7

Source: HRS whole-space supplement (S).

* S5.2 `W:r2:orbit-maximal` (S lines 3363-3390), with the orbit feature `W:r2:orbit-feature`
  (3330-3334) and its bounds `W:r2:feature-derivatives` (3340-3345);
* S5.4 `W:r2:weighted-higher-order` (3769-3790);
* S5.5 `W:r2:general-orbits` (3884-3905), with the Section S5 standing hypotheses
  (S lines 3828-3852) collected in `WholeSetup` (ISSUES Q1);
* S5.7 `W:r2:fixed-equation` (4078-4106).

## Representation decisions

* `ℓ²` (the coordinates `(z(φ_j))_j` of the oscillator test family `φ_j = λ_j^{-m/2} h_j`) is
  `OscDual d m` itself (its norm is `‖z‖_{B_m}`), the Hermite coordinates being indexed by
  `MultiIndex d` instead of an enumeration `j ≥ 1` (a bijection preserving eigenvalue order).
* `𝒦 = H¹([0,T];ℓ²) ⊕ ℓ²` (S line 3333) is `KSpace d m T`, the `ℓ²`-sum
  `ℓ² × L²([0,T];ℓ²) × ℓ²` with elements `(A₀, A', B)` representing the pair
  `(A, B)`, `A(t) = A₀ + ∫_0^t A'` (`KSpace.evalA`).  The norm `(‖A₀‖²+‖A'‖²+‖B‖²)^{1/2}` is
  equivalent to the `H¹ ⊕ ℓ²` norm on `[0,T]` (constants depend on `T`).  The feature
  `Γ_{r,a}(x)` has `A₀ = B = (∂_aφ_j(x))_j` and weak derivative
  `A'(t) = 1_{t>r}(∂_a U(r,t) L_t φ_j(x))_j` (S lines 3338-3339, 3892-3893); that this is the true
  weak time derivative of `t ↦ ∂_a U(r,max(t,r))φ_j(x)` is the content of `∂_t U_t f = U_t L f`
  (S5.1) and is not re-asserted.
* A continuous `𝒦`-martingale with a given covariance density is
  `HRS.IsHilbertMartingaleWithCovariation` (CLT-02 layer; the covariance density is a bilinear-form
  valued process).  "Trace" is `HRS.traceNormForm` (for the positive trace-class forms of this
  layer it is the trace).
* `E‖TM‖²_{C_tB_m}` is the `ℝ≥0∞`-valued `∫⁻ (sup_t ‖(TM)(t)‖)²`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole

variable {d : ℕ}

/-! ### `ℓ²`, `𝒦`, features -/

open Classical in
/-- The element of `ℓ² = OscDual d m` with coordinates `c` (`0` if `c ∉ ℓ²`). -/
def ellVec (m : ℝ) (c : MultiIndex d → ℝ) : OscDual d m :=
  if h : Memℓp c 2 then (⟨c, h⟩ : lp (fun _ : MultiIndex d => ℝ) 2) else 0

/-- `‖c‖_{ℓ²} = (∑ c_α²)^{1/2}` in `ℝ≥0∞` (`⊤` if `c ∉ ℓ²`). -/
def l2NormE {ι : Type*} (c : ι → ℝ) : ℝ≥0∞ := (∑' α, ENNReal.ofReal (c α ^ 2)) ^ (1 / 2 : ℝ)

instance (m : ℝ) : TopologicalSpace.SeparableSpace (OscDual d m) :=
  HRS.StaticLimitAux.separable_lp (ι := MultiIndex d)

instance (m : ℝ) : SecondCountableTopology (OscDual d m) :=
  UniformSpace.secondCountable_of_separable _

instance fact_two_ne_top_ennreal : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩

/-- `L²([0,T]; ℓ²)`. -/
abbrev L2Path (d : ℕ) (m T : ℝ) : Type := Lp (OscDual d m) 2 (volume.restrict (Set.Icc (0 : ℝ) T))

/-- `𝒦 = H¹([0,T];ℓ²) ⊕ ℓ²`, as `ℓ² × L²([0,T];ℓ²) × ℓ²` (see the module docstring). -/
def KSpace (d : ℕ) (m T : ℝ) : Type :=
  WithLp 2 (OscDual d m × WithLp 2 (L2Path d m T × OscDual d m))

namespace KSpace

variable {m T : ℝ}

instance : NormedAddCommGroup (KSpace d m T) :=
  inferInstanceAs (NormedAddCommGroup (WithLp 2 (OscDual d m × WithLp 2 (L2Path d m T × OscDual d m))))

instance : InnerProductSpace ℝ (KSpace d m T) :=
  inferInstanceAs (InnerProductSpace ℝ (WithLp 2 (OscDual d m × WithLp 2 (L2Path d m T × OscDual d m))))

instance : CompleteSpace (KSpace d m T) :=
  inferInstanceAs (CompleteSpace (WithLp 2 (OscDual d m × WithLp 2 (L2Path d m T × OscDual d m))))

instance : SecondCountableTopology (KSpace d m T) :=
  inferInstanceAs (SecondCountableTopology
    (WithLp 2 (OscDual d m × WithLp 2 (L2Path d m T × OscDual d m))))

instance : MeasurableSpace (KSpace d m T) := borel _

instance : BorelSpace (KSpace d m T) := ⟨rfl⟩

/-- The element `(A₀, A', B)`. -/
def mk (a₀ : OscDual d m) (a' : L2Path d m T) (b : OscDual d m) : KSpace d m T :=
  WithLp.toLp 2 (a₀, WithLp.toLp 2 (a', b))

/-- The initial value `A(0)` of the `H¹` component. -/
def A₀ (x : KSpace d m T) : OscDual d m :=
  (WithLp.ofLp (show WithLp 2 (OscDual d m × WithLp 2 (L2Path d m T × OscDual d m)) from x)).1

/-- The weak derivative `A'` of the `H¹` component. -/
def A' (x : KSpace d m T) : L2Path d m T :=
  (WithLp.ofLp (WithLp.ofLp
    (show WithLp 2 (OscDual d m × WithLp 2 (L2Path d m T × OscDual d m)) from x)).2).1

/-- The `ℓ²` component `B`. -/
def B (x : KSpace d m T) : OscDual d m :=
  (WithLp.ofLp (WithLp.ofLp
    (show WithLp 2 (OscDual d m × WithLp 2 (L2Path d m T × OscDual d m)) from x)).2).2

/-- The value `A(t) = A₀ + ∫_0^t A'` of the `H¹([0,T];ℓ²)` component at `t ∈ [0,T]`. -/
def evalA (x : KSpace d m T) (t : ℝ) : OscDual d m :=
  x.A₀ + ∫ τ in Set.Icc (0 : ℝ) (min t T), (x.A' : ℝ → OscDual d m) τ

end KSpace

open Classical in
/-- The orbit feature `Γ_{r,·}(x) = ((t ↦ D U(r,max{t,r}) φ_j(x))_j, (D φ_j(x))_j) ∈ 𝒦`
(`W:r2:orbit-feature` S lines 3330-3334; `W:r2:nonautonomous-feature` S lines 3892-3893), for a
spatial derivative evaluation `D` (`∂_a` for the gradient components; "any one fixed derivative
`D^α`", S lines 3379-3382) and the generator coefficients `C` (`U(r,t) = propagatorW C r t`,
`L_t = generatorW C t`).  Its `H¹` part is represented by `(A₀, A') = (Dφ(x), 1_{t>r} D U(r,t) L_t φ(x))`. -/
def orbitFeature (C : WholeCoeff d) (m T : ℝ) (Dop : (Euc d → ℝ) → Euc d → ℝ) (r : ℝ) (x : Euc d) :
    KSpace d m T :=
  let base : OscDual d m := ellVec m fun α => Dop (oscTestFun m α) x
  let f : ℝ → OscDual d m := fun t => if r < t then
    ellVec m fun α => Dop (propagatorW C r t (generatorW C t (oscTestFun m α))) x else 0
  KSpace.mk base (if h : MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) T)) then h.toLp f else 0) base

/-- The `a`-th gradient component `∂_a`. -/
def gradComp (a : Fin d) (g : Euc d → ℝ) (x : Euc d) : ℝ := gradient g x a

/-- The gradient feature `Γ_{r,a}(x)`. -/
def gradFeature (C : WholeCoeff d) (m T : ℝ) (a : Fin d) (r : ℝ) (x : Euc d) : KSpace d m T :=
  orbitFeature C m T (gradComp a) r x

/-- The bilinear form `(u,v) ↦ 2q ∑_a ∫ ⟨Γ_{r,a}(x),u⟩⟨Γ_{r,a}(x),v⟩ dν(x)`, the covariance
`C_r` of `W:r2:orbit-maximal` (S lines 3366-3368). -/
def featureForm (m T q : ℝ) {n : ℕ} (Γ : Fin n → Euc d → KSpace d m T) (ν : Measure (Euc d))
    (u v : KSpace d m T) : ℝ :=
  2 * q * ∑ a, ∫ x, inner ℝ (Γ a x) u * inner ℝ (Γ a x) v ∂ν

/-- The reconstruction `(𝒯M)(t) = A_T(t) - B_T + B_t` (`W:r2:reconstruct`, S line 3374) of a
`𝒦`-valued process `M = (A, B)`. -/
def reconstructPath {Ω : Type*} (m T : ℝ) (M : ℝ → Ω → KSpace d m T) (ζ : Ω) (t : ℝ) :
    OscDual d m :=
  (M T ζ).evalA t - (M T ζ).B + (M t ζ).B

/-- The conclusions of Lemma S5.2 for a feature family `Γ_a(r,x)`, `a < n`, with constants
`Ctr, Cmax`:
(i) for every `q ≥ 0`, `r ∈ [0,T]` and finite positive measure `ν`, the form
`C_r = 2q ∑_a ∫ Γ_a⊗Γ_a dν` is a bounded bilinear form which is positive trace class, with trace
at most `Ctr q ν(ℝ^d)`;
(ii) every continuous `𝒦`-martingale `M` with covariation density `Σ_r` (`Σ_r` positive trace class,
integrable; in particular `Σ_r = C_r`, and the covariation of a difference of two such martingales)
determines the continuous `B_m`-valued path `𝒯M` and `E‖𝒯M‖²_{C_tB_m} ≤ Cmax E∫_0^T Tr Σ_r dr`. -/
def OrbitMaximalConclusion (m T : ℝ) {n : ℕ} (Γ : Fin n → ℝ → Euc d → KSpace d m T)
    (Ctr Cmax : ℝ) : Prop :=
  (∀ q : ℝ, 0 ≤ q → ∀ r ∈ Set.Icc 0 T, ∀ ν : Measure (Euc d), IsFiniteMeasure ν →
    ∃ B : KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ,
      (∀ u v, B u v = featureForm m T q (fun a => Γ a r) ν u v) ∧ IsTraceClassCov B ∧
      traceNormForm B ≤ Ctr * q * (ν Set.univ).toReal) ∧
  (∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℝ mΩ) (M : ℝ → Ω → KSpace d m T)
      (Sg : ℝ → Ω → (KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ)),
    IsHilbertMartingaleWithCovariation P ℱ T M Sg →
      (∀ᵐ ζ ∂P, Continuous fun t : Set.Icc (0 : ℝ) T => reconstructPath m T M ζ t) ∧
      ∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) T, ENNReal.ofReal ‖reconstructPath m T M ζ t‖) ^ 2 ∂P ≤
        ENNReal.ofReal (Cmax * ∫ ζ, (∫ r in Set.Icc (0 : ℝ) T, traceNormForm (Sg r ζ)) ∂P))

/-! ### S5.1 consequence: bounded features (`W:r2:feature-derivatives`) -/

/-- Display `W:r2:feature-derivatives` (S:W:r2:orbit-maximal, TeX S L3340-3345; the input of Lemma S5.2, not
a labelled row): under the hypotheses of Lemma S5.1
(second part) and `k > d/2 + 6`, `J = 2k + 2d + 20`, `m > J + 3d + 4`, the feature
`Γ_{r,a}(x) ∈ 𝒦` is `C^{k-1}` in `x` and
`sup_{r∈[0,T],x} ‖D_x^b Γ_{r,a}(x)‖_𝒦 ≤ C_{T,b}` for `b ≤ k - 1`.  The adjoint is the classical
adjoint solution along the time-independent coefficients
`ν Δ + (-Qx + c)·∇ + div g*(ρ∇)` (`M = -1`, `c = -∇g*ρ + σ`, `σ` Schwartz).  This display is not a
labelled row; it is the input of S5.2.  Technical hypotheses: `T ≥ 0`, `ν > 0` (as in S5.1). -/
theorem orbit_feature_bounded (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (k : ℕ)
    (hk : (d : ℝ) / 2 + 6 < k) (m : ℝ) (hm : ((2 * k + 2 * d + 20 : ℕ) : ℝ) + 3 * d + 4 < m)
    (T ν : ℝ) (Q : Matrix (Fin d) (Fin d) ℝ) (ρ : Euc d → ℝ) (c : Euc d → Euc d)
    (hT : 0 ≤ T) (hν : 0 < ν) (hρ : IsSchwartzDensity ρ)
    (hc : ∃ σ : Euc d → Euc d, (∀ i, ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = fun x => σ x i) ∧
      c = fun x => σ x - convGradConvW (rieszKernelGrad d s) ρ x) :
    ∀ b : ℕ, b + 1 ≤ k → ∃ Cb : ℝ, ∀ a : Fin d, ∀ r ∈ Set.Icc 0 T,
      ContDiff ℝ ((k - 1 : ℕ) : WithTop ℕ∞) (fun x => gradFeature (fixedViscosityCoeff s (-1) Q ν c ρ) m T a r x) ∧
      ∀ x : Euc d, ‖iteratedFDeriv ℝ b
        (fun y => gradFeature (fixedViscosityCoeff s (-1) Q ν c ρ) m T a r y) x‖ ≤ Cb := by
  sorry

/-! ### S5.2 -/

/-- Lemma S5.2 (S:W:r2:orbit-maximal, TeX S L3363-3390): intrinsic construction and maximal
estimate.  For a feature family bounded in `𝒦` (`‖Γ_{r,a}(x)‖ ≤ B`, the bound
`W:r2:feature-derivatives` supplied by S5.1, see `orbit_feature_bounded`), there are `C_T` (depending
on `T, d, B`) such that `OrbitMaximalConclusion` holds for the gradient features: `C_r` is positive
trace class with trace at most `C_T q ν_r(ℝ^d)` (for every finite positive `ν_r`, a fortiori a
predictable measure-valued process), and every continuous `𝒦`-martingale `M = (A,B)` with
covariation `Σ_r` determines the continuous path `𝒯M(t) = A_T(t) - B_T + B_t` with
`E‖𝒯M‖²_{C_tB_m} ≤ C_T E ∫_0^T Tr Σ_r dr`.  The maximal estimate is stated for an arbitrary
covariation density `Σ_r` (this covers `Σ_r = C_r`, a difference martingale and its covariance, and
a covariance restricted to a measurable time set).  The feature family is any family of derivative
evaluations `D` (`Dop`) with the same bound: `∂_a` (gradient components) and `D^α` ("any one fixed
derivative `D^α` for which the corresponding orbit bounds hold").  The identification clause "for the
empirical noise this is exactly its adjoint stochastic convolution" is `orbit_maximal_identification`;
the clause "for deterministic `ν_r` it is the corresponding Gaussian convolution" is not stated
(it needs the cylindrical Brownian motion on `L²([0,T]×ℝ^d;ℝ^d)` and the Gaussian stochastic
convolution, absent from the library).  Statement repair `Supplement repair P4` (docs/ISSUES.md): the features are
assumed measurable in `x` (`hmeas`; the TeX features are continuous), without it clause (i) is false by Bochner junk. -/
theorem orbit_maximal (C : WholeCoeff d) (m T : ℝ) (hT : 0 ≤ T) {n : ℕ}
    (Dop : Fin n → (Euc d → ℝ) → Euc d → ℝ) (B : ℝ)
    (hB : ∀ a : Fin n, ∀ r ∈ Set.Icc 0 T, ∀ x : Euc d, ‖orbitFeature C m T (Dop a) r x‖ ≤ B)
    (hmeas : ∀ a : Fin n, ∀ r ∈ Set.Icc 0 T,
      Measurable (fun x : Euc d => orbitFeature C m T (Dop a) r x)) :
    ∃ Ctr Cmax : ℝ, OrbitMaximalConclusion m T
      (fun (a : Fin n) (r : ℝ) (x : Euc d) => orbitFeature C m T (Dop a) r x) Ctr Cmax := by
  sorry

/-- The integrand `√(2q/N) Γ_{r,a}(x_i^r)`, indexed by `(i,a)`, of the empirical noise
`M_t = √(2q/N) ∑_{i,a} ∫_0^t Γ_{r,a}(x_i^r) dB_i^a(r)` (S lines 3398-3399). -/
def empiricalNoiseIntegrand {Ω : Type*} {N : ℕ} (C : WholeCoeff d) (m T q : ℝ)
    (X : ℝ≥0 → Ω → EucConfig d N) : ℝ → Ω → Fin N × Fin d → KSpace d m T :=
  fun r ζ ia => Real.sqrt (2 * q / N) • gradFeature C m T ia.2 r (X (Real.toNNReal r) ζ ia.1)

/-- The orbit feature `Γ_{r,a}(x)` of `orbitFeature` is genuinely an element of `𝒦_T` (no junk `0` from `ellVec` / `toLp`):
the coordinates of `Dop φ_α(x)` are in `ℓ²`, those of `Dop U(r,t) ℒ_t φ_α(x)` are in `ℓ²` for `r < t ≤ T`, and
`t ↦ (…)_α` is in `L²([0,T];ℓ²)`.  (Same predicate as `IsKFeature` in `CriticalNoise.lean`, which imports this file.) -/
def IsOrbitFeatureK (C : WholeCoeff d) (m T : ℝ) (Dop : (Euc d → ℝ) → Euc d → ℝ) (r : ℝ) (x : Euc d) :
    Prop :=
  Memℓp (fun α : MultiIndex d => Dop (oscTestFun m α) x) 2 ∧
  (∀ t ∈ Set.Ioc r T, Memℓp (fun α : MultiIndex d =>
    Dop (propagatorW C r t (generatorW C t (oscTestFun m α))) x) 2) ∧
  MemLp (fun t : ℝ => if r < t then ellVec (d := d) m (fun α => Dop
    (propagatorW C r t (generatorW C t (oscTestFun m α))) x) else 0) 2
    (volume.restrict (Set.Icc (0 : ℝ) T))

/-- Inputs of Lemma S5.2 on the coefficients `C` (S L3398-3410): the Duhamel identity for the gradient of the
adjoint propagator of the oscillator test functions, `∂_aU^{r,t}φ_α - ∂_aφ_α = ∫_r^t ∂_aU^{r,s}ℒ_sφ_α ds` for
`0 ≤ r ≤ t ≤ T` (with integrable right side; at `r = t` it also forces `propagatorW C t t φ_α` to be the true
adjoint solution, not the junk value `0`), and the absence of junk values in the orbit features. -/
structure OscAdjointInput (C : WholeCoeff d) (m T : ℝ) : Prop where
  duhamel : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ∀ (α : MultiIndex d) (a : Fin d) (x : Euc d),
    IntegrableOn (fun s => gradComp a (propagatorW C r s (generatorW C s (oscTestFun m α))) x)
      (Set.Icc r t) ∧
    gradComp a (propagatorW C r t (oscTestFun m α)) x - gradComp a (oscTestFun m α) x =
      ∫ s in Set.Icc r t, gradComp a (propagatorW C r s (generatorW C s (oscTestFun m α))) x
  feature : ∀ (a : Fin d), ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x : Euc d, IsOrbitFeatureK C m T (gradComp a) r x

/-- Lemma S5.2 (S:W:r2:orbit-maximal, TeX S L3363-3390), identification clause (S L3377-3379, proof
L3398-3410): if `M = (A,B)` is the `𝒦`-valued Itô integral (`IsHilbertItoIntegral`, the Hilbert
Itô layer of CLT-02, with a cylindrical Brownian motion `W = (B_i^a)` indexed by
`(i,a) ∈ [N]×[d]`) of the empirical-noise integrand, then for every `t ∈ [0,T]` and every Hermite
coordinate `α` the `α`-th coordinate of `(𝒯M)(t) = A_T(t) - B_T + B_t` is almost surely the adjoint
stochastic convolution `√(2q/N) ∑_{i,a} ∫_0^t ∂_a U(r,t)φ_α(x_i^r) dB_i^a(r)` (real Itô integral
`HRS.itoIntegral` with the `t`-dependent integrand, truncated to `r ∈ [0,t]`: the adjoint propagator is not determined
for `r > t`, and the Itô integral depends on the integrand for all `r` through its existence).  Statement repair `MH-REPAIRS-4`
(docs/ISSUES.md, 2026-10-19): truncation of the integrand and the hypothesis `hC : OscAdjointInput C m T` (Duhamel identity
for the gradient of the propagator and no junk values of the orbit features, which in the paper requires `m` large).
Technical hypotheses: `N ≥ 1`; the integrand is a progressive Hilbert-Schmidt integrand (`IsHSIntegrand`).
Repair S5.2 (2026-10-23, approved): `hB`, a uniform bound of the base orbit-feature vector
`a ↦ (∂_aφ_α(x))_α` in the `ℓ²`-type space `𝒦` (`ellVec`).  Without it the statement cannot be proved: `hΦ` controls the integrand
only on `[0,T]`, while `IsHilbertItoIntegral` (through `itoIntegral`, which is a `Classical.choose` when the Itô integral
exists and `0` otherwise) involves all horizons, so for an integrand that is not square integrable beyond `T` the hypothesis
`hM` is satisfied by an `M` with vanishing coordinates.  `hB` lifts `hΦ` to every horizon; it follows from the `b = 0` case of the
orbit-feature bound `orbit_feature_bounded` (S L3356, used at L3392 of the TeX proof). -/
theorem orbit_maximal_identification (C : WholeCoeff d) (m T q : ℝ) (N : ℕ)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → Fin N × Fin d → ℝ) (X : ℝ≥0 → Ω → EucConfig d N)
    (M : ℝ → Ω → KSpace d m T) (hN : 1 ≤ N) (hW : IsCylindricalBrownian P ℱ W)
    (hΦ : IsHSIntegrand P ℱ T (empiricalNoiseIntegrand C m T q X))
    (hM : IsHilbertItoIntegral P ℱ W (empiricalNoiseIntegrand C m T q X) M)
    (hC : OscAdjointInput C m T)
    (hB : ∃ B : ℝ, ∀ (a : Fin d) (x : Euc d),
      ‖ellVec (d := d) m (fun α => gradComp a (oscTestFun m α) x)‖ ≤ B) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ α : MultiIndex d, ∀ᵐ ζ ∂P,
      OscDual.coord (reconstructPath m T M ζ t) α =
        itoIntegral P ℱ W (fun r ζ' ia => if r ∈ Set.Icc (0 : ℝ) t then Real.sqrt (2 * q / N) *
          gradComp ia.2 (propagatorW C r t (oscTestFun m α)) (X (Real.toNNReal r) ζ' ia.1) else 0) t ζ := by
  sorry

/-! ### Weighted spaces `E_{r,P}`, `F_{r,P}` (S lines 3745-3760) -/

/-- The norm of `E_{r,P} = {f : ⟨x⟩^{-P} f ∈ H^r}` in its equivalent form
`(∑_{|α|≤r} ∫⟨x⟩^{-2P}|D^αf|²)^{1/2}` (S lines 3758-3760: "the norm in `E_{r,P}` is equivalent to the
square root of `∑_{|α|≤r}∫⟨x⟩^{-2P}|D^αf|²`"), in `ℝ≥0∞`; the sum runs over ordered index tuples
(an equivalent norm). -/
def weightedSobolevE (r : ℕ) (P : ℝ) (f : Euc d → ℝ) : ℝ≥0∞ :=
  (∑ j ∈ Finset.range (r + 1), ∑ i : Fin j → Fin d,
    ∫⁻ x, ENNReal.ofReal (jbracket x ^ (-2 * P) * (partialDeriv i f x) ^ 2)) ^ (1 / 2 : ℝ)

/-- The initial-field space `F_0 = (H^ℓ(⟨x⟩^{-d-3}dx))'` (S lines 4088-4090) is `F_{ℓ,P}` with
`2P = d+3`.  The norm of a functional `η` (given by its values on functions) in `F_{r,P}`:
`sup {|η f| / ‖f‖_{E_{r,P}} : f ∈ C_c^∞, 0 < ‖f‖_{E_{r,P}} < ∞}`.  The sup is over the test functions
`C_c^∞` of which `E_{r,P}` is the completion (S L7707-7708); a sup over all functions of finite
`weightedSobolevE` would admit non-differentiable `f` (junk derivatives `0` in `partialDeriv`), e.g. `1_{x_i} + εg`, and
make every empirical field have norm `⊤` (audit repair). -/
def dualNormE (r : ℕ) (P : ℝ) (η : (Euc d → ℝ) → ℝ) : ℝ≥0∞ :=
  ⨆ (f : Euc d → ℝ) (_ : ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      0 < weightedSobolevE r P f ∧ weightedSobolevE r P f < ⊤),
    ENNReal.ofReal |η f| / weightedSobolevE r P f

/-- The linear flow `Φ_t` of the affine drift `-Qx`: `Φ_0 = id`, `d/dt Φ_t(x) = -QΦ_t(x)`. -/
def IsLinearFlow (Q : Matrix (Fin d) (Fin d) ℝ) (Φ : ℝ → Euc d → Euc d) : Prop :=
  (∀ x, Φ 0 x = x) ∧ ∀ x t, HasDerivAt (fun t' => Φ t' x) (-(Torus.matVec Q (Φ t x))) t

/-- Lemma S5.4 (S:W:r2:weighted-higher-order, TeX S L3769-3790), analytic part: `d ≥ 2`,
`0 ≤ s < d/2` (Hilbert-Schmidt range), `P > d/2`, `r` an integer; the evolution of Lemma S5.1
(`IsUlBackwardEvolution`, the operator `νΔ + (-Qx + c)·∇ + div g*(ρ∇)` of S5.1) satisfies:
(a) for every sufficiently large `k ≥ k₀` (the output `k₀`, S5.1 "for every sufficiently large integer `k`";
supplement repair P5; `k₀` depends on `d, s, θ` only) it is bounded on each `E_{r,P}`, uniformly on `[0,T]`: `U_t f ∈ C^r` and `‖U_t f‖_{E_{r,P}} ≤ C‖f‖_{E_{r,P}}` for
`f ∈ C_c^∞` (the dense core; the evolution is extended by density);
(b) after conjugation by the affine flow its generator maps `E_{r+2,P}` boundedly to `E_{r,P}`:
`‖(𝓛_0 (g∘Φ_t^{-1}))∘Φ_t‖_{E_{r,P}} ≤ C‖g‖_{E_{r+2,P}}`, `t ∈ [0,T]`, `g ∈ C_c^∞`, where
`𝓛_0 = 𝓛 - (-Qx·∇)` is the generator without the affine drift;
(c) the evaluation functional `f ↦ D^αf(x)` has norm at most `C⟨x⟩^P` in `F_{r,P}` when
`r > d/2 + |α|`: `|D^αf(x)| ≤ C⟨x⟩^P‖f‖_{E_{r,P}}`.
NOT STATED: the sentence "the maximal estimate therefore applies in these spaces whenever the
corresponding `2P` particle moment is finite" (S L3777-3778): it would need the maximal estimate of
S5.2 in the spaces `F_{r,P}` (no Banach-space model of `F_{r,P}` exists in the library).
NOT STATED (blocked): the final tightness/identification claim of the lemma (tightness in
`C([0,T];F_{r+2,P})` of fluctuation fields under `L^p(F_{r,P+2})` and `L^p(F_{r+2,P})` moment bounds,
and identification of the limit as the Gaussian linearized process): it needs a Banach-space model
of `F_{r,P}`, the canonical empirical equations on `ℝ^d`, and the weighted Gaussian process, none of
which exist in the library. -/
theorem weighted_higher_order (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) / 2)
    (θ : Euc d → ℝ) (hθ : IsUlCutoff θ) :
    ∃ k₀ : ℕ, ∀ (r : ℕ) (P : ℝ), (d : ℝ) / 2 < P →
    ∀ (T ν : ℝ) (Q M : Matrix (Fin d) (Fin d) ℝ) (ρ : Euc d → ℝ) (c : Euc d → Euc d), 0 ≤ T →
    0 < ν → IsSchwartzDensity ρ → IsSmoothBounded c →
    let Cf := fixedViscosityCoeff s M Q ν c ρ
    (∃ C : ℝ, ∀ k : ℕ, k₀ ≤ k → ∀ t ∈ Set.Icc 0 T, ∀ f : Euc d → ℝ, ContDiff ℝ ∞ f →
        HasCompactSupport f → ∀ u, IsUlBackwardEvolution θ k Cf t f u → ∀ r' ∈ Set.Icc 0 t,
          ContDiff ℝ r (u r') ∧
          weightedSobolevE r P (u r') ≤ ENNReal.ofReal C * weightedSobolevE r P f) ∧
    (∃ C : ℝ, ∀ Φ : ℝ → Euc d → Euc d, IsLinearFlow Q Φ → ∀ t ∈ Set.Icc 0 T,
        ∀ g : Euc d → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
          weightedSobolevE r P (fun x => generatorW ⟨s, M, ν, fun _ y => c y, fun _ => ρ⟩ 0
              (fun y => g (Φ (-t) y)) (Φ t x)) ≤
            ENNReal.ofReal C * weightedSobolevE (r + 2) P g) ∧
    (∀ α : ℕ, (d : ℝ) / 2 + α < r → ∃ C : ℝ, ∀ (i : Fin α → Fin d) (x : Euc d) (f : Euc d → ℝ),
        ContDiff ℝ ∞ f → ENNReal.ofReal |partialDeriv i f x| ≤
          ENNReal.ofReal (C * jbracket x ^ P) * weightedSobolevE r P f) := by
  sorry

/-! ### The Section S5 standing hypotheses -/

/-- The bounds on which the constants of S5.5-S5.7 may depend (S lines 3828-3852, 3939-3957):
the finite interval `[0,T]`, `V(x) = xᵀQx/2 + c·x`, the interaction matrix `M`, the kernel exponent
`s`, `k`, the oscillator index `m`, `ν_*`, the weighted-density bound `Λ` with exponent `L`, the
adjoint constant `K`, the heat-kernel completion constant `C₀`, and the uniformly local cutoff. -/
structure WholeBounds (d : ℕ) where
  θ : Euc d → ℝ
  s : ℝ
  T : ℝ
  M : Matrix (Fin d) (Fin d) ℝ
  Q : Matrix (Fin d) (Fin d) ℝ
  c : Euc d
  k : ℕ
  m : ℝ
  νstar : ℝ
  Λ : ℝ
  K : ℝ
  L : ℝ
  C₀ : ℝ

namespace WholeBounds

/-- `J = 4k + 4d + 40` (S line 3851). -/
def J (b : WholeBounds d) : ℕ := 4 * b.k + 4 * d + 40

/-- The standing constraints of Section S5: `d ≥ 2`, `0 ≤ s < d`, `T > 0`, `Q = Qᵀ`, the cutoff,
`k > d/2 + 8`, `m > J + 3d + 4`, `L > 3d + 3k + 2s + 30`, `ν_* ≥ 0`. -/
structure Valid (b : WholeBounds d) : Prop where
  hd : 2 ≤ d
  hs0 : 0 ≤ b.s
  hsd : b.s < d
  hT : 0 < b.T
  hQ : b.Q.IsSymm
  hθ : IsUlCutoff b.θ
  hk : (d : ℝ) / 2 + 8 < b.k
  hm : (b.J : ℝ) + 3 * d + 4 < b.m
  hL : 3 * (d : ℝ) + 3 * b.k + 2 * b.s + 30 < b.L
  hν : 0 ≤ b.νstar

end WholeBounds

/-- The coefficient and adjoint hypotheses of Section S5 (S lines 3828-3852), uniformly in `N`,
for a family of mean-field trajectories `ρ_N` at inverse temperatures `β_N`
(`invβ N = β_N⁻¹ ∈ [0,ν_*]`, `0` for `β_N = ∞`) and initial scales `κ_N > 0`:
the mean-field solutions of the dynamics with `V = xᵀQx/2 + c·x` and matrix `M`; the weighted
Schwartz bounds (derivatives of `ρ_N^t` through order `k + 6 + ⌈d/2⌉` bounded by `C⟨x⟩^{-L}`);
the whole-space uniformly local adjoint input through order `k+1` in `C_b` with constant `K`
(`UlAdjointInput`, standing for "the coefficient and adjoint hypotheses of `thm:adjoint-rd` or
`thm:adjoint-lp`(ii),(iii) with `p=2`, in one of their explicitly verified matrix regimes,
uniformly in `N`"); the regime fields `regime` (per `N`, one of the explicitly verified matrix regimes: `R1`/`R2a`/`R2c`/`R3` of
`thm:adjoint-rd` (`RdRegimeHolds`), or a case of `thm:adjoint-lp` at `p = 2` (`LpCase.Holds`)) and `force` (the
singular-force proviso `‖|∇|^{s-d}∇ρ_N^t‖_∞ ≤ Λ` when `d-1 ≤ s`, as in `IsRegularMFRd`), added 2026-10-22 after review
(F-CAU-regime) so that uniqueness of classical adjoint solutions applies; and the heat-kernel completion `energy_nonneg`
(`𝓔_N^t = F_N(X_N,ρ_N^t) + o_N ≥ 0` off collisions, S lines 3913-3915 `E_{N,p}`; the completion
constant of `H:eq:energy-completion`). -/
structure WholeSetup (b : WholeBounds d) where
  invβ : ℕ → ℝ
  ρ : ℕ → ℝ → Euc d → ℝ
  κ : ℕ → ℝ
  hinvβ : ∀ N, 0 ≤ invβ N ∧ invβ N ≤ b.νstar
  hκ : ∀ N, 0 < κ N
  mf : ∀ N, IsWholeMeanFieldSolution (⟨b.s, b.M, quadV b.Q b.c, invβ N⟩ : WholeDyn d) b.T (ρ N)
  dens : ∀ N, ∀ t ∈ Set.Icc 0 b.T, ContDiff ℝ (b.k + 6 + ⌈(d : ℝ) / 2⌉₊) (ρ N t) ∧
    weightedSupE (b.k + 6 + ⌈(d : ℝ) / 2⌉₊) b.L (ρ N t) ≤ ENNReal.ofReal b.Λ
  adjoint : ∀ N, UlAdjointInput b.θ
    ((⟨b.s, b.M, quadV b.Q b.c, invβ N⟩ : WholeDyn d).coeff (ρ N)) b.T (b.k + 1) b.K
  regime : ∀ N, (∃ (Rg : PDE.Regime) (ν₀ : ℝ),
      HRS.Whole.AppendixA.RdRegimeHolds Rg d b.s b.M (invβ N) ν₀) ∨
    (∃ c : HRS.Whole.AppendixA.LpCase, HRS.Whole.AppendixA.LpCase.Holds d b.s 2 b.M c)
  force : (d : ℝ) - 1 ≤ b.s → ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) b.T, ∀ x,
    ‖HRS.Whole.AppendixA.fracForceRd d b.s (ρ N t) x‖ ≤ b.Λ
  energy_nonneg : ∀ N : ℕ, 2 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) b.T, ∀ X : EucConfig d N,
    X ∉ eucCollisionSet d N →
      0 ≤ rieszModulatedEnergy d b.s X (withDensityReal (ρ N t)) + oN d b.s b.C₀ N

namespace WholeSetup

variable {b : WholeBounds d} (S : WholeSetup b)

/-- The dynamics data at particle number `N` (matrix `M`, `V = xᵀQx/2 + c·x`, `ν = β_N⁻¹`). -/
def dyn (N : ℕ) : WholeDyn d := ⟨b.s, b.M, quadV b.Q b.c, S.invβ N⟩

/-- The coefficients of the linear equation at `N`. -/
def coeff (N : ℕ) : WholeCoeff d := (S.dyn N).coeff (S.ρ N)

/-- `σ_N = min{κ_N, √(Nβ_N)}` (`(σ_N,a_N,q_N) = (κ_N, 1, 0)` at `β_N = ∞`). -/
def σ (N : ℕ) : ℝ := sigmaScale N (S.κ N) (S.invβ N)

/-- `a_N = σ_N/κ_N`. -/
def A (N : ℕ) : ℝ := Ascale N (S.κ N) (S.invβ N)

/-- `q_N = σ_N²/(Nβ_N)`. -/
def q (N : ℕ) : ℝ := qScale N (S.κ N) (S.invβ N)

/-- `E_{N,p} = sup_{t≤T} ‖F_N(X_N^t, ρ_N^t) + o_N‖_{L^p}` (S lines 3912-3915), in `ℝ≥0∞`. -/
def energyMomentE {Ω : Type*} [MeasurableSpace Ω] (N : ℕ) (p : ℝ) (P : Measure Ω)
    (X : ℝ≥0 → Ω → EucConfig d N) : ℝ≥0∞ :=
  ⨆ t : Set.Icc (0 : ℝ) b.T,
    (∫⁻ ζ, ENNReal.ofReal |rieszModulatedEnergy d b.s (X (Real.toNNReal t) ζ)
        (withDensityReal (S.ρ N t)) + oN d b.s b.C₀ N| ^ p ∂P) ^ (1 / p)

/-- `ε_{N,p} = ‖((κ_N(μ_N^0 - ρ_N^0) - η_N^0)(U_N(0,t)φ_j))_j‖_{L^p(C_tℓ²)}`
(`W:r2:general-initial-error`, S lines 3926-3930), in `ℝ≥0∞`; `η₀` is the prescribed random initial
field, a random functional on test functions. -/
def initialErrorE {Ω : Type*} [MeasurableSpace Ω] (N : ℕ) (p : ℝ) (P : Measure Ω)
    (X₀ : Ω → EucConfig d N) (η₀ : Ω → (Euc d → ℝ) → ℝ) : ℝ≥0∞ :=
  (∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) b.T, l2NormE fun α : MultiIndex d =>
      S.κ N * (pair (empirical (X₀ ζ)) (propagatorW (S.coeff N) 0 t (oscTestFun b.m α)) -
        pair (withDensityReal (S.ρ N 0)) (propagatorW (S.coeff N) 0 t (oscTestFun b.m α))) -
        η₀ ζ (propagatorW (S.coeff N) 0 t (oscTestFun b.m α))) ^ p ∂P) ^ (1 / p)

end WholeSetup

/-! ### S5.5 -/

/-- Lemma S5.5 (S:W:r2:general-orbits, TeX S L3884-3905), feature bounds, for a setup `S` of Section S5
(`WholeSetup`, with the standing constraints `WholeBounds.Valid`): the nonautonomous feature
`Γ^N_{r,a}(x)` of `W:r2:nonautonomous-feature` is `C^k` in `x` and bounded in `𝒦` together with its
spatial derivatives through order `k`, uniformly in `N, r, x`; the reconstruction and maximal
estimate of S5.2 hold for it with the same uniformity (`OrbitMaximalConclusion` with constants
independent of `N`); and for every canonical collision-free (pairwise distinct) configuration
`|Comm_N(Mᵀ∇U_N(r,t)φ_j; X_N, ρ_N^r)| ≤ C_T b_j(F_N(X_N,ρ_N^r) + o_N)`, `b_j = λ_j^{(J-m)/2}`
(the weighted Hermite bound; `φ_α = λ_α^{-m/2}h_α`), `0 ≤ r ≤ t ≤ T`, `N ≥ 2`.  The hypotheses
`2(s+1) > d`-type branch distinctions of the proof (S lines 3896-3905: sub-Coulomb via S4.12/S4.14,
Coulomb and super-Coulomb via the globally Lipschitz commutator) are not separate hypotheses: they
are folded into the adjoint input of `WholeSetup` and the constant.  "All the original logarithmic
moment assumptions are retained": the weighted density bounds imply them. -/
theorem general_orbits_features (b : WholeBounds d) (hb : b.Valid) :
    ∃ C : ℝ, ∀ S : WholeSetup b, ∀ (N : ℕ) (a : Fin d), ∀ r ∈ Set.Icc 0 b.T,
      ContDiff ℝ b.k (fun x => gradFeature (S.coeff N) b.m b.T a r x) ∧
      ∀ j : ℕ, j ≤ b.k → ∀ x : Euc d, ‖iteratedFDeriv ℝ j
        (fun y => gradFeature (S.coeff N) b.m b.T a r y) x‖ ≤ C := by
  sorry

/-- Lemma S5.5 (S:W:r2:general-orbits, TeX S L3884-3905), reconstruction and maximal estimate for the nonautonomous features
(S lines 3897-3899: "the reconstruction and maximal estimate of Lemma S5.2 hold with this feature,
with the same uniformity"). -/
theorem general_orbits_maximal (b : WholeBounds d) (hb : b.Valid) :
    ∃ Ctr Cmax : ℝ, ∀ S : WholeSetup b, ∀ N : ℕ, OrbitMaximalConclusion b.m b.T
      (fun (a : Fin d) (r : ℝ) (x : Euc d) => gradFeature (S.coeff N) b.m b.T a r x) Ctr Cmax := by
  sorry

/-- Lemma S5.5 (S:W:r2:general-orbits, TeX S L3884-3905), commutator bound
`W:r2:general-commutator-orbit` (L3898-3905).  Statement repair `Supplement repair P6` (docs/ISSUES.md): the heat-kernel
completion constant `C₀` is chosen large (`C₀min ≤ b.C₀`, all other bounds equal to those of `b₀`), the constant `C` may
depend on `b.C₀`. -/
theorem general_orbits_commutator (b₀ : WholeBounds d) (hb : b₀.Valid) :
    ∃ C₀min : ℝ, ∀ b : WholeBounds d, b = { b₀ with C₀ := b.C₀ } → C₀min ≤ b.C₀ →
    ∃ C : ℝ, ∀ S : WholeSetup b, ∀ (N : ℕ), 2 ≤ N → ∀ X : EucConfig d N, Function.Injective X →
      ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ b.T → ∀ α : MultiIndex d,
        |commN d b.s (fun x => Torus.matVec b.M.transpose
            (gradient (propagatorW (S.coeff N) r t (oscTestFun b.m α)) x))
          X (withDensityReal (S.ρ N r))| ≤
        C * oscEigenvalue d α ^ (((b.J : ℝ) - b.m) / 2) *
          (rieszModulatedEnergy d b.s X (withDensityReal (S.ρ N r)) + oN d b.s b.C₀ N) := by
  sorry

/-! ### S5.7 -/

/-- The coefficients `(ρ, c, ν)` of S5.7: `νΔ + (-Qx + c_t(x))·∇ - Div g*(ρ_t Mᵀ∇ ·)`. -/
def fixedEqCoeff (s : ℝ) (M Q : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) (c : ℝ → Euc d → Euc d)
    (ρ : ℝ → Euc d → ℝ) : WholeCoeff d :=
  ⟨s, M, ν, fun t x => -(Torus.matVec Q x) + c t x, ρ⟩

/-- `η` is linear on the functions of finite `E_{r,P}` norm (`F_0 = (E_{k,(d+3)/2})'`: the
prescribed initial field is a continuous *linear* functional on the weighted Sobolev space; it
is bounded iff `dualNormE r P η < ⊤`).  Superseded in `fixed_equation` by `IsBoundedLinearOnE` (this predicate alone admits
functionals vanishing on `C_c^∞` with `dualNormE = 0`); kept for `HRS/MS/FixEqAux1.lean`. -/
def IsLinearOnE (r : ℕ) (P : ℝ) (η : (Euc d → ℝ) → ℝ) : Prop :=
  ∀ f g : Euc d → ℝ, weightedSobolevE r P f < ⊤ → weightedSobolevE r P g < ⊤ → ∀ c : ℝ,
    η (f + g) = η f + η g ∧ η (c • f) = c * η f

/-- `η` is a bounded linear functional on the test functions of `E_{r,P}` (S5.7 repair R1, ED3; `F_0 = (E_{k,(d+3)/2})'`,
S L4088-4095): additive and homogeneous on the `C^r` functions of finite `E_{r,P}` norm, and bounded,
`|η f| ≤ B ‖f‖_{E_{r,P}}` for every such `f` (the class `IsR2WeightedTest` of `Window.lean`; the bound is NOT restricted to
`C_c^∞`).  Because `C_c^∞` is dense in this class for the `E_{r,P}` norm (cutoff `χ(x/n)f` and mollification), the bound gives
`|η f| ≤ dualNormE r P η * ‖f‖_{E_{r,P}}` on the whole class, so `dualNormE` (a supremum over `C_c^∞` only) does see `η` on the
non-compactly supported functions `U^{0,t}φ_α` to which `fixed_equation` applies it.  The previous hypothesis `IsLinearOnE`
(no bound; kept above for `HRS/MS/FixEqAux1.lean`) is satisfied by a functional that vanishes on `C_c^∞` and is `1` on a
Gaussian (`s57_wild_functional_dualNormE`); such a functional is not bounded. -/
def IsBoundedLinearOnE (r : ℕ) (P : ℝ) (η : (Euc d → ℝ) → ℝ) : Prop :=
  (∀ f g : Euc d → ℝ, ContDiff ℝ r f → weightedSobolevE r P f < ⊤ →
      ContDiff ℝ r g → weightedSobolevE r P g < ⊤ → ∀ c : ℝ,
    η (f + g) = η f + η g ∧ η (c • f) = c * η f) ∧
  ∃ B : ℝ, ∀ f : Euc d → ℝ, ContDiff ℝ r f → weightedSobolevE r P f < ⊤ →
    |η f| ≤ B * (weightedSobolevE r P f).toReal

/-- The F-CAU data hypotheses of `fixed_equation` for one family of coefficients `(ν, c, ρ)` (S5.7 repair R2, ED3), so that
classical adjoint solutions of `fixedEqCoeff b.s b.M b.Q ν c ρ` are unique on `[0,T]` (`Fcau.propagatorW_unique_star`,
`HRS/MS/StarTie.lean`) and `propagatorW` is the classical solution.  `regime` and `force` are the fields of `WholeSetup` of the same
names (with `ν` for `invβ N`); the other fields of the F-CAU hypotheses are implied by the hypotheses already in `fixed_equation`
(`MatBound`: automatic; `VHypRd` for `V = xᵀQx/2`: `b.Valid.hQ`; `IsProbDensity`, `MemCb`, `cbNorm` and `weightedSupE`
parts of `CoeffHypRd`: from the density bounds at level `k + 6 + ⌈d/2⌉ + 4`, with `b.L ≥ d + 3`) except the two time-continuity
fields: `rho_cont` (the field `cont` of `CoeffHypRd`: weak continuity of `t ↦ ρ_t` on `[0,T]`, which `WholeSetup` has from
`IsWholeMeanFieldSolution`) and `drift_cont` (joint continuity of the transport coefficient on `[0,T] × ℝ^d`, the field `cont`
of `IsAdvectingDrift`; for `WholeSetup` it follows from the mean-field drift) and `uniq_data` (the case split of `HRS/MS/UniqFTie.lean`: `ν > 0`, or
the mean-field tie `c_t = M∇g*ρ_t - c₀`; it is what makes the uniqueness lemma `uniqf_unique_fe` applicable). -/
structure FixedEqFcauHyp (b : WholeBounds d) (ν : ℝ) (c : ℝ → Euc d → Euc d)
    (ρ : ℝ → Euc d → ℝ) : Prop where
  regime : (∃ (Rg : PDE.Regime) (ν₀ : ℝ),
      HRS.Whole.AppendixA.RdRegimeHolds Rg d b.s b.M ν ν₀) ∨
    (∃ cs : HRS.Whole.AppendixA.LpCase, HRS.Whole.AppendixA.LpCase.Holds d b.s 2 b.M cs)
  force : (d : ℝ) - 1 ≤ b.s → ∀ t ∈ Set.Icc (0 : ℝ) b.T, ∀ x,
    ‖HRS.Whole.AppendixA.fracForceRd d b.s (ρ t) x‖ ≤ b.Λ
  rho_cont : ∀ ψ : Euc d → ℝ, Continuous ψ → (∃ B : ℝ, ∀ x, |ψ x| ≤ B) →
    ContinuousOn (fun r => ∫ x, ψ x * ρ r x) (Set.Icc (0 : ℝ) b.T)
  drift_cont : ContinuousOn (fun p : ℝ × Euc d => c p.1 p.2) (Set.Icc (0 : ℝ) b.T ×ˢ Set.univ)
  /-- Repair S5.7 (uniqueness coverage, approved 2026-10-23, review UNIQF): uniqueness of classical adjoint solutions
  is available for `ν > 0` with a free bounded transport coefficient, and for `ν = 0` only when `c` is the mean-field
  drift `c_t = M ∇g*ρ_t - c₀` of the `WholeSetup` coefficients (`HRS/MS/UniqFTie.lean`). -/
  uniq_data : 0 < ν ∨ ∃ c₀ : Euc d, ∀ t ∈ Set.Icc (0 : ℝ) b.T, ∀ x, c t x =
    Torus.matVec b.M (convGradConvW (rieszKernelGrad d b.s) (ρ t) x) - c₀

/-- `‖v‖_{C_b^K}` of a vector field, in `ℝ≥0∞` (`∑_{j≤K} sup_x ‖D^jv(x)‖`). -/
def cbNormVecE (K : ℕ) (v : Euc d → Euc d) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (K + 1), ⨆ x : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ j v x‖

/-- Proposition S5.7 (S:W:r2:fixed-equation, TeX S L4078-4106): the additional cost of a fixed
limiting equation.  In the setting of S5.6 let `(ρ_N, c_N, ν_N)` and `(ρ, c, ν)` satisfy the same
uniform adjoint branch (`UlAdjointInput` with constant `K_ad`, for both families, through order `k+1` and, in the repair
below, also through order `k + 4 + ⌈d/2⌉`), with a common affine transport `-Qx` and matrix `M`; the transport coefficients `c_N, c` are bounded
and the weighted density bounds hold through `k + 6 + ⌈d/2⌉ + 4` derivatives (four further levels),
exponent `b.L`; `K > k + 6 + ⌈d/2⌉ + 4` is an integer larger than all those levels, `L' > 3d + 3K + 2s + 30`,
used only in `Δ_N` (which may be `⊤`), with `ℓ = k` fixed before `K`.  The hypotheses on `ρ_N, ρ, c_N, c`
are imposed only through the levels `k + 6 + ⌈d/2⌉ + 4` demanded by the TeX (not through `K`).  Put
`Δ_N = |ν_N - ν| + sup_t ‖c_N^t - c^t‖_{C_b^K} + max_{|α|≤K} sup_{t,x} ⟨x⟩^L |D^α(ρ_N^t - ρ^t)|`
and `τ_N = sup_t ‖ρ_N^t - ρ^t‖_{L¹}`.  For every prescribed initial field `η⁰` (a random functional)
on a probability space (`η⁰` measurable, almost surely linear and bounded on `E_{k,(d+3)/2}`,
with finite `p`-th moment in `F_0`, S L4093-4095) there is a coupling
`(Ω × Ω₂, P ⊗ P₂)` (independent noises) of `Y_N` (initial factor `a_N`, noise factor `q_N`,
coefficients `(ρ_N,c_N,ν_N)`) and `Y` (initial factor `a`, noise factor `q`, coefficients
`(ρ,c,ν)`), both with the *same* initial field `η⁰` (a random functional on `ℝ^d`, `η⁰ ∘ fst`),
such that
`‖Y_N - Y‖_{L^p(C_tB_m)} ≤ C_T[(|a_N - a| + |a|Δ_N)‖η⁰‖_{L^p(F_0)} + |√q_N - √q| + √q(Δ_N + √τ_N)]`
(`W:r2:fixed-equation-cost`).  `C_T` depends on the bounds only (quantified before everything
else).  Technical hypotheses: `0 ≤ a_N, a, q_N, q` (scale factors); `T > 0`.

Statement repairs R1-R3 (ED3, approved 2026-10-23, `docs/S57_PLAN.md`, including the fields `rho_cont`, `drift_cont` of `FixedEqFcauHyp` (P1) and the extra `⌈d/2⌉` levels of the density, drift and `K` hypotheses (P2), approved the same day after review E4; the unrepaired statement was false, a linear functional
vanishing on `C_c^∞` and equal to `1` on a Gaussian has `dualNormE = 0`): (R1) `η⁰` is a *bounded* linear functional on the `C^k`
functions of finite `E_{k,(d+3)/2}` norm (`IsBoundedLinearOnE`, S L4093-4095); (R2) the F-CAU data hypotheses `FixedEqFcauHyp`
(regime, singular-force proviso, weak continuity of `ρ`, continuity of the transport coefficient, and the uniqueness case `uniq_data` (`ν > 0`, or `c_t = M∇g*ρ_t - c₀`, so at `ν = 0` only mean-field transport; repair approved 2026-10-23, review E5)) for both families, so that
classical adjoint solutions are unique and `propagatorW` is the classical solution in the Duhamel identity
`(U_N-U)(r,t)ψ = ∫_r^t U_N(r,u)(L_N^u-L^u)U(u,t)ψ du` of the TeX proof (S L4094-4106); (R3) `UlAdjointInput` also at order
`k + 4 + ⌈d/2⌉` for both families: the identity is applied to `ψ = L_N^tφ_α` (the terminal-time derivative of the features) and the
`C_b^{k+1}` norm of `(U_N-U)ψ` needs `(L_N-L)Uψ ∈ H_ul^{k+2+⌈d/2⌉}`, i.e. `Uψ ∈ C_b^{k+4+⌈d/2⌉}` (the diffusion difference costs two
derivatives); the order `k+1` hypotheses are kept (they bound `U_N` on the data `(L_N-L)Uψ`, which is only `C^{k+2+⌈d/2⌉+}`). -/
theorem fixed_equation (b : WholeBounds d) (hb : b.Valid) (K : ℕ)
    (hK : b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊ < K) (L' : ℝ) (hL' : 3 * (d : ℝ) + 3 * K + 2 * b.s + 30 < L')
    (p : ℝ) (hp : p = 1 ∨ p = 2) :
    ∃ C : ℝ, ∀ (νN ν : ℝ) (cN c : ℝ → Euc d → Euc d) (ρN ρ : ℝ → Euc d → ℝ) (aN a qN q : ℝ),
      0 ≤ aN → 0 ≤ a → 0 ≤ qN → 0 ≤ q → 0 ≤ νN → νN ≤ b.νstar → 0 ≤ ν → ν ≤ b.νstar →
      UlAdjointInput b.θ (fixedEqCoeff b.s b.M b.Q νN cN ρN) b.T (b.k + 1) b.K →
      UlAdjointInput b.θ (fixedEqCoeff b.s b.M b.Q ν c ρ) b.T (b.k + 1) b.K →
      UlAdjointInput b.θ (fixedEqCoeff b.s b.M b.Q νN cN ρN) b.T (b.k + 4 + ⌈(d : ℝ) / 2⌉₊) b.K →
      UlAdjointInput b.θ (fixedEqCoeff b.s b.M b.Q ν c ρ) b.T (b.k + 4 + ⌈(d : ℝ) / 2⌉₊) b.K →
      FixedEqFcauHyp b νN cN ρN → FixedEqFcauHyp b ν c ρ →
      (∀ t ∈ Set.Icc 0 b.T, IsProbDensity (ρN t) ∧ IsProbDensity (ρ t) ∧
        ContDiff ℝ (b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) (ρN t) ∧
        ContDiff ℝ (b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) (ρ t) ∧
        weightedSupE (b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) b.L (ρN t) ≤ ENNReal.ofReal b.Λ ∧
        weightedSupE (b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) b.L (ρ t) ≤ ENNReal.ofReal b.Λ) →
      (∀ t ∈ Set.Icc 0 b.T, ContDiff ℝ (b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) (cN t) ∧
        ContDiff ℝ (b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) (c t) ∧
        cbNormVecE (b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) (cN t) ≤ ENNReal.ofReal b.Λ ∧
        cbNormVecE (b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) (c t) ≤ ENNReal.ofReal b.Λ) →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (η₀ : Ω → (Euc d → ℝ) → ℝ), Measurable η₀ →
        (∀ᵐ ζ ∂P, IsBoundedLinearOnE b.k ((d + 3 : ℝ) / 2) (η₀ ζ)) →
        (∫⁻ ζ, dualNormE b.k ((d + 3 : ℝ) / 2) (η₀ ζ) ^ p ∂P < ⊤) →
      ∃ (Ω₂ : Type) (_ : MeasurableSpace Ω₂) (P₂ : Measure Ω₂) (h₂ : IsProbabilityMeasure P₂)
        (YN Y : ℝ → Ω × Ω₂ → OscDual d b.m),
        haveI := h₂
        IsLinearFluctuationSolutionW (P.prod P₂) (fixedEqCoeff b.s b.M b.Q νN cN ρN) b.m qN b.T
          (fun ζ f => aN * η₀ ζ.1 f) YN ∧
        IsLinearFluctuationSolutionW (P.prod P₂) (fixedEqCoeff b.s b.M b.Q ν c ρ) b.m q b.T
          (fun ζ f => a * η₀ ζ.1 f) Y ∧
        (∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) b.T, ENNReal.ofReal ‖YN t ζ - Y t ζ‖) ^ p ∂(P.prod P₂)) ^
            (1 / p) ≤
          ENNReal.ofReal C *
            ((ENNReal.ofReal |aN - a| + ENNReal.ofReal |a| *
                (ENNReal.ofReal |νN - ν| +
                  (⨆ t : Set.Icc (0 : ℝ) b.T, cbNormVecE K (fun x => cN t x - c t x)) +
                  (⨆ t : Set.Icc (0 : ℝ) b.T, weightedSupE K L' (fun x => ρN t x - ρ t x)))) *
              ((∫⁻ ζ, dualNormE b.k ((d + 3 : ℝ) / 2) (η₀ ζ) ^ p ∂P) ^ (1 / p)) +
              ENNReal.ofReal |Real.sqrt qN - Real.sqrt q| +
              ENNReal.ofReal (Real.sqrt q) *
                ((ENNReal.ofReal |νN - ν| +
                    (⨆ t : Set.Icc (0 : ℝ) b.T, cbNormVecE K (fun x => cN t x - c t x)) +
                    (⨆ t : Set.Icc (0 : ℝ) b.T, weightedSupE K L' (fun x => ρN t x - ρ t x))) +
                  (⨆ t : Set.Icc (0 : ℝ) b.T,
                    ∫⁻ x, ENNReal.ofReal |ρN t x - ρ t x|) ^ (1 / 2 : ℝ))) := by
  sorry

end HRS.Whole
