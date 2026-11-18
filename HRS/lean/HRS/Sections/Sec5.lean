import HRS.Sections.Sec3
import HRS.Sections.Sec4
import HRS.Equilibrium.StaticLimits
import HRS.Dynamics.InitialData
import HRS.Stochastic.SelectedFlow
import HRS.Sections.Q41Aux4
import HRS.Sections.Q41Aux21

/-!
# HRS.Sections.Sec5 — Section 5 (evolving fluctuations and thermalization): statement drafts

Statement drafts (all proofs are `sorry`) for the rows

* `M:N:thm:dynamic` (Proposition 5.4, TeX M L6075-6107);
* `M:P:lem:moving-moments` (Lemma 5.8, M L6641-6657);
* `M:P:prop:iid` (Proposition 5.9, M L6781-6803);
* `M:A:prop:UI` (Proposition 5.10, M L7035-7047);
* `M:O:prop:relative` (Proposition 5.13, M L7159-7171);
* `M:C:prop:criterion` (Proposition 5.14, M L7191-7211);
* `M:E:cor:mean-threshold` (Corollary 5.16, M L7441-7456);
* `M:E:cor:mean-particles` (Corollary 5.17, M L7466-7485);
* `M:U:prop:unbounded` (Proposition 5.18, M L7506-7514).

(`M:E:prop:mean`, Proposition 5.15, is covered by the existing `HRS.PDE.nonlinear_transient`.)

## Representation decisions (to be recorded in `docs/ISSUES.md`)

* **The smooth positive trajectory** (M L738-745, "the smooth positive trajectory above", L6076) is
  `IsSmoothPositiveTrajectory`: gradient dynamics `M = -I`, `β > 0`, smooth `V`, a smooth strictly
  positive probability density `ρ⁰`, and `ρ` the global solution in `C([0,∞);H^K)` of `O:eq:mf-finite`
  (`PDE.IsMFSolutionHK`, Proposition 5.1) for every `K > d/2+6`.  Smoothness, positivity and the
  uniform derivative bounds quoted in M L740-744 are then theorems of Proposition 5.1, not
  hypotheses.  The dynamics datum is `traj.dyn = PDE.mfData`.
* **Particle systems.**  `IsParticleSystem P D T X₀ W X`: `X` is the collision-free strong solution
  on `[0,T]` (`IsStrongSolution`), `W` a vector Brownian motion (`IsVectorBrownian`) and the initial
  configuration `X₀` is independent of `W`.  The law `f_N^t` is `P.map (X t)`; `f_N^∘ = P.map X₀`.
  Statements whose proofs use Itô calculus for the particles (`dynamic_entropy`, `dynamic_comparison`,
  `ui_comparison`, `ui_qualitative`, `criterion_comparison`, `criterion_stationary`) also assume a filtered strong
  solution (`IsFilteredSolution`: `X` adapted to a Brownian filtration carrying `W`), the strong-solution
  adaptedness of A.1 (M L10131) that `IsStrongSolution` (measurability only, ISSUES D1) does not record
  (repairs 2026-10-16, ISSUES §I "5.14" and the entry after it).
  Relative entropies are Mathlib's `klDiv` (`relEntropy`, ISSUES E1), values in `ℝ≥0∞`.
* **Constants**: "constants independent of `N`" is `∃ C, ∀ N ≥ 2, ∀ systems`.  A constant that the
  TeX allows to depend on fixed data (`T`, the tests, `p₀`, `r`, ...) is chosen after that datum and
  before `N`; no dependence on the initial law of the particle system is allowed unless the TeX
  displays it (it enters only through `B_N`, `J_N`, `r_N`).
* **Observations.**  `⟨φ, η_N^t⟩ = linCoord (μ^t) φ (X_N^t) = √N(μ_N^t(φ) - μ^t(φ))`;
  `⟨φ, ζ_N^t⟩ = √N(μ_N^t(φ) - m_N^t(φ))` with `m_N^t = meanEmpirical (P.map X_N^t)`.
* **Random limits.**  Gaussian vectors `G` are given with their law
  (`multivariateGaussian 0 Σ`, `noiseCovMatrix`) and independence from the initial configuration;
  convergence in law uses Mathlib's `TendstoInDistribution` along sequences of systems indexed by
  `n ↦ N = n+2` (`ParticleSeq`).
* **Expectations of possibly infinite quantities** (`E[sup ‖·‖²]`, `r_N`, `Θ(L)`) are `ℝ≥0∞`-valued
  (`lintegral`, `⨆`, `tsum` of `ofReal`).
* **Nonnegative observation times** `u_n ≥ 0` are carried explicitly where `Real.toNNReal` is applied.

## Ambiguities recorded in the docstrings
* Prop 5.10 (`ui_comparison`, `ui_qualitative`): the base estimate for `L²` initial densities is not a
  displayed theorem (the printed `H:thm:equilibrium` is stationary); the finite-dimensional clauses
  `A:eq:UI-error` are stated, the path-space qualitative clauses are not.
* Prop 5.14 (`criterion_comparison`): the hypothesis "`(N:eq:entropy)` holds" is read as the global-in-time
  bound (`P:eq:entropy-input`, M L6577-6580) with an arbitrary constant `C₁` on which `C` may depend.
* Prop 5.18 (`unbounded_stationary_sup`): `‖η̄^t‖_{H^{-m}} < ∞` a.s. is automatic for an `E_m`-valued
  process; it is encoded as existence of the `E_m`-valued continuous stationary process.
* Prop 5.4: the constants may depend on the tests (the TeX says "independent of `N` and of the terminal
  times"), not on the initial law; `H:eq:meanfield` has no `V` in Prop 5.15, `V = 0` as in M L872.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS

variable {d : ℕ}

/-! ### Common data -/

/-- The smooth positive trajectory of M L738-745 (`H:subsec:nonequilibrium`): `ρ` is the global
solution (Proposition 5.1, `O:eq:mf-finite`) in `C([0,∞);H^K)`, for every `K > d/2+6`, of the
mean-field equation `H:eq:meanfield` with `M = -I`, inverse temperature `β > 0`, smooth `V` and a
smooth positive probability density `ρ⁰` (only `t ≥ 0` is constrained). -/
structure IsSmoothPositiveTrajectory (d : ℕ) (s β : ℝ) (V ρ₀ : Torus d → ℝ)
    (ρ : ℝ → Torus d → ℝ) : Prop where
  hs0 : 0 ≤ s
  hsd : s < d
  hβ : 0 < β
  V_smooth : Torus.IsSmooth V
  init : SmoothPosDensity ρ₀
  global : ∀ K : ℕ, (d : ℝ) / 2 + 6 < K →
    ∃ ρc : ℝ → (Lattice d → ℂ), PDE.IsMFSolutionHK d s V β⁻¹ K ρ₀ ρc ∧
      ∀ t, 0 ≤ t → PDE.mfPath ρc t = ρ t

/-- The dynamics data `M = -I`, `β⁻¹` of the trajectory (`PDE.mfData`). -/
def IsSmoothPositiveTrajectory.dyn {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (h : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) : DynData d :=
  PDE.mfData d s h.hs0 h.hsd V β h.hβ

/-- The particle system data: `X` is a collision-free strong solution on `[0,T]` of the particle
system `D` driven by the vector Brownian motion `W`, with initial configuration `X₀` independent of
`W` (`H:eq:intro-particles`, M L170-178). -/
structure IsParticleSystem {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D : DynData d) (T : ℝ)
    {N : ℕ} (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
    (X : ℝ≥0 → Ω → Config d N) : Prop where
  brownian : IsVectorBrownian P W
  indep : ProbabilityTheory.IndepFun X₀ (fun ω => fun t : ℝ≥0 => W t ω) P
  sol : IsStrongSolution P D T X₀ W X

/-- A sequence of particle systems, indexed by `n` with `N = n + 2` particles, on varying
probability spaces (for statements about convergence in law). -/
structure ParticleSeq (d : ℕ) where
  Ω : ℕ → Type
  mΩ : ∀ n, MeasurableSpace (Ω n)
  P : ∀ n, Measure (Ω n)
  prob : ∀ n, IsProbabilityMeasure (P n)
  X₀ : ∀ n, Ω n → Config d (n + 2)
  W : ∀ n, ℝ≥0 → Ω n → (Fin (n + 2) → Euc d)
  X : ∀ n, ℝ≥0 → Ω n → Config d (n + 2)

attribute [instance] ParticleSeq.mΩ ParticleSeq.prob

/-- Every term of the sequence is a particle system on `[0,T]` for the dynamics `D`. -/
def ParticleSeq.IsSolutionOn (S : ParticleSeq d) (D : DynData d) (T : ℝ) : Prop :=
  ∀ n, IsParticleSystem (S.P n) D T (S.X₀ n) (S.W n) (S.X n)

/-- `B_N = 1 + H(f_N^∘ | Q_N^0) + N δ_N` (`N:eq:B`, `H:eq:entropy-bound`, M L6082, L772); meaningful
under finiteness of the relative entropy (`relEntropy ≠ ⊤`). -/
def entropyScale (d : ℕ) (s : ℝ) (N : ℕ) (f Q : Measure (Config d N)) : ℝ :=
  1 + (relEntropy f Q).toReal + N * deltaN d s N

/-- The noise covariance matrix `Σ_{ab} = 2q ∫_0^{t_a∧t_b} ∫ ∇U^{r,t_a}φ_a·∇U^{r,t_b}φ_b dμ^r dr`
(`N:eq:noise-cov`, M L6070-6071, and `C:eq:G-covariance`, M L7203-7204, with `2q = 2/β`); the same
matrix as in `IsLinearFluctuationSolution`. -/
def noiseCovMatrix (D : DynData d) (ρ : ℝ → Torus d → ℝ) (q : ℝ) {p : ℕ} (t : Fin p → ℝ)
    (φ : Fin p → Torus d → ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun a b => 2 * q * ∫ r in Set.Icc 0 (min (t a) (t b)), ∫ x,
    inner ℝ (Torus.grad (propagator D ρ r (t a) (φ a)) x)
      (Torus.grad (propagator D ρ r (t b) (φ b)) x) * ρ r x

/-! ### Proposition 5.4 -/

/-- Proposition 5.4 (`M:N:thm:dynamic`, TeX M L6075-6107), first assertion `N:eq:entropy`: for all
`N ≥ 2`, `sup_{0≤t≤T}(H(f_N^t | Q_N^t) + H(f_N^t | (μ^t)^{⊗N})) ≤ C_T B_N`, where
`Q_N^t = ℚ_{N,β}(μ^t)` is the modulated Gibbs law at the physical inverse temperature and
`f_N^t` the law of `X_N^t`.  The constant depends on the trajectory, `T`, `d`, `s`, `β`, `V`
(M L6558: "uniform over the smooth positive trajectory") and not on `N` or on the initial law.
Standing assumptions: `2 ≤ d` (M L417), `0 ≤ s < d` (in the trajectory), `H(f_N^∘ | Q_N^0) < ∞`
(M L6078). -/
theorem dynamic_entropy (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsParticleSystem P htr.dyn T X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
          IsFilteredSolution P ℱ W' W X) →
        relEntropy (P.map X₀)
          (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) ≠ ⊤ →
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          relEntropy (P.map (X t.toNNReal))
              (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ t))) +
            relEntropy (P.map (X t.toNNReal)) (Measure.pi fun _ => withDensityReal (ρ t)) ≤
          ENNReal.ofReal (C * entropyScale d s N (P.map X₀)
            (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0)))) := by
  sorry

/-- Proposition 5.4, second assertion `N:eq:dynamic-bound` (M L6086-6091): for every fixed finite
family of smooth terminal tests `φ_a` there is `C_T` (independent of `N`, of the terminal times
`t_a ∈ [0,T]` and of the initial law) such that, for every Gaussian vector `G` independent of the
initial configuration with the covariance `N:eq:noise-cov` (`noiseCovMatrix` with `q = β⁻¹`),
`d_{C²}((⟨φ_a, η_N^{t_a}⟩)_a, (⟨f_a^0, η_N^∘⟩)_a + G) ≤ C_T (B_N/√N + √(B_N/N))`,
`f_a^r = U^{r,t_a}φ_a` (`propagator`). -/
theorem dynamic_comparison (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (T : ℝ) (hT : 0 ≤ T) (p : ℕ)
    (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, Torus.IsSmooth (φ a)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsParticleSystem P htr.dyn T X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
          IsFilteredSolution P ℱ W' W X) →
        relEntropy (P.map X₀)
          (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) ≠ ⊤ →
        ∀ t : Fin p → ℝ, (∀ a, t a ∈ Set.Icc (0 : ℝ) T) →
        ∀ G : Ω → EuclideanSpace ℝ (Fin p),
          law P G = ProbabilityTheory.multivariateGaussian 0 (noiseCovMatrix htr.dyn ρ β⁻¹ t φ) →
          AEMeasurable G P →
          ProbabilityTheory.IndepFun X₀ G P →
          smoothDist 2
              (law P fun ω => (WithLp.toLp 2 fun a =>
                linCoord (withDensityReal (ρ (t a))) (φ a) (X (t a).toNNReal ω) :
                  EuclideanSpace ℝ (Fin p)))
              (law P fun ω => (WithLp.toLp 2 fun a =>
                linCoord (withDensityReal (ρ 0)) (propagator htr.dyn ρ 0 (t a) (φ a)) (X₀ ω) + G ω a :
                  EuclideanSpace ℝ (Fin p))) ≤
            C * (entropyScale d s N (P.map X₀)
                  (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) / Real.sqrt N +
                Real.sqrt (entropyScale d s N (P.map X₀)
                  (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) / N)) := by
  sorry

private lemma q35_tendsto_natpow {e : ℝ} (he : e < 0) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ e) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (neg_pos.2 he)).comp tendsto_natCast_atTop_atTop
  simpa [Function.comp_def] using h

private lemma q35_tendsto_log_mul :
    Tendsto (fun N : ℕ => (1 + Real.log N) * (N : ℝ) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
  have h1 := q35_tendsto_natpow (e := -(1 / 2 : ℝ)) (by norm_num)
  have h2 : Tendsto (fun N : ℕ => Real.log N / (N : ℝ) ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
    ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero).comp
      tendsto_natCast_atTop_atTop
  have h3 := h1.add h2
  rw [zero_add] at h3
  refine h3.congr fun N => ?_
  rw [Real.rpow_neg (Nat.cast_nonneg N)]
  ring

/-- case `s = d/2`: `√N δ_N = (1 + log N) N^{-1/2}` for `N ≥ 1`. -/
private lemma q35_sqrt_delta_mid {d : ℕ} {s : ℝ} (h : s = (d : ℝ) / 2) :
    ∀ᶠ N : ℕ in atTop, Real.sqrt N * deltaN d s N = (1 + Real.log N) * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  have hδ : deltaN d s N = (N : ℝ) ^ (-1 : ℝ) * (1 + Real.log N) := by
    unfold deltaN
    rw [if_neg (not_lt.2 h.ge), if_pos h, Real.rpow_neg_one,
      Real.log_mul (Real.exp_pos 1).ne' hN0.ne', Real.log_exp]
  have hpow : (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (-1 : ℝ) = (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_add hN0]; norm_num
  rw [hδ, Real.sqrt_eq_rpow]
  linear_combination (1 + Real.log N) * hpow


/-- `√N δ_N → 0` for `0 ≤ s < 2d/3`. -/
private lemma q35_sqrt_delta_tendsto {d : ℕ} (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s < 2 * (d : ℝ) / 3) :
    Tendsto (fun N : ℕ => Real.sqrt N * deltaN d s N) atTop (𝓝 0) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  rcases lt_trichotomy s ((d : ℝ) / 2) with h | h | h
  · refine (q35_tendsto_natpow (e := -(1 / 2 : ℝ)) (by norm_num)).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
    unfold deltaN
    rw [if_pos h, Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_add hN0]
    norm_num
  · exact q35_tendsto_log_mul.congr' ((q35_sqrt_delta_mid h).mono fun N hN => hN.symm)
  · have hspos : 0 < s := by linarith
    have h32 : 3 / 2 < (d : ℝ) / s := (lt_div_iff₀ hspos).2 (by linarith)
    refine (q35_tendsto_natpow (e := 1 / 2 + (1 - (d : ℝ) / s)) (by linarith)).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
    unfold deltaN
    rw [if_neg (not_lt.2 h.le), if_neg (ne_of_gt h), Real.sqrt_eq_rpow, ← Real.rpow_add hN0]


/-- Proposition 5.4, "In particular" sentence (M L6092-6094): if `H(f_N^∘ | Q_N^0) = o(√N)` and
`s < 2d/3`, the right side `B_N/√N + √(B_N/N)` of `N:eq:dynamic-bound` tends to zero.
(`h N = H(f_N^∘ | Q_N^0) ≥ 0`.) -/
theorem dynamic_bound_vanishes (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < 2 * (d : ℝ) / 3)
    (h : ℕ → ℝ) (hh0 : ∀ N, 0 ≤ h N) (ho : Tendsto (fun N : ℕ => h N / Real.sqrt N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (1 + h N + N * deltaN d s N) / Real.sqrt N +
      Real.sqrt ((1 + h N + N * deltaN d s N) / N)) atTop (𝓝 0) := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hP2 := q35_sqrt_delta_tendsto hd1 hs0 hs
  have ha : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) :=
    q35_tendsto_natpow (by norm_num)
  have t1 : Tendsto (fun N : ℕ => (1 + h N + N * deltaN d s N) / Real.sqrt N) atTop (𝓝 0) := by
    have hsum := (ha.add ho).add hP2
    rw [add_zero, add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
    have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
    have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
    rw [Real.rpow_neg hN0.le, ← Real.sqrt_eq_rpow]
    generalize Real.sqrt N = t at *
    rw [← hsq]
    field_simp
  have t2 : Tendsto (fun N : ℕ => (1 + h N + N * deltaN d s N) / N) atTop (𝓝 0) := by
    have hm := t1.mul ha
    rw [zero_mul] at hm
    refine hm.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
    have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
    have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
    rw [Real.rpow_neg hN0.le, ← Real.sqrt_eq_rpow]
    generalize Real.sqrt N = t at *
    rw [← hsq]
    field_simp
  have t3 : Tendsto (fun N : ℕ => Real.sqrt ((1 + h N + N * deltaN d s N) / N)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp t2
    rw [Real.sqrt_zero] at this
    exact this
  have hfin := t1.add t3
  rw [add_zero] at hfin
  exact hfin

/-- Proposition 5.4, last paragraph (M L6096-6106): suppose `B_N/√N → 0`.  If, in addition,
`η_N^∘ = √N(μ_N^0 - μ^0)` converges in law in `H^{-m}(𝕋^d)` for some `m > d+4`, then the fluctuation
trajectories `η_N^{·}` converge in law in `C([0,T];H^{-m})` to the solution `Y` of the linearized
stochastic equation `N:eq:linear-spde` (`IsLinearFluctuationSolution` with `q = β⁻¹`) with that
initial law, the Gaussian part being independent of the initial value (built into the predicate;
"independently of the driving vector white noise").  Here `η°` is a random element of `E_m` on a
probability space `(Ω', P')` (the limiting initial field, with the law of the limit) and `Y` any
solution on that space with `Y⁰ = η°`.  Sequences of particle systems are indexed by `n ↦ N = n+2`.

Statement repair (ISSUES.md, entry "Statement sweep repairs (ADAPTSPEC3)"): the last paragraph of Proposition 5.4 (M L6096-6106) is proved from the entropy/duality estimates of its first two assertions (Itô calculus), so each `S.X n` is assumed a filtered strong solution (`hSF`, `IsFilteredSolution`, the shape of `ui_qualitative`). -/
theorem dynamic_convergence (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (T : ℝ) (hT : 0 ≤ T) (S : ParticleSeq d)
    (hS : S.IsSolutionOn htr.dyn T)
    (hSF : ∀ n, ∃ (ℱ : MeasureTheory.Filtration ℝ (S.mΩ n))
      (W' : ℝ≥0 → S.Ω n → (Fin (n + 2) × Fin d) → ℝ),
      IsFilteredSolution (S.P n) ℱ W' (S.W n) (S.X n))
    (hfin : ∀ n, relEntropy ((S.P n).map (S.X₀ n))
      (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ 0))) ≠ ⊤)
    (hB : Tendsto (fun n : ℕ => entropyScale d s (n + 2) ((S.P n).map (S.X₀ n))
        (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ 0))) /
          Real.sqrt ((n + 2 : ℕ) : ℝ)) atTop (𝓝 0))
    (m : ℝ) (hm : (d : ℝ) + 4 < m)
    (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (η₀ : Ω' → NegSobolev d m)
    (hlaw : MeasureTheory.TendstoInDistribution
      (fun n ω => etaE m (S.X₀ n ω) (withDensityReal (ρ 0))) atTop η₀ S.P P')
    (Y : ℝ → Ω' → NegSobolev d m)
    (hY : IsLinearFluctuationSolution P' htr.dyn ρ m β⁻¹ T η₀ Y) :
    MeasureTheory.TendstoInDistribution
      (fun n ω => flucPath m T (Real.sqrt ((n + 2 : ℕ) : ℝ)) (S.X n) ρ ω) atTop
      (toPath m T Y) S.P P' := by
  sorry

/-! ### Lemma 5.8 (moments under the moving law) -/

/-- `J_N = 1 + N δ_N + log ‖h_N^0‖_{L^{p₀}(Q_N^0)}` (`H:eq:strong-bound`, M L785-787), `h_N^0 = df_N^0/dQ_N^0`;
meaningful under `f ≪ Q` and `‖h_N^0‖_{L^{p₀}(Q)} < ∞`. -/
def logMomentScale (d : ℕ) (s : ℝ) (N : ℕ) (p₀ : ℝ) (f Q : Measure (Config d N)) : ℝ :=
  1 + N * deltaN d s N + Real.log (eLpNorm (f.rnDeriv Q) (ENNReal.ofReal p₀) Q).toReal

/-- The `k`-th real coordinate `⟨e_k, ∫_0^t 𝒱^{t,r} 𝓡_N^r dr⟩ = ∫_0^t 𝓡_N^r(U^{r,t} e_k) dr` of the
integrated remainder of `P:eq:noneq-mild` (M L6573-6575), with `𝓡_N^r(φ) = -√N F_N^{h_{∇φ}}(X_N^r, μ^r)`
and `𝒱^{t,r}` the transpose of the propagator `U^{r,t}`. -/
def evolvingForcingCoord {Ω : Type*} {N : ℕ} (D : DynData d) (ρ : ℝ → Torus d → ℝ)
    (X : ℝ≥0 → Ω → Config d N) (k : NonzeroLattice d) (t : ℝ) (ω : Ω) : ℝ :=
  ∫ r in (0 : ℝ)..t,
    -(Real.sqrt N * modulatedEnergy
      (commKernel (periodicRieszGrad d D.s) (Torus.grad (propagator D ρ r t (Torus.realMode k))))
      (X r.toNNReal ω) (withDensityReal (ρ r)))

/-- Lemma 5.8 (`M:P:lem:moving-moments`, TeX M L6641-6657), first assertion `P:eq:log-moment`: under
`h_N^0 = df_N^0/dQ_N^0 ∈ L^{p₀}(Q_N^0)` for a fixed `p₀ > 1` there is `p_∞ > 1` independent of `N`
with `sup_{t≥0} log ‖f_N^t/Q_N^t‖_{L^{p_∞}(Q_N^t)} ≤ C J_N` (stated as `‖·‖ ≤ exp(C J_N)`, with
`f_N^t ≪ Q_N^t` part of the conclusion).  `X` is a global particle system (`∀ T`).

Statement repair (ISSUES.md, entry "Statement sweep repairs (ADAPTSPEC3)"): the proof (TeX L6641-6700) differentiates the `L^{p(t)}` norm of the density along the flow (variable-exponent identity, entropy argument as in `dynamic_entropy`), which needs a Brownian filtration, so `X` is assumed a filtered strong solution (`∃ ℱ W', IsFilteredSolution P ℱ W' W X`, the shape of `dynamic_comparison`). -/
theorem moving_log_moment (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (p₀ : ℝ) (hp₀ : 1 < p₀) :
    ∃ pInf C : ℝ, 1 < pInf ∧ 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        (∀ T : ℝ, 0 ≤ T → IsParticleSystem P htr.dyn T X₀ W X) →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
          IsFilteredSolution P ℱ W' W X) →
        P.map X₀ ≪ modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0)) →
        eLpNorm ((P.map X₀).rnDeriv (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))))
          (ENNReal.ofReal p₀) (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) < ⊤ →
        ∀ t : ℝ, 0 ≤ t →
          P.map (X t.toNNReal) ≪ modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ t)) ∧
          eLpNorm ((P.map (X t.toNNReal)).rnDeriv
              (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ t))))
            (ENNReal.ofReal pInf) (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ t))) ≤
          ENNReal.ofReal (Real.exp (C * logMomentScale d s N p₀ (P.map X₀)
            (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))))) := by
  sorry

/-- Lemma 5.8, second assertion `P:eq:pair-moments` (M L6644-6646): for every fixed `r ≥ 1` and
every symmetric (measurable) pair kernel `h` with `|h| ≤ D w`, `w = g + c_*`,
`sup_{t≥0} ‖N F_N^h(X_N^t, μ^t)‖_{L^r} ≤ C_r D J_N`.  As in Proposition 5.5 the constant `c_*` is any
number with `w ≥ 1` off zero (the source fixes one such `c_*`, M L6110-6111, L6537) and the constant
`C_r` is chosen after `c_*`, `r`, `p₀` and before `D`, `h`, `N` and the system.  The bound `|h| ≤ D w`
is required only off the diagonal (`x ≠ y`): `periodicRiesz d s 0` is a junk value, and the diagonal is
null for every measure involved.  Technical hypothesis: `h` measurable (implicit in the integrals).

Statement repair (ISSUES.md, entry "Statement sweep repairs (ADAPTSPEC3)"): the proof uses `moving_log_moment` and the pressure estimates on the moving law, so `X` is assumed a filtered strong solution as in `moving_log_moment` (`∃ ℱ W', IsFilteredSolution P ℱ W' W X`). -/
theorem moving_pair_moments (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (p₀ : ℝ) (hp₀ : 1 < p₀) (cstar : ℝ)
    (hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + cstar) (r : ℝ) (hr : 1 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        (∀ T : ℝ, 0 ≤ T → IsParticleSystem P htr.dyn T X₀ W X) →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
          IsFilteredSolution P ℱ W' W X) →
        P.map X₀ ≪ modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0)) →
        eLpNorm ((P.map X₀).rnDeriv (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))))
          (ENNReal.ofReal p₀) (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) < ⊤ →
        ∀ (D : ℝ), 0 ≤ D → ∀ h : Torus d → Torus d → ℝ, Measurable (Function.uncurry h) →
          (∀ x y, h x y = h y x) →
          (∀ x y, x ≠ y → |h x y| ≤ D * (periodicRiesz d s (x - y) + cstar)) →
          ∀ t : ℝ, 0 ≤ t →
            eLpNorm (fun ω => (N : ℝ) * modulatedEnergy h (X t.toNNReal ω) (withDensityReal (ρ t)))
              (ENNReal.ofReal r) P ≤
            ENNReal.ofReal (C * D * logMomentScale d s N p₀ (P.map X₀)
              (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0)))) := by
  sorry

/-- Lemma 5.8, third assertion `P:eq:L2-integrated` (M L6647-6650): for `m > d/2 + 2` and `T`,
`sup_{a≥0} ‖∫_0^· 𝒱^{·,r}𝓡_N^r dr‖_{L²(C([a,a+T];E_m))} ≤ C_T J_N/√N`; the squared left side is
`E[sup_{a≤t≤a+T} ∑_k ⟨k⟩^{-2m} |∫_0^t 𝓡_N^r(U^{r,t}e_k) dr|²]` (`ℝ≥0∞`-valued `lintegral`,
`E_m`-norm through the orthonormal real modes).  Caveat on `∫⁻ ⨆_t`: to keep the integrand a countable supremum
(hence measurable, so the lintegral is a genuine expectation) the supremum is taken over rational `t ∈ [a,a+T]`;
this is the same quantity as the supremum over all `t ∈ [a,a+T]` by the continuity in `t` of the path in
`C([a,a+T];E_m)` (the source's norm, M L6647-6650), which the source asserts.  Conjunct: a.s. the time integrands are interval
integrable (well-definedness of the integrals).

Statement repair (ISSUES.md, entry "Statement sweep repairs (ADAPTSPEC3)"): the proof uses `moving_pair_moments` (hence `moving_log_moment`), so `X` is assumed a filtered strong solution as there (`∃ ℱ W', IsFilteredSolution P ℱ W' W X`). -/
theorem moving_integrated_forcing (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ}
    {ρ : ℝ → Torus d → ℝ} (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (p₀ : ℝ) (hp₀ : 1 < p₀)
    (m : ℝ) (hm : (d : ℝ) / 2 + 2 < m) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        (∀ T' : ℝ, 0 ≤ T' → IsParticleSystem P htr.dyn T' X₀ W X) →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
          IsFilteredSolution P ℱ W' W X) →
        P.map X₀ ≪ modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0)) →
        eLpNorm ((P.map X₀).rnDeriv (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))))
          (ENNReal.ofReal p₀) (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) < ⊤ →
        (∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ k : NonzeroLattice d,
          IntervalIntegrable (fun r =>
            Real.sqrt N * modulatedEnergy
              (commKernel (periodicRieszGrad d htr.dyn.s) (Torus.grad (propagator htr.dyn ρ r t (Torus.realMode k))))
              (X r.toNNReal ω) (withDensityReal (ρ r))) volume 0 t) ∧
        ∀ a : ℝ, 0 ≤ a →
          ∫⁻ ω, ⨆ t ∈ {t : ℝ | t ∈ Set.Icc a (a + T) ∧ ∃ q : ℚ, (q : ℝ) = t}, ∑' k : NonzeroLattice d,
              ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * m) *
                evolvingForcingCoord htr.dyn ρ X k t ω ^ 2) ∂P ≤
            ENNReal.ofReal ((C * logMomentScale d s N p₀ (P.map X₀)
              (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) / Real.sqrt N) ^ 2) := by
  sorry

/-! ### Proposition 5.9 (independent initial fields) -/

/-- `i_{N,m} = N^{-(m - d/2)/(2m)}` (`P:eq:iid-rates`, M L6788, and `H:eq:iid-errors`). -/
def iidRateSmooth (d : ℕ) (m : ℝ) (N : ℕ) : ℝ := (N : ℝ) ^ (-((m - (d : ℝ) / 2) / (2 * m)))

/-- `j_{N,m} = (log(eN)/√N)^{(m - d/2)/(m + d/2)}` (`P:eq:iid-rates`, M L6789-6790). -/
def iidRateW (d : ℕ) (m : ℝ) (N : ℕ) : ℝ :=
  (Real.log (Real.exp 1 * N) / Real.sqrt N) ^ (((m : ℝ) - (d : ℝ) / 2) / (m + (d : ℝ) / 2))

/-- Proposition 5.9 (`M:P:prop:iid`, TeX M L6781-6803), main assertion `P:eq:iid-comparison`: let
`0 < c ≤ ρ ≤ C̄`, `∫ρ = 1`, `m > d/2`, `S_N = η_N = N^{-1/2}∑(δ_{x_i} - ρ dx)` for independent samples of
`ρ dx` and `G_ρ` a centered Gaussian on `E_m` with the bridge covariance
`ρ(φψ) - ρ(φ)ρ(ψ)` (`iidCov`; `IsCenteredGaussianWithCov`).  Then in `E_m`
`d_2(S_N, G_ρ) ≤ C_m i_{N,m}`, `W_1(S_N, G_ρ) ≤ C_m j_{N,m}`, `W_2(S_N, G_ρ) ≤ C_m j_{N,m}^{1/3}`,
with `C_m` uniform under the displayed density bounds (chosen before `ρ`).  Wasserstein bounds are
`ℝ≥0∞` statements (ISSUES M1).  Technical hypotheses: `2 ≤ d` (standing, M L417), `1 ≤ N`
(`μ_N` needs at least one particle). -/
theorem iid_field_comparison (hd : 2 ≤ d) (m : ℝ) (hm : (d : ℝ) / 2 < m) (c Cbar : ℝ)
    (hc : 0 < c) :
    ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, c ≤ ρ x) →
      (∀ x, ρ x ≤ Cbar) → ∀ γ : Measure (NegSobolev d m),
      IsCenteredGaussianWithCov m γ (iidCov (withDensityReal ρ)) →
      ∀ N : ℕ, 1 ≤ N →
        smoothDist 2 (law (Measure.pi fun _ : Fin N => withDensityReal ρ)
            (fun X : Config d N => etaE m X (withDensityReal ρ))) γ ≤ Cm * iidRateSmooth d m N ∧
        wassersteinE 1 (law (Measure.pi fun _ : Fin N => withDensityReal ρ)
            (fun X : Config d N => etaE m X (withDensityReal ρ))) γ ≤
          ENNReal.ofReal (Cm * iidRateW d m N) ∧
        wassersteinE 2 (law (Measure.pi fun _ : Fin N => withDensityReal ρ)
            (fun X : Config d N => etaE m X (withDensityReal ρ))) γ ≤
          ENNReal.ofReal (Cm * iidRateW d m N ^ ((1 : ℝ) / 3)) := by
  sorry

/-- Proposition 5.9, last two sentences (M L6797-6803): the same three estimates hold for the
two-component product preparation with conditional density `(1 + aUb/√N)ρ` (`U` a fair sign, `a ∈ ℝ`
and `b ∈ L^∞(𝕋^d;ℝ)` fixed, `ρ(b) = 0`, `N ≥ max{2, 4a²‖b‖_∞²}`), the field being centered at `ρ`,
with limiting initial field `G_ρ + aUbρ dx` (`G_ρ` independent of `U`): the law of the limit is
`½ Law(G_ρ + abρ dx) + ½ Law(G_ρ - abρ dx)` (the shift `abρ dx ∈ E_m` is `NegSobolev.ofFun`).
The constant `C_m` is chosen after `a, b` and before `ρ` (uniform under the density bounds, as in
the first part).  `‖b‖_∞` is the essential supremum norm. -/
theorem iid_field_mixture (hd : 2 ≤ d) (m : ℝ) (hm : (d : ℝ) / 2 < m) (c Cbar : ℝ) (hc : 0 < c)
    (a : ℝ) (b : Torus d → ℝ) (hbm : Measurable b) (hbL : MemLp b ⊤ volume) :
    ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, c ≤ ρ x) →
      (∀ x, ρ x ≤ Cbar) → pair (withDensityReal ρ) b = 0 →
      ∀ γ : Measure (NegSobolev d m),
      IsCenteredGaussianWithCov m γ (iidCov (withDensityReal ρ)) →
      ∀ N : ℕ, 2 ≤ N → 4 * a ^ 2 * (eLpNorm b ⊤ volume).toReal ^ 2 ≤ N →
        smoothDist 2
            (law ((2 : ℝ≥0∞)⁻¹ • Measure.pi (fun _ : Fin N =>
                  withDensityReal fun x => (1 + a * b x / Real.sqrt N) * ρ x) +
                (2 : ℝ≥0∞)⁻¹ • Measure.pi (fun _ : Fin N =>
                  withDensityReal fun x => (1 - a * b x / Real.sqrt N) * ρ x))
              (fun X : Config d N => etaE m X (withDensityReal ρ)))
            ((2 : ℝ≥0∞)⁻¹ • γ.map (fun F => F + NegSobolev.ofFun m (fun x => a * b x * ρ x)) +
              (2 : ℝ≥0∞)⁻¹ • γ.map (fun F => F - NegSobolev.ofFun m (fun x => a * b x * ρ x))) ≤
          Cm * iidRateSmooth d m N ∧
        wassersteinE 1
            (law ((2 : ℝ≥0∞)⁻¹ • Measure.pi (fun _ : Fin N =>
                  withDensityReal fun x => (1 + a * b x / Real.sqrt N) * ρ x) +
                (2 : ℝ≥0∞)⁻¹ • Measure.pi (fun _ : Fin N =>
                  withDensityReal fun x => (1 - a * b x / Real.sqrt N) * ρ x))
              (fun X : Config d N => etaE m X (withDensityReal ρ)))
            ((2 : ℝ≥0∞)⁻¹ • γ.map (fun F => F + NegSobolev.ofFun m (fun x => a * b x * ρ x)) +
              (2 : ℝ≥0∞)⁻¹ • γ.map (fun F => F - NegSobolev.ofFun m (fun x => a * b x * ρ x))) ≤
          ENNReal.ofReal (Cm * iidRateW d m N) ∧
        wassersteinE 2
            (law ((2 : ℝ≥0∞)⁻¹ • Measure.pi (fun _ : Fin N =>
                  withDensityReal fun x => (1 + a * b x / Real.sqrt N) * ρ x) +
                (2 : ℝ≥0∞)⁻¹ • Measure.pi (fun _ : Fin N =>
                  withDensityReal fun x => (1 - a * b x / Real.sqrt N) * ρ x))
              (fun X : Config d N => etaE m X (withDensityReal ρ)))
            ((2 : ℝ≥0∞)⁻¹ • γ.map (fun F => F + NegSobolev.ofFun m (fun x => a * b x * ρ x)) +
              (2 : ℝ≥0∞)⁻¹ • γ.map (fun F => F - NegSobolev.ofFun m (fun x => a * b x * ρ x))) ≤
          ENNReal.ofReal (Cm * iidRateW d m N ^ ((1 : ℝ) / 3)) := by
  sorry

/-! ### Proposition 5.10 (uniformly integrable initial densities) -/

/-- `Θ(L) = sup_{N≥2} ∫ h_N^∘ 1_{h_N^∘ > L} dℙ_{N,β}` (`A:eq:UI`, M L7027-7030), where
`h_N^∘ = dν_N^∘/dℙ_{N,β}` and `ℙ_{N,β}` is the canonical Gibbs law of the gradient model with potential
`V` (`canonicalGibbs`).  For `ν_N^∘ ≪ ℙ_{N,β}` the integral equals `ν_N^∘{h_N^∘ > L}`.  The family
is indexed by `n ↦ N = n + 2`; the value is in `ℝ≥0∞`. -/
def uiTail (d : ℕ) (s β : ℝ) (V : Torus d → ℝ) (ν : ∀ n : ℕ, Measure (Config d (n + 2)))
    (L : ℝ) : ℝ≥0∞ :=
  ⨆ n : ℕ, ν n {X | ENNReal.ofReal L <
    (ν n).rnDeriv (canonicalGibbs (periodicRiesz d s) V (n + 2) β) X}

/-- Proposition 5.10 (`M:A:prop:UI`, TeX M L7035-7047), quantitative part (the displays `A:eq:UI-error`
and the sentence after it, M L7040-7044): for the stationary canonical gradient dynamics (smooth
`V`, thermal density `ρβ`, `μ_β = ρβ dx`) started from laws `ν_N^∘ ≪ ℙ_{N,β}` and the exactly centered
fluctuations `ζ_N^t = √N(μ_N^t - m_{N,β})` (center the invariant first marginal), for fixed smooth
tests `φ_a` and `T`, there are `C_T, c > 0` (independent of `L`, `N` and of the family `ν`) such that
for every `L ≥ 1` with `Θ(L) ≤ 1/2`:
(1) the comparison retaining the initial law, for terminal times `t_a ∈ [0,T]` and every Gaussian `G`
independent of the initial configuration with the noise covariance `noiseCovMatrix` (frozen
coefficient `ρβ`, `q = β⁻¹`):
`d_{C²}((⟨φ_a, ζ_N^{t_a}⟩)_a, (⟨U^{0,t_a}φ_a, ζ_N^∘⟩)_a + G) ≤ C_T√L ε_N + 4Θ(L)`, `ε_N = √δ_N`;
(2) at times `u + t_a` (`u ≥ 0`, lags `t_a ∈ [0,T]`) the comparison with the stationary Gaussian vector
(`PDE.stationaryLagCov`) has error `≤ C_T√L(ε_N + e^{-cu}) + 4Θ(L)`.
AMBIGUITY (M L7036-7037, L7050-7054): the source derives these from `H:thm:equilibrium` applied to the
truncated `L²` densities `h_{N,L}`; the stationary theorem as printed (M L943-975) contains no
initial-law clause, so the base estimate `C√L ε_N` for `‖h‖₂² ≤ 2L` is taken from M L7054-7056 and the
Remark M L1217-1225.  The path-space qualitative clauses of M L7037-7038 (convergence in law in
`C([a,a+T];E_m)`, identification of the initial law of the limiting equation, tightness of paths) are
NOT stated.  `ζ_N^∘ = ζ_N^0` is the `t = 0` centered field.  Technical hypotheses: `2 ≤ d`,
global solutions (`∀ T'`), `ν_N^∘ ≪ ℙ_{N,β}` (so that the densities `h_N^∘` exist). -/
theorem ui_comparison (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hρpos : ∀ x, 0 < ρβ x) (T : ℝ) (hT : 0 ≤ T) (p : ℕ) (φ : Fin p → Torus d → ℝ)
    (hφ : ∀ a, Torus.IsSmooth (φ a)) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ S : ParticleSeq d,
      (∀ T' : ℝ, 0 ≤ T' → S.IsSolutionOn (PDE.mfData d s hs0 hsd V β hβ) T') →
      (∀ n, ∃ (ℱ : MeasureTheory.Filtration ℝ (S.mΩ n))
          (W' : ℝ≥0 → S.Ω n → (Fin (n + 2) × Fin d) → ℝ),
        IsFilteredSolution (S.P n) ℱ W' (S.W n) (S.X n)) →
      (∀ n, (S.P n).map (S.X₀ n) ≪ canonicalGibbs (periodicRiesz d s) V (n + 2) β) →
      ∀ L : ℝ, 1 ≤ L → uiTail d s β V (fun n => (S.P n).map (S.X₀ n)) L ≤ 1 / 2 → ∀ n : ℕ,
        (∀ t : Fin p → ℝ, (∀ a, t a ∈ Set.Icc (0 : ℝ) T) →
          ∀ G : S.Ω n → EuclideanSpace ℝ (Fin p),
            law (S.P n) G = ProbabilityTheory.multivariateGaussian 0
              (noiseCovMatrix (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) β⁻¹ t φ) →
            AEMeasurable G (S.P n) →
            ProbabilityTheory.IndepFun (S.X₀ n) G (S.P n) →
            ENNReal.ofReal (smoothDist 2
                (law (S.P n) fun ω => (WithLp.toLp 2 fun a =>
                  linCoord (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β)) (φ a)
                    (S.X n (t a).toNNReal ω) : EuclideanSpace ℝ (Fin p)))
                (law (S.P n) fun ω => (WithLp.toLp 2 fun a =>
                  linCoord (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β))
                    (propagator (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) 0 (t a) (φ a))
                    (S.X₀ n ω) + G ω a : EuclideanSpace ℝ (Fin p)))) ≤
              ENNReal.ofReal (C * Real.sqrt L * Real.sqrt (deltaN d s (n + 2))) +
                4 * uiTail d s β V (fun n => (S.P n).map (S.X₀ n)) L) ∧
        (∀ (u : ℝ), 0 ≤ u → ∀ t : Fin p → ℝ, (∀ a, t a ∈ Set.Icc (0 : ℝ) T) →
            ENNReal.ofReal (smoothDist 2
                (law (S.P n) fun ω => (WithLp.toLp 2 fun a =>
                  linCoord (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β)) (φ a)
                    (S.X n (u + t a).toNNReal ω) : EuclideanSpace ℝ (Fin p)))
                (ProbabilityTheory.multivariateGaussian 0
                  (PDE.stationaryLagCov d s β (PDE.mfData d s hs0 hsd V β hβ) ρβ t φ))) ≤
              ENNReal.ofReal (C * Real.sqrt L *
                  (Real.sqrt (deltaN d s (n + 2)) + Real.exp (-c * u))) +
                4 * uiTail d s β V (fun n => (S.P n).map (S.X₀ n)) L) := by
  sorry

/-- Proposition 5.10, qualitative part (M L7037-7038, and the limits taken in M L7063-7064): if
`Θ(L) → 0` as `L → ∞` (`A:eq:UI`), then for fixed smooth tests the initial-law comparison of
`ui_comparison` (1) tends to `0` as `N → ∞` (for every choice of Gaussian vectors `G_n` independent of
the initial configuration with the covariance `noiseCovMatrix`), and for every `u_n → ∞` the shifted-
window vector at times `u_n + t_a` converges to the stationary Gaussian vector (`d_{C²} → 0`).
(Interpretation of "all qualitative initial-law and shifted-window conclusions of
`H:thm:equilibrium`": the finite-dimensional conclusions; see the AMBIGUITY of `ui_comparison`; the
path-space qualitative conclusions, i.e. convergence in law in `C([a,a+T];E_m)` of `ζ_N^{a_N+·}` and of
the fluctuation trajectories with identified initial law, are NOT stated.)  Technical hypotheses:
`0 ≤ u_n` (`Real.toNNReal` of a negative time is a junk value), `2 ≤ d`. -/
theorem ui_qualitative (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hρpos : ∀ x, 0 < ρβ x) (T : ℝ) (hT : 0 ≤ T) (p : ℕ) (φ : Fin p → Torus d → ℝ)
    (hφ : ∀ a, Torus.IsSmooth (φ a)) (S : ParticleSeq d)
    (hS : ∀ T' : ℝ, 0 ≤ T' → S.IsSolutionOn (PDE.mfData d s hs0 hsd V β hβ) T')
    (hSF : ∀ n, ∃ (ℱ : MeasureTheory.Filtration ℝ (S.mΩ n))
      (W' : ℝ≥0 → S.Ω n → (Fin (n + 2) × Fin d) → ℝ),
      IsFilteredSolution (S.P n) ℱ W' (S.W n) (S.X n))
    (hν : ∀ n, (S.P n).map (S.X₀ n) ≪ canonicalGibbs (periodicRiesz d s) V (n + 2) β)
    (hUI : Tendsto (uiTail d s β V (fun n => (S.P n).map (S.X₀ n))) atTop (𝓝 0))
    (t : Fin p → ℝ) (ht : ∀ a, t a ∈ Set.Icc (0 : ℝ) T)
    (G : ∀ n, S.Ω n → EuclideanSpace ℝ (Fin p))
    (hG : ∀ n, law (S.P n) (G n) = ProbabilityTheory.multivariateGaussian 0
      (noiseCovMatrix (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) β⁻¹ t φ))
    (hGm : ∀ n, AEMeasurable (G n) (S.P n))
    (hGi : ∀ n, ProbabilityTheory.IndepFun (S.X₀ n) (G n) (S.P n))
    (u : ℕ → ℝ) (hu0 : ∀ n, 0 ≤ u n) (hu : Tendsto u atTop atTop) :
    Tendsto (fun n => smoothDist 2
        (law (S.P n) fun ω => (WithLp.toLp 2 fun a =>
          linCoord (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β)) (φ a)
            (S.X n (t a).toNNReal ω) : EuclideanSpace ℝ (Fin p)))
        (law (S.P n) fun ω => (WithLp.toLp 2 fun a =>
          linCoord (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β))
            (propagator (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) 0 (t a) (φ a))
            (S.X₀ n ω) + G n ω a : EuclideanSpace ℝ (Fin p)))) atTop (𝓝 0) ∧
    Tendsto (fun n => smoothDist 2
        (law (S.P n) fun ω => (WithLp.toLp 2 fun a =>
          linCoord (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β)) (φ a)
            (S.X n (u n + t a).toNNReal ω) : EuclideanSpace ℝ (Fin p)))
        (ProbabilityTheory.multivariateGaussian 0
          (PDE.stationaryLagCov d s β (PDE.mfData d s hs0 hsd V β hβ) ρβ t φ))) atTop (𝓝 0) := by
  sorry

/-- Proposition 5.10, last sentence (M L7044-7045) with its proof (`A:eq:entropy-tail`, M L7065-7070):
a uniform bound `H(ν_N^∘ | ℙ_{N,β}) ≤ H₀` on the unnormalized entropy implies the uniform integrability
`A:eq:UI`, quantitatively `Θ(L) ≤ (H₀ + e⁻¹)/log L` for `L > 1`. -/
theorem ui_of_entropy_bound {s β : ℝ} (V : Torus d → ℝ) (ν : ∀ n : ℕ, Measure (Config d (n + 2)))
    (hν : ∀ n, IsProbabilityMeasure (ν n)) (H₀ : ℝ)
    (hH : ∀ n, relEntropy (ν n) (canonicalGibbs (periodicRiesz d s) V (n + 2) β) ≤
      ENNReal.ofReal H₀) :
    (∀ L : ℝ, 1 < L → uiTail d s β V ν L ≤ ENNReal.ofReal ((H₀ + Real.exp (-1)) / Real.log L)) ∧
      Tendsto (uiTail d s β V ν) atTop (𝓝 0) := by
  sorry

/-! ### Proposition 5.13 (equilibrium-relative initial laws) -/

/-! #### Auxiliary lemmas for Proposition 5.13 (L² contraction of an invariant Markov family) -/

namespace Rel513Aux

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {S : Type*} [MeasurableSpace S]

/-- Jensen (Cauchy–Schwarz with constant `1`) for a probability measure, in `ℝ≥0∞`. -/
theorem jensen_enn {μ : Measure S} [IsProbabilityMeasure μ] {φ : S → ℝ≥0∞} (hφ : Measurable φ) :
    (∫⁻ x, φ x ∂μ) ^ (2 : ℝ) ≤ ∫⁻ x, φ x ^ (2 : ℝ) ∂μ := by
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ (p := 2) (q := 2) Real.HolderConjugate.two_two
    (f := fun _ => (1 : ℝ≥0∞)) (g := φ) measurable_const.aemeasurable hφ.aemeasurable
  simp only [Pi.mul_apply, one_mul, ENNReal.one_rpow, lintegral_one, measure_univ] at hH
  calc (∫⁻ x, φ x ∂μ) ^ (2 : ℝ) ≤ ((∫⁻ x, φ x ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow hH (by norm_num)
    _ = ∫⁻ x, φ x ^ (2 : ℝ) ∂μ := by
        rw [← ENNReal.rpow_mul]
        norm_num

/-- `L¹(ν κ)`-bound: `‖f‖_{L¹(ν κ)} ≤ ‖h‖_{L²(Π)} ‖f‖_{L²(Π)}` when `ν = h Π` and `Π κ = Π`. -/
theorem l1_core (Pi : Measure S) [IsProbabilityMeasure Pi] (κ : Kernel S S) [IsMarkovKernel κ]
    (hinv : Pi.bind κ = Pi) (ν : Measure S) (h : S → ℝ≥0∞) (hh : Measurable h)
    (hν : Pi.withDensity h = ν) (f : S → ℝ) (hf : Measurable f) :
    ∫⁻ x, ‖f x‖ₑ ∂(ν.bind κ) ≤ eLpNorm h 2 Pi * eLpNorm f 2 Pi := by
  have hfn : Measurable (fun x => ‖f x‖ₑ) := hf.enorm
  have hfn2 : Measurable (fun x => ‖f x‖ₑ ^ (2 : ℝ)) := hfn.pow_const _
  have hg : Measurable (fun y => ∫⁻ x, ‖f x‖ₑ ∂(κ y)) := hfn.lintegral_kernel
  have hg2 : Measurable (fun y => ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(κ y)) := hfn2.lintegral_kernel
  rw [Measure.lintegral_bind κ.measurable.aemeasurable hfn.aemeasurable, ← hν,
    lintegral_withDensity_eq_lintegral_mul Pi hh hg]
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq Pi (p := 2) (q := 2) Real.HolderConjugate.two_two
    hh.aemeasurable hg.aemeasurable
  have hJ : ∫⁻ y, (∫⁻ x, ‖f x‖ₑ ∂(κ y)) ^ (2 : ℝ) ∂Pi ≤ ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂Pi := by
    calc ∫⁻ y, (∫⁻ x, ‖f x‖ₑ ∂(κ y)) ^ (2 : ℝ) ∂Pi ≤ ∫⁻ y, ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(κ y) ∂Pi :=
          lintegral_mono fun y => jensen_enn (μ := κ y) hfn
      _ = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(Pi.bind κ) :=
          (Measure.lintegral_bind κ.measurable.aemeasurable hfn2.aemeasurable).symm
      _ = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂Pi := by rw [hinv]
  have hhn : eLpNorm h 2 Pi = (∫⁻ x, h x ^ (2 : ℝ) ∂Pi) ^ ((1 : ℝ) / 2) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hh.aestronglyMeasurable]
    simp
  have hfn' : eLpNorm f 2 Pi = (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂Pi) ^ ((1 : ℝ) / 2) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf.aestronglyMeasurable]
    simp
  rw [hhn, hfn']
  calc ∫⁻ x, (h * fun y => ∫⁻ x, ‖f x‖ₑ ∂(κ y)) x ∂Pi
      ≤ (∫⁻ x, h x ^ (2 : ℝ) ∂Pi) ^ ((1 : ℝ) / 2) *
          (∫⁻ x, (∫⁻ y, ‖f y‖ₑ ∂(κ x)) ^ (2 : ℝ) ∂Pi) ^ ((1 : ℝ) / 2) := hH
    _ ≤ (∫⁻ x, h x ^ (2 : ℝ) ∂Pi) ^ ((1 : ℝ) / 2) *
          (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂Pi) ^ ((1 : ℝ) / 2) := by
        gcongr

end Rel513Aux

/-- Proposition 5.13 (`M:O:prop:relative`, TeX M L7159-7171), the abstract Markov statement.
`Π` is an invariant law (`Π κ_r = Π`) of the Markov process with transition kernels `κ_r`, started
from the law `ν = h⁰Π`; the process `Xp` is any process whose one-time marginals are `ν κ_r`
(only these enter the proof, M L7168-7170).  The remainder integrand `A^r` (jointly measurable) obeys
`‖A^r‖_{L²(Π)} ≤ ε a(r)` for `r ∈ [0,t]` with `∫_0^t a ≤ C`, and `‖h⁰‖_{L²(Π)} ≤ R`.  Then
`E[|∫_0^t (A^r(X^r) - E[A^r(X^r)]) dr|] ≤ 2 R C ε`  (`ℝ≥0∞`-valued outer expectation; the inner
`E` is the actual expectation).  The hypothesis `ε_N → 0` of the source is not used for the
inequality at fixed `N` and is omitted (`ε = ε_N`).  The last sentence of the proposition ("for the stationary Riesz remainder estimates this applies
throughout `0 ≤ s < d`, with the actual finite-particle center and the complete marginal-induced linear term
retained") is not formalised: it is not a self-contained claim but the assertion that the remainder bound
of the (unstated) stationary Riesz identity of Section 4 has the form `‖A_N^r‖_{L²(Π_N)} ≤ ε_N a(r)`; it
instantiates this statement once that stationary identity is stated, and its content is that identity.
Technical hypotheses: measurability of `A`, `Xp`, `a`; integrability of `a` on `[0,t]` (so that
`∫_0^t a ≤ C` is not the junk value `0` of a Bochner integral); `0 ≤ ε`. -/
theorem relative_remainder {S : Type*} [MeasurableSpace S] (Pi : Measure S)
    [IsProbabilityMeasure Pi] (κ : ℝ → ProbabilityTheory.Kernel S S)
    [∀ r, ProbabilityTheory.IsMarkovKernel (κ r)] (hinv : ∀ r, 0 ≤ r → Pi.bind (κ r) = Pi)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Xp : ℝ → Ω → S) (hXp : Measurable fun q : ℝ × Ω => Xp q.1 q.2)
    (ν : Measure S) (hν : ν ≪ Pi) (R : ℝ) (hR : eLpNorm (ν.rnDeriv Pi) 2 Pi ≤ ENNReal.ofReal R)
    (hlaw : ∀ r, 0 ≤ r → P.map (Xp r) = ν.bind (κ r))
    (A : ℝ → S → ℝ) (hA : Measurable (Function.uncurry A)) (ε : ℝ) (hε : 0 ≤ ε)
    (a : ℝ → ℝ) (ha : ∀ r, 0 ≤ a r) (ha_meas : Measurable a) (t C : ℝ) (ht : 0 ≤ t)
    (ha_int : IntegrableOn a (Set.Icc (0 : ℝ) t))
    (hAL2 : ∀ r ∈ Set.Icc (0 : ℝ) t, eLpNorm (A r) 2 Pi ≤ ENNReal.ofReal (ε * a r))
    (haC : ∫ r in Set.Icc (0 : ℝ) t, a r ≤ C) :
    ∫⁻ ω, ENNReal.ofReal |∫ r in (0 : ℝ)..t, (A r (Xp r ω) - ∫ ω', A r (Xp r ω') ∂P)| ∂P ≤
      ENNReal.ofReal (2 * R * C * ε) := by
  -- `ν` is a probability measure: `ν univ = (ν κ_0) univ = P(Xp 0 ∈ univ) = 1`
  have hνfin : IsFiniteMeasure ν := by
    have hX0 : Measurable (Xp 0) := hXp.comp (measurable_const.prodMk measurable_id)
    have h0 : (ν.bind (κ 0)) Set.univ = 1 := by
      rw [← hlaw 0 le_rfl, Measure.map_apply hX0 MeasurableSet.univ]
      simp
    rw [Measure.bind_apply MeasurableSet.univ (κ 0).measurable.aemeasurable] at h0
    simp only [measure_univ] at h0
    rw [lintegral_one] at h0
    exact ⟨by rw [h0]; exact ENNReal.one_lt_top⟩
  set h := ν.rnDeriv Pi with hdef
  have hhm : Measurable h := Measure.measurable_rnDeriv ν Pi
  have hνeq : Pi.withDensity h = ν := Measure.withDensity_rnDeriv_eq ν Pi hν
  set Hn := eLpNorm h 2 Pi with hHn_def
  have hXpr : ∀ r : ℝ, Measurable (fun ω => Xp r ω) := fun r =>
    hXp.comp (measurable_const.prodMk measurable_id)
  have hAr : ∀ r : ℝ, Measurable (A r) := fun r =>
    hA.comp (measurable_const.prodMk measurable_id)
  have hC0 : 0 ≤ C := le_trans (setIntegral_nonneg measurableSet_Icc fun r _ => ha r) haC
  -- `L¹` bound for one time slice
  have hK : ∀ r ∈ Set.Icc (0 : ℝ) t, ∫⁻ ω, ‖A r (Xp r ω)‖ₑ ∂P ≤ Hn * ENNReal.ofReal (ε * a r) := by
    intro r hr
    have h1 : ∫⁻ ω, ‖A r (Xp r ω)‖ₑ ∂P = ∫⁻ x, ‖A r x‖ₑ ∂(P.map (Xp r)) :=
      (lintegral_map (hAr r).enorm (hXpr r)).symm
    rw [h1, hlaw r hr.1]
    have hl1 := Rel513Aux.l1_core Pi (κ r) (hinv r hr.1) ν h hhm hνeq (A r) (hAr r)
    calc ∫⁻ x, ‖A r x‖ₑ ∂(ν.bind (κ r)) ≤ Hn * eLpNorm (A r) 2 Pi := hl1
      _ ≤ Hn * ENNReal.ofReal (ε * a r) := by
        gcongr
        exact hAL2 r hr
  have hjoint : Measurable (fun q : ℝ × Ω => A q.1 (Xp q.1 q.2)) :=
    hA.comp (measurable_fst.prodMk hXp)
  have hcm : Measurable (fun r : ℝ => ∫ ω', A r (Xp r ω') ∂P) :=
    (StronglyMeasurable.integral_prod_right (f := fun r ω' => A r (Xp r ω'))
      hjoint.stronglyMeasurable).measurable
  have hFm : Measurable (fun q : ℝ × Ω => A q.1 (Xp q.1 q.2) - ∫ ω', A q.1 (Xp q.1 ω') ∂P) :=
    hjoint.sub (hcm.comp measurable_fst)
  -- pointwise-in-time bound on the centred integrand
  have hFbd : ∀ r ∈ Set.Icc (0 : ℝ) t, ∫⁻ ω, ‖A r (Xp r ω) - ∫ ω', A r (Xp r ω') ∂P‖ₑ ∂P ≤
      2 * (Hn * ENNReal.ofReal (ε * a r)) := by
    intro r hr
    have hc : ‖∫ ω', A r (Xp r ω') ∂P‖ₑ ≤ ∫⁻ ω', ‖A r (Xp r ω')‖ₑ ∂P :=
      enorm_integral_le_lintegral_enorm _
    have hmeas : Measurable (fun ω => ‖A r (Xp r ω)‖ₑ) := ((hAr r).comp (hXpr r)).enorm
    calc ∫⁻ ω, ‖A r (Xp r ω) - ∫ ω', A r (Xp r ω') ∂P‖ₑ ∂P
        ≤ ∫⁻ ω, (‖A r (Xp r ω)‖ₑ + ‖∫ ω', A r (Xp r ω') ∂P‖ₑ) ∂P :=
          lintegral_mono fun ω => enorm_sub_le
      _ = (∫⁻ ω, ‖A r (Xp r ω)‖ₑ ∂P) + ‖∫ ω', A r (Xp r ω') ∂P‖ₑ := by
          rw [lintegral_add_left hmeas, lintegral_const, measure_univ, mul_one]
      _ ≤ (∫⁻ ω, ‖A r (Xp r ω)‖ₑ ∂P) + ∫⁻ ω', ‖A r (Xp r ω')‖ₑ ∂P := by gcongr
      _ = 2 * ∫⁻ ω, ‖A r (Xp r ω)‖ₑ ∂P := by ring
      _ ≤ 2 * (Hn * ENNReal.ofReal (ε * a r)) := by
          gcongr
          exact hK r hr
  have hmeasG : Measurable fun r : ℝ => 2 * (Hn * ENNReal.ofReal (ε * a r)) := by
    have : Measurable fun r : ℝ => ENNReal.ofReal (ε * a r) :=
      ENNReal.measurable_ofReal.comp (ha_meas.const_mul ε)
    exact measurable_const.mul (measurable_const.mul this)
  have hmain : ∫⁻ ω, ENNReal.ofReal |∫ r in (0 : ℝ)..t, (A r (Xp r ω) - ∫ ω', A r (Xp r ω') ∂P)| ∂P ≤
      ∫⁻ r in Set.Ioc (0 : ℝ) t, 2 * (Hn * ENNReal.ofReal (ε * a r)) := by
    calc ∫⁻ ω, ENNReal.ofReal |∫ r in (0 : ℝ)..t, (A r (Xp r ω) - ∫ ω', A r (Xp r ω') ∂P)| ∂P
        = ∫⁻ ω, ‖∫ r in Set.Ioc (0 : ℝ) t, (A r (Xp r ω) - ∫ ω', A r (Xp r ω') ∂P)‖ₑ ∂P := by
          refine lintegral_congr fun ω => ?_
          rw [intervalIntegral.integral_of_le ht, Real.enorm_eq_ofReal_abs]
      _ ≤ ∫⁻ ω, (∫⁻ r in Set.Ioc (0 : ℝ) t, ‖A r (Xp r ω) - ∫ ω', A r (Xp r ω') ∂P‖ₑ) ∂P :=
          lintegral_mono fun ω => enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ r in Set.Ioc (0 : ℝ) t, (∫⁻ ω, ‖A r (Xp r ω) - ∫ ω', A r (Xp r ω') ∂P‖ₑ ∂P) := by
          refine lintegral_lintegral_swap ?_
          exact (hFm.enorm.comp measurable_swap).aemeasurable
      _ ≤ ∫⁻ r in Set.Ioc (0 : ℝ) t, 2 * (Hn * ENNReal.ofReal (ε * a r)) :=
          setLIntegral_mono hmeasG fun r hr => hFbd r ⟨hr.1.le, hr.2⟩
  have hint : ∫⁻ r in Set.Ioc (0 : ℝ) t, 2 * (Hn * ENNReal.ofReal (ε * a r)) =
      (2 * Hn * ENNReal.ofReal ε) * ENNReal.ofReal (∫ r in Set.Ioc (0 : ℝ) t, a r) := by
    have hIoc : IntegrableOn a (Set.Ioc 0 t) := ha_int.mono_set Set.Ioc_subset_Icc_self
    have hm : Measurable fun r => ENNReal.ofReal (a r) := ENNReal.measurable_ofReal.comp ha_meas
    rw [ofReal_integral_eq_lintegral_ofReal hIoc (Filter.Eventually.of_forall ha),
      ← lintegral_const_mul _ hm]
    refine lintegral_congr fun r => ?_
    rw [ENNReal.ofReal_mul hε]
    ring
  have hintC : ∫ r in Set.Ioc (0 : ℝ) t, a r ≤ C := by
    rw [← integral_Icc_eq_integral_Ioc]
    exact haC
  have hbound : ∫⁻ ω, ENNReal.ofReal |∫ r in (0 : ℝ)..t, (A r (Xp r ω) - ∫ ω', A r (Xp r ω') ∂P)| ∂P ≤
      (2 * Hn * ENNReal.ofReal ε) * ENNReal.ofReal C :=
    hmain.trans (hint.le.trans (by gcongr))
  by_cases hR0 : 0 ≤ R
  · have hfin : (2 * Hn * ENNReal.ofReal ε) * ENNReal.ofReal C ≤
        ENNReal.ofReal (2 * R * C * ε) := by
      have e : ENNReal.ofReal (2 * R * C * ε) =
          (2 * ENNReal.ofReal R * ENNReal.ofReal ε) * ENNReal.ofReal C := by
        rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg zero_le_two hR0) hC0),
          ENNReal.ofReal_mul (mul_nonneg zero_le_two hR0), ENNReal.ofReal_mul zero_le_two,
          ENNReal.ofReal_ofNat]
        ring
      rw [e]
      gcongr
    exact hbound.trans hfin
  · have hR0' : ENNReal.ofReal R = 0 := ENNReal.ofReal_eq_zero.mpr (le_of_lt (not_le.mp hR0))
    have hHn0 : Hn = 0 := le_antisymm (hR.trans hR0'.le) zero_le
    have hz : (2 * Hn * ENNReal.ofReal ε) * ENNReal.ofReal C = 0 := by
      rw [hHn0]
      simp
    exact le_trans (hbound.trans hz.le) zero_le


/-! ### Proposition 5.14 (full-range implication with its missing input explicit) -/

/-- `⟨φ, ζ_N^t⟩ = √N(μ_N^t(φ) - m_N^t(φ))`, `m_N^t = E[μ_N^t]` the actual mean empirical measure
(`H:eq:centerings`, M L461-466). -/
def zetaStat {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω) (X : ℝ≥0 → Ω → Config d N)
    (t : ℝ) (φ : Torus d → ℝ) (ω : Ω) : ℝ :=
  Real.sqrt N * ((1 / (N : ℝ)) * ∑ i, φ (X t.toNNReal ω i) -
    pair (meanEmpirical (P.map (X t.toNNReal))) φ)

/-- `𝓡_N(t,φ) = √N ∫_0^t (𝖢_N(∇U^{r,t}φ; μ^r) - E[𝖢_N(∇U^{r,t}φ; μ^r)]) dr`
(`C:eq:integrated-remainder`, M L7178-7183), with `𝖢_N(v;μ) = F_N^{h_v}(X_N, μ)` (`N:eq:commutator`). -/
def integratedRemainder {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (D : DynData d)
    (ρ : ℝ → Torus d → ℝ) (P : Measure Ω) (X : ℝ≥0 → Ω → Config d N) (t : ℝ)
    (φ : Torus d → ℝ) (ω : Ω) : ℝ :=
  ∫ r in (0 : ℝ)..t, centeredCommutatorForcing d D.s P (fun r => withDensityReal (ρ r)) X
    (propagator D ρ r t φ) r ω

/-- `r_N = sup_{t≥0} sup_{‖Q_βφ‖_{H^j} ≤ 1} E[|𝓡_N(t,φ)|]` (`C:eq:rN`, M L7185-7187), as an `ℝ≥0∞`
supremum of `lintegral`s (`φ` continuous in `H^j`, `Q_β φ = φ - μ_β(φ)`). -/
def criterionRemainder {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (D : DynData d)
    (ρ : ℝ → Torus d → ℝ) (ρβ : Torus d → ℝ) (j : ℕ) (P : Measure Ω)
    (X : ℝ≥0 → Ω → Config d N) : ℝ≥0∞ :=
  ⨆ (t : ℝ) (_ : 0 ≤ t) (φ : Torus d → ℝ)
    (_ : Continuous φ ∧ MemSobolev (j : ℝ) φ ∧
      sobolevNorm (j : ℝ) (projMean (withDensityReal ρβ) φ) ≤ 1),
    ∫⁻ ω, ENNReal.ofReal |integratedRemainder D ρ P X t φ ω| ∂P

/-- Proposition 5.14 (`M:C:prop:criterion`, TeX M L7191-7211), first assertion
`C:eq:centered-comparison`: suppose the entropy bound `N:eq:entropy` holds for all `t ≥ 0` with a
constant `C₁` (as imported in M L6577-6580 `P:eq:entropy-input`), `B_N/N → 0` and `r_N → 0`.  Then,
for every fixed finite family of smooth tests, every `t_1, …, t_p ≥ 0` and every Gaussian `G`
independent of the initial configuration with covariance `C:eq:G-covariance` (`noiseCovMatrix`),
`d_{C²}((⟨φ_a, ζ_N^{t_a}⟩)_a, (⟨U^{0,t_a}φ_a, ζ_N^∘⟩)_a + G) ≤ C (r_N + √(B_N/N))`.
Representation: `r_N ∈ ℝ≥0∞`, so the bound is `ofReal d ≤ ofReal C * (r_N + ofReal √(B_N/N))`; the constant
`C` depends on the trajectory, `ρβ`, `j`, the tests and `C₁` only; `j` is even with `j > d/2 + 4` (as in
Proposition 5.2).  `ζ_N^∘ = ζ_N^0`.  The source's constants `C_T` of `N:eq:entropy` (taken uniform in
`t ≥ 0`) are the only part of the hypothesis on the particle systems beyond being global strong solutions.
"Strong solution" includes adaptedness to a Brownian filtration (`IsFilteredSolution`, as for the whole-space
`RdStanding.filtered`): `IsSolutionOn` only gives measurability (ISSUES D1), while the duality identity (Lemma 3.7)
needs the filtration.  Repair 2026-10-16, ISSUES §I "5.14". -/
theorem criterion_comparison (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hρpos : ∀ x, 0 < ρβ x) (j : ℕ) (hj : Even j) (hjd : (d : ℝ) / 2 + 4 < j) (p : ℕ)
    (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, Torus.IsSmooth (φ a)) (C₁ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : ParticleSeq d,
      (∀ T : ℝ, 0 ≤ T → S.IsSolutionOn htr.dyn T) →
      (∀ n, ∃ (ℱ : MeasureTheory.Filtration ℝ (S.mΩ n))
          (W' : ℝ≥0 → S.Ω n → (Fin (n + 2) × Fin d) → ℝ),
        IsFilteredSolution (S.P n) ℱ W' (S.W n) (S.X n)) →
      (∀ n, relEntropy ((S.P n).map (S.X₀ n))
        (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ 0))) ≠ ⊤) →
      (∀ n, ∀ t : ℝ, 0 ≤ t →
        relEntropy ((S.P n).map (S.X n t.toNNReal))
              (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ t))) +
            relEntropy ((S.P n).map (S.X n t.toNNReal))
              (Measure.pi fun _ => withDensityReal (ρ t)) ≤
          ENNReal.ofReal (C₁ * entropyScale d s (n + 2) ((S.P n).map (S.X₀ n))
            (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ 0))))) →
      Tendsto (fun n : ℕ => entropyScale d s (n + 2) ((S.P n).map (S.X₀ n))
        (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ 0))) / ((n + 2 : ℕ) : ℝ))
        atTop (𝓝 0) →
      Tendsto (fun n : ℕ => criterionRemainder htr.dyn ρ ρβ j (S.P n) (S.X n)) atTop (𝓝 0) →
      ∀ n : ℕ, ∀ t : Fin p → ℝ, (∀ a, 0 ≤ t a) →
        ∀ G : S.Ω n → EuclideanSpace ℝ (Fin p),
          law (S.P n) G = ProbabilityTheory.multivariateGaussian 0
            (noiseCovMatrix htr.dyn ρ β⁻¹ t φ) →
          AEMeasurable G (S.P n) →
          ProbabilityTheory.IndepFun (S.X₀ n) G (S.P n) →
          ENNReal.ofReal (smoothDist 2
              (law (S.P n) fun ω => (WithLp.toLp 2 fun a =>
                zetaStat (S.P n) (S.X n) (t a) (φ a) ω : EuclideanSpace ℝ (Fin p)))
              (law (S.P n) fun ω => (WithLp.toLp 2 fun a =>
                zetaStat (S.P n) (S.X n) 0 (propagator htr.dyn ρ 0 (t a) (φ a)) ω + G ω a :
                  EuclideanSpace ℝ (Fin p)))) ≤
            ENNReal.ofReal C * (criterionRemainder htr.dyn ρ ρβ j (S.P n) (S.X n) +
              ENNReal.ofReal (Real.sqrt (entropyScale d s (n + 2) ((S.P n).map (S.X₀ n))
                (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ 0))) /
                  ((n + 2 : ℕ) : ℝ)))) := by
  sorry

/-- Proposition 5.14, last sentence (M L7208-7210): if in addition `sup_N E‖ζ_N^∘‖_{H^{-j}} < ∞`
(`≤ M`), the stationary comparison at times `u + τ_a` (fixed lags `τ_a ≥ 0`, so on every diverging
sequence `u_N`) has error `C(r_N + √(B_N/N) + e^{-c u})`, the comparison law being the stationary
Gaussian evolution `PDE.stationaryLagCov` with covariance `C:eq:stationary-cov`.  `C, c` depend on the
trajectory, `ρβ`, `j`, the tests, `C₁` and `M`. -/
theorem criterion_stationary (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hρpos : ∀ x, 0 < ρβ x) (j : ℕ) (hj : Even j) (hjd : (d : ℝ) / 2 + 4 < j) (p : ℕ)
    (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, Torus.IsSmooth (φ a)) (C₁ M : ℝ) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ S : ParticleSeq d,
      (∀ T : ℝ, 0 ≤ T → S.IsSolutionOn htr.dyn T) →
      (∀ n, ∃ (ℱ : MeasureTheory.Filtration ℝ (S.mΩ n))
          (W' : ℝ≥0 → S.Ω n → (Fin (n + 2) × Fin d) → ℝ),
        IsFilteredSolution (S.P n) ℱ W' (S.W n) (S.X n)) →
      (∀ n, relEntropy ((S.P n).map (S.X₀ n))
        (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ 0))) ≠ ⊤) →
      (∀ n, ∀ t : ℝ, 0 ≤ t →
        relEntropy ((S.P n).map (S.X n t.toNNReal))
              (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ t))) +
            relEntropy ((S.P n).map (S.X n t.toNNReal))
              (Measure.pi fun _ => withDensityReal (ρ t)) ≤
          ENNReal.ofReal (C₁ * entropyScale d s (n + 2) ((S.P n).map (S.X₀ n))
            (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ 0))))) →
      Tendsto (fun n : ℕ => entropyScale d s (n + 2) ((S.P n).map (S.X₀ n))
        (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ 0))) / ((n + 2 : ℕ) : ℝ))
        atTop (𝓝 0) →
      Tendsto (fun n : ℕ => criterionRemainder htr.dyn ρ ρβ j (S.P n) (S.X n)) atTop (𝓝 0) →
      (∀ n, ∫⁻ ω, ‖zetaE (j : ℝ) ((S.P n).map (S.X₀ n)) (S.X₀ n ω)‖ₑ ∂(S.P n) ≤
        ENNReal.ofReal M) →
      ∀ n : ℕ, ∀ u : ℝ, 0 ≤ u → ∀ τ : Fin p → ℝ, (∀ a, 0 ≤ τ a) →
          ENNReal.ofReal (smoothDist 2
              (law (S.P n) fun ω => (WithLp.toLp 2 fun a =>
                zetaStat (S.P n) (S.X n) (u + τ a) (φ a) ω : EuclideanSpace ℝ (Fin p)))
              (ProbabilityTheory.multivariateGaussian 0
                (PDE.stationaryLagCov d s β htr.dyn ρβ τ φ))) ≤
            ENNReal.ofReal C * (criterionRemainder htr.dyn ρ ρβ j (S.P n) (S.X n) +
              ENNReal.ofReal (Real.sqrt (entropyScale d s (n + 2) ((S.P n).map (S.X₀ n))
                (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ 0))) /
                  ((n + 2 : ℕ) : ℝ))) + ENNReal.ofReal (Real.exp (-c * u))) := by
  sorry

/-! ### Proposition 5.15 (existing), Corollaries 5.16 and 5.17 -/

/-- The conclusion of Proposition 5.15 (`M:E:prop:mean`, TeX M L7288-7313; the existing, proved
theorem `HRS.PDE.nonlinear_transient` asserts that for `0 < |ε| ≤ ε₀` such `ρ`, `A`, `C`, `C_j` exist):
for the homogeneous model `V = 0`, `ρ` is a global smooth positive solution of `H:eq:meanfield`
(`M = -I`, inverse temperature `β`) with datum `ρ⁰ = 1 + εψ_k`, `ψ_k = √2 cos(2πk·x)` (`PDE.cosTest`), and
there is `A` with `|A - ε| ≤ Cε²`, `sign A = sign ε`, and
`‖ρ^t - 1 - A e^{-λt}ψ_k‖_{C^j} ≤ C_j ε² e^{-3λt/2}` (`λ = λ_{β,k} = PDE.transientRate`) for all `t ≥ 0`
and `j ≥ 0` (`E:eq:amplitude`, `E:eq:mean-asymptotic`).  Used as the hypothesis "ε as in
Proposition 5.15" of Corollaries 5.16 and 5.17 (Proposition 5.15 does not assert uniqueness of the
solution, so the corollaries are stated for every solution with these properties). -/
structure IsMeanTransient (d : ℕ) (s β : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (k : Lattice d) (ε A : ℝ) (ρ : ℝ → Torus d → ℝ) (C : ℝ) (Cj : ℕ → ℝ) : Prop where
  sol : ∀ T : ℝ, 0 < T → IsMeanFieldSolution (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) T ρ
  smooth_pos : ∀ t : ℝ, 0 ≤ t → Torus.IsSmooth (ρ t) ∧ ∀ x, 0 < ρ t x
  init : ρ 0 = fun x => 1 + ε * PDE.cosTest k x
  amp : |A - ε| ≤ C * ε ^ 2 ∧ Real.sign A = Real.sign ε
  asymp : ∀ (j : ℕ) (t : ℝ), 0 ≤ t →
    Torus.cbNorm j (fun x => ρ t x - 1 - A * Real.exp (-PDE.transientRate d s β k * t) *
      PDE.cosTest k x) ≤ Cj j * ε ^ 2 * Real.exp (-3 * PDE.transientRate d s β k * t / 2)

/-! #### Calculus for Corollary 5.16 (auxiliary lemmas used by the three corollaries below) -/

namespace Cor516Aux

variable {d : ℕ}

theorem cbNorm_nonneg' (j : ℕ) (φ : Torus d → ℝ) : 0 ≤ Torus.cbNorm j φ := by
  unfold Torus.cbNorm
  exact Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _

theorem cbNorm_zero_le (j : ℕ) (φ : Torus d → ℝ) : Torus.cbNorm 0 φ ≤ Torus.cbNorm j φ := by
  unfold Torus.cbNorm
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_succ (Nat.zero_le j)))
    fun _ _ _ => Real.iSup_nonneg fun _ => norm_nonneg _

theorem abs_le_cbNorm' {j : ℕ} {φ : Torus d → ℝ} (hφ : Torus.IsCk j φ) (x : Torus d) :
    |φ x| ≤ Torus.cbNorm j φ := by
  obtain ⟨y, rfl⟩ : ∃ y : Euc d, Torus.mk y = x := by
    choose r hr using fun i => QuotientAddGroup.mk_surjective (x i)
    exact ⟨WithLp.toLp 2 r, funext fun i => hr i⟩
  have hc : ContDiff ℝ ((0 : ℕ) : WithTop ℕ∞) (Torus.lift φ) :=
    (show ContDiff ℝ (j : WithTop ℕ∞) (Torus.lift φ) from hφ).of_le (by exact_mod_cast Nat.zero_le j)
  have h1 := le_ciSup (Torus.bddAbove_norm_iteratedFDeriv_lift 0 φ hc) y
  rw [norm_iteratedFDeriv_zero] at h1
  have e0 : Torus.cbNorm 0 φ = ⨆ z : Euc d, ‖iteratedFDeriv ℝ 0 (Torus.lift φ) z‖ := by
    unfold Torus.cbNorm
    rw [Finset.sum_range_one]
  calc |φ (Torus.mk y)| = ‖Torus.lift φ y‖ := (Real.norm_eq_abs _).symm
    _ ≤ Torus.cbNorm 0 φ := by rw [e0]; exact h1
    _ ≤ Torus.cbNorm j φ := cbNorm_zero_le j φ

theorem continuous_of_isCk' {f : Torus d → ℝ} {j : ℕ} (hf : Torus.IsCk j f) : Continuous f :=
  Torus.continuous_of_continuous_lift
    (show ContDiff ℝ (j : WithTop ℕ∞) (Torus.lift f) from hf).continuous

theorem isCk_of_isSmooth' {f : Torus d → ℝ} (h : Torus.IsSmooth f) (j : ℕ) : Torus.IsCk j f :=
  (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift f) from h).of_le (by exact_mod_cast le_top)

theorem isCk_const' (j : ℕ) (c : ℝ) : Torus.IsCk j (fun _ : Torus d => c) := by
  unfold Torus.IsCk
  exact contDiff_const

theorem isCk_sub' {j : ℕ} {f g : Torus d → ℝ} (hf : Torus.IsCk j f) (hg : Torus.IsCk j g) :
    Torus.IsCk j (fun x => f x - g x) := by
  unfold Torus.IsCk at *
  exact hf.sub hg

theorem isCk_const_mul' {j : ℕ} {f : Torus d → ℝ} (hf : Torus.IsCk j f) (c : ℝ) :
    Torus.IsCk j (fun x => c * f x) := by
  unfold Torus.IsCk at *
  exact contDiff_const.mul hf

theorem isCk_cosTest' (k : Lattice d) (j : ℕ) : Torus.IsCk j (PDE.cosTest k) := by
  have e : Torus.lift (PDE.cosTest k) = fun y => Real.sqrt 2 * Real.cos (Torus.freqFunctional k y) := by
    funext y
    simp [PDE.cosTest, Torus.lift, Torus.cosMode_mk, Torus.freqFunctional_apply]
  unfold Torus.IsCk
  rw [e]
  exact contDiff_const.mul (Real.contDiff_cos.comp (Torus.freqFunctional k).contDiff)

theorem cbNorm_const_mul' {j : ℕ} {f : Torus d → ℝ} (hf : Torus.IsCk j f) (c : ℝ) :
    Torus.cbNorm j (fun x => c * f x) ≤ |c| * Torus.cbNorm j f := by
  unfold Torus.cbNorm
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have hiL : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hci : ContDiff ℝ i (Torus.lift f) :=
    (show ContDiff ℝ (j : WithTop ℕ∞) (Torus.lift f) from hf).of_le (by exact_mod_cast hiL)
  have e : Torus.lift (fun x => c * f x) = c • Torus.lift f := by
    funext u
    simp [Torus.lift]
  refine ciSup_le fun x => ?_
  rw [e, iteratedFDeriv_const_smul_apply hci.contDiffAt, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (le_ciSup (Torus.bddAbove_norm_iteratedFDeriv_lift i f hci) x) (abs_nonneg _)

/-- Remainder: the `C^j` norm of `ρ^t - 1 - A e^{-λt} ψ` (asymptotic bound of `IsMeanTransient`). -/
theorem cbNorm_sub_scalar_le {lam A ε Cj : ℝ} {j : ℕ} {t : ℝ} {ρt : Torus d → ℝ} {k : Lattice d}
    (hR : Torus.cbNorm j (fun x => ρt x - 1 - A * Real.exp (-lam * t) * PDE.cosTest k x) ≤
      Cj * ε ^ 2 * Real.exp (-3 * lam * t / 2)) :
    Torus.cbNorm j (fun x => ρt x - 1 - A * Real.exp (-lam * t) * PDE.cosTest k x) ≤
      |Cj| * ε ^ 2 * Real.exp (-3 * lam * t / 2) := by
  have hE : 0 ≤ Real.exp (-3 * lam * t / 2) := (Real.exp_pos _).le
  refine hR.trans ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)) hE

/-- Decomposition of `σ(ρ^t - 1) - bψ` into the remainder and a multiple of `ψ`. -/
theorem decomp_cbNorm {lam A ε Cj : ℝ} {j : ℕ} {t : ℝ} {ρt : Torus d → ℝ} {k : Lattice d}
    (hsm : Torus.IsCk j ρt) (σ b : ℝ)
    (hR : Torus.cbNorm j (fun x => ρt x - 1 - A * Real.exp (-lam * t) * PDE.cosTest k x) ≤
      Cj * ε ^ 2 * Real.exp (-3 * lam * t / 2)) :
    Torus.cbNorm j (fun x => σ * (ρt x - 1) - b * PDE.cosTest k x) ≤
      |Cj| * ε ^ 2 * (|σ| * Real.exp (-3 * lam * t / 2)) +
        |σ * A * Real.exp (-lam * t) - b| * Torus.cbNorm j (PDE.cosTest k) := by
  have hRck : Torus.IsCk j (fun x => ρt x - 1 - A * Real.exp (-lam * t) * PDE.cosTest k x) :=
    isCk_sub' (isCk_sub' hsm (isCk_const' j 1)) (isCk_const_mul' (isCk_cosTest' k j) _)
  have e : (fun x => σ * (ρt x - 1) - b * PDE.cosTest k x) =
      (fun x => σ * (ρt x - 1 - A * Real.exp (-lam * t) * PDE.cosTest k x)) +
        (fun x => (σ * A * Real.exp (-lam * t) - b) * PDE.cosTest k x) := by
    funext x
    simp only [Pi.add_apply]
    ring
  rw [e]
  refine (Torus.cbNorm_add_le j _ _ (isCk_const_mul' hRck σ)
    (isCk_const_mul' (isCk_cosTest' k j) _)).trans (add_le_add ?_ ?_)
  · refine (cbNorm_const_mul' hRck σ).trans ?_
    have h2 := mul_le_mul_of_nonneg_left (cbNorm_sub_scalar_le hR) (abs_nonneg σ)
    calc |σ| * Torus.cbNorm j (fun x => ρt x - 1 - A * Real.exp (-lam * t) * PDE.cosTest k x)
        ≤ |σ| * (|Cj| * ε ^ 2 * Real.exp (-3 * lam * t / 2)) := h2
      _ = |Cj| * ε ^ 2 * (|σ| * Real.exp (-3 * lam * t / 2)) := by ring
  · exact cbNorm_const_mul' (isCk_cosTest' k j) _

/-- `∫ ψ_k² = 1` for `k ≠ 0` (`ψ_k = cosTest k`). -/
theorem integral_cosTest_sq {k : Lattice d} (hk : k ≠ 0) :
    ∫ x : Torus d, PDE.cosTest k x ^ 2 = 1 := by
  have key : ∀ k' : Lattice d, (hk' : k' ≠ 0) → Lattice.IsPosHalf k' →
      ∫ x : Torus d, PDE.cosTest k' x ^ 2 = 1 := by
    intro k' hk' hp
    have h := Torus.realMode_orthonormal ⟨k', hk'⟩ ⟨k', hk'⟩
    rw [if_pos rfl] at h
    have e : ∀ x : Torus d, Torus.realMode ⟨k', hk'⟩ x * Torus.realMode ⟨k', hk'⟩ x =
        PDE.cosTest k' x ^ 2 := by
      intro x
      simp only [Torus.realMode, if_pos hp, PDE.cosTest]
      ring
    simp_rw [e] at h
    exact h
  by_cases hp : Lattice.IsPosHalf k
  · exact key k hk hp
  · have hn : Lattice.IsPosHalf (-k) := (Torus.isPosHalf_neg k hk).mpr hp
    have hnk : -k ≠ 0 := neg_ne_zero.mpr hk
    refine Eq.trans ?_ (key (-k) hnk hn)
    congr 1
    funext x
    simp [PDE.cosTest, Torus.cosMode_neg]

theorem transientRate_pos' {s β : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (k : Lattice d) (hk : k ≠ 0) : 0 < PDE.transientRate d s β k := by
  unfold PDE.transientRate
  have h1 : 0 < Lattice.enorm k := lt_of_lt_of_le one_pos (one_le_enorm k hk)
  have h2 := rieszCoeff_pos hd hs0 hsd k hk
  have h3 : 0 < β⁻¹ := inv_pos.mpr hβ
  exact mul_pos (pow_pos (mul_pos (mul_pos two_pos Real.pi_pos) h1) 2) (by linarith)

theorem sqrt_mul_exp_eq {lam : ℝ} (hlam : 0 < lam) (N : ℕ) (hN : 1 ≤ N) (u : ℝ) :
    Real.sqrt N * Real.exp (-lam * u) = Real.exp (-lam * (u - (2 * lam)⁻¹ * Real.log N)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsq : Real.sqrt N = Real.exp (Real.log N * (1 / 2)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hNpos]
  have e : -lam * (u - (2 * lam)⁻¹ * Real.log N) = -lam * u + Real.log N * (1 / 2) := by
    field_simp
    ring
  rw [e, Real.exp_add, hsq]
  ring

theorem exp_three_half_le {lam u τ : ℝ} (hlam : 0 < lam) (huτ : u ≤ τ) :
    Real.exp (-3 * lam * τ / 2) ≤ Real.exp (-lam * u) * Real.exp (-(lam / 2) * u) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  nlinarith [mul_nonneg hlam.le (sub_nonneg.2 huτ)]

theorem late_cbNorm_le {lam A ε Cj : ℝ} {j : ℕ} {k : Lattice d} (hlam : 0 < lam) {u τ σ : ℝ}
    (hu : 0 ≤ u) (huτ : u ≤ τ) (hσ : 0 ≤ σ) {ρT : Torus d → ℝ} (hsm : Torus.IsCk j ρT)
    (hR : Torus.cbNorm j (fun x => ρT x - 1 - A * Real.exp (-lam * τ) * PDE.cosTest k x) ≤
      Cj * ε ^ 2 * Real.exp (-3 * lam * τ / 2)) :
    Torus.cbNorm j (fun x => σ * (ρT x - 1)) ≤
      |Cj| * ε ^ 2 * (σ * Real.exp (-lam * u) * Real.exp (-(lam / 2) * u)) +
        |A| * (σ * Real.exp (-lam * u)) * Torus.cbNorm j (PDE.cosTest k) := by
  have hd := decomp_cbNorm (k := k) hsm σ 0 hR
  have e0 : (fun x => σ * (ρT x - 1)) = (fun x => σ * (ρT x - 1) - 0 * PDE.cosTest k x) := by
    funext x
    ring
  rw [e0]
  refine hd.trans ?_
  have hE := exp_three_half_le hlam huτ
  have he : Real.exp (-lam * τ) ≤ Real.exp (-lam * u) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hlam.le (sub_nonneg.2 huτ)])
  have habs : |σ * A * Real.exp (-lam * τ) - 0| = σ * |A| * Real.exp (-lam * τ) := by
    rw [sub_zero, abs_mul, abs_mul, abs_of_nonneg hσ, abs_of_pos (Real.exp_pos _)]
  rw [habs, abs_of_nonneg hσ]
  have hΨ := cbNorm_nonneg' j (PDE.cosTest k)
  have h1 : |Cj| * ε ^ 2 * (σ * Real.exp (-3 * lam * τ / 2)) ≤
      |Cj| * ε ^ 2 * (σ * Real.exp (-lam * u) * Real.exp (-(lam / 2) * u)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc σ * Real.exp (-3 * lam * τ / 2) ≤ σ * (Real.exp (-lam * u) * Real.exp (-(lam / 2) * u)) :=
          mul_le_mul_of_nonneg_left hE hσ
      _ = σ * Real.exp (-lam * u) * Real.exp (-(lam / 2) * u) := by ring
  have h2 : σ * |A| * Real.exp (-lam * τ) * Torus.cbNorm j (PDE.cosTest k) ≤
      |A| * (σ * Real.exp (-lam * u)) * Torus.cbNorm j (PDE.cosTest k) := by
    refine mul_le_mul_of_nonneg_right ?_ hΨ
    calc σ * |A| * Real.exp (-lam * τ) = |A| * σ * Real.exp (-lam * τ) := by ring
      _ ≤ |A| * σ * Real.exp (-lam * u) := by gcongr
      _ = |A| * (σ * Real.exp (-lam * u)) := by ring
  linarith [h1, h2]

theorem crit_cbNorm_le {lam A ε Cj τ0 : ℝ} {j : ℕ} {k : Lattice d} (hlam : 0 < lam) {u t σ : ℝ}
    (hu : 0 ≤ u) (ht : 0 ≤ t) (hσ : 0 ≤ σ) {ρT : Torus d → ℝ} (hsm : Torus.IsCk j ρT)
    (hR : Torus.cbNorm j (fun x => ρT x - 1 - A * Real.exp (-lam * (u + t)) * PDE.cosTest k x) ≤
      Cj * ε ^ 2 * Real.exp (-3 * lam * (u + t) / 2)) :
    Torus.cbNorm j (fun x => σ * (ρT x - 1) - A * Real.exp (-lam * (τ0 + t)) * PDE.cosTest k x) ≤
      |Cj| * ε ^ 2 * (σ * Real.exp (-lam * u) * Real.exp (-(lam / 2) * u)) +
        |A| * |σ * Real.exp (-lam * u) - Real.exp (-lam * τ0)| * Torus.cbNorm j (PDE.cosTest k) := by
  have hd := decomp_cbNorm (k := k) hsm σ (A * Real.exp (-lam * (τ0 + t))) hR
  refine hd.trans ?_
  have hE := exp_three_half_le hlam (show u ≤ u + t by linarith)
  have hkey : σ * A * Real.exp (-lam * (u + t)) - A * Real.exp (-lam * (τ0 + t)) =
      A * Real.exp (-lam * t) * (σ * Real.exp (-lam * u) - Real.exp (-lam * τ0)) := by
    have e1 : Real.exp (-lam * (u + t)) = Real.exp (-lam * u) * Real.exp (-lam * t) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp (-lam * (τ0 + t)) = Real.exp (-lam * τ0) * Real.exp (-lam * t) := by
      rw [← Real.exp_add]; ring_nf
    rw [e1, e2]
    ring
  have hetle : Real.exp (-lam * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hlam.le ht])
  have hetpos := Real.exp_pos (-lam * t)
  have habs : |σ * A * Real.exp (-lam * (u + t)) - A * Real.exp (-lam * (τ0 + t))| ≤
      |A| * |σ * Real.exp (-lam * u) - Real.exp (-lam * τ0)| := by
    rw [hkey, abs_mul, abs_mul, abs_of_pos hetpos]
    have hX := abs_nonneg (σ * Real.exp (-lam * u) - Real.exp (-lam * τ0))
    have hA0 := abs_nonneg A
    nlinarith [mul_nonneg hA0 hX]
  rw [abs_of_nonneg hσ]
  have hΨ := cbNorm_nonneg' j (PDE.cosTest k)
  have h1 : |Cj| * ε ^ 2 * (σ * Real.exp (-3 * lam * (u + t) / 2)) ≤
      |Cj| * ε ^ 2 * (σ * Real.exp (-lam * u) * Real.exp (-(lam / 2) * u)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc σ * Real.exp (-3 * lam * (u + t) / 2) ≤ σ * (Real.exp (-lam * u) * Real.exp (-(lam / 2) * u)) :=
          mul_le_mul_of_nonneg_left hE hσ
      _ = σ * Real.exp (-lam * u) * Real.exp (-(lam / 2) * u) := by ring
  have h2 := mul_le_mul_of_nonneg_right habs hΨ
  linarith [h1, h2]

theorem early_lower {lam A ε Cj : ℝ} {j : ℕ} {k : Lattice d} (hk : k ≠ 0) {t : ℝ}
    {ρt : Torus d → ℝ} (hsm : Torus.IsCk j ρt)
    (hR : Torus.cbNorm j (fun x => ρt x - 1 - A * Real.exp (-lam * t) * PDE.cosTest k x) ≤
      Cj * ε ^ 2 * Real.exp (-3 * lam * t / 2)) :
    A * Real.exp (-lam * t) - Torus.cbNorm j (PDE.cosTest k) *
        (|Cj| * ε ^ 2 * Real.exp (-3 * lam * t / 2)) ≤
      ∫ x, PDE.cosTest k x * (ρt x - 1) := by
  have hψck : Torus.IsCk j (PDE.cosTest k) := isCk_cosTest' k j
  have hψc : Continuous (PDE.cosTest k) := continuous_of_isCk' hψck
  have hρc : Continuous ρt := continuous_of_isCk' hsm
  have hRck : Torus.IsCk j (fun x => ρt x - 1 - A * Real.exp (-lam * t) * PDE.cosTest k x) :=
    isCk_sub' (isCk_sub' hsm (isCk_const' j 1)) (isCk_const_mul' hψck _)
  have hRc : Continuous (fun x => ρt x - 1 - A * Real.exp (-lam * t) * PDE.cosTest k x) :=
    (hρc.sub continuous_const).sub (continuous_const.mul hψc)
  have hΨ := cbNorm_nonneg' j (PDE.cosTest k)
  have hR' := cbNorm_sub_scalar_le hR
  have hbd : ∀ x, |PDE.cosTest k x * (ρt x - 1 - A * Real.exp (-lam * t) * PDE.cosTest k x)| ≤
      Torus.cbNorm j (PDE.cosTest k) * (|Cj| * ε ^ 2 * Real.exp (-3 * lam * t / 2)) := fun x => by
    rw [abs_mul]
    exact mul_le_mul (abs_le_cbNorm' hψck x) ((abs_le_cbNorm' hRck x).trans hR') (abs_nonneg _) hΨ
  have hψ2 : ∀ x, |PDE.cosTest k x ^ 2| ≤ Torus.cbNorm j (PDE.cosTest k) ^ 2 := fun x => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_le_cbNorm' hψck x) 2
  have hi1 : MeasureTheory.Integrable
      (fun x => PDE.cosTest k x * (ρt x - 1 - A * Real.exp (-lam * t) * PDE.cosTest k x)) :=
    MeasureTheory.Integrable.of_bound ((hψc.mul hRc).aestronglyMeasurable)
      _ (MeasureTheory.ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hbd x)
  have hi2 : MeasureTheory.Integrable (fun x => (A * Real.exp (-lam * t)) * PDE.cosTest k x ^ 2) :=
    MeasureTheory.Integrable.of_bound ((continuous_const.mul (hψc.pow 2)).aestronglyMeasurable)
      (|A * Real.exp (-lam * t)| * Torus.cbNorm j (PDE.cosTest k) ^ 2)
      (MeasureTheory.ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (hψ2 x) (abs_nonneg _))
  have hsplit : ∫ x, PDE.cosTest k x * (ρt x - 1) =
      (∫ x, PDE.cosTest k x * (ρt x - 1 - A * Real.exp (-lam * t) * PDE.cosTest k x)) +
        (A * Real.exp (-lam * t)) * ∫ x, PDE.cosTest k x ^ 2 := by
    have e : (fun x => PDE.cosTest k x * (ρt x - 1)) = fun x =>
        PDE.cosTest k x * (ρt x - 1 - A * Real.exp (-lam * t) * PDE.cosTest k x) +
          (A * Real.exp (-lam * t)) * PDE.cosTest k x ^ 2 := by
      funext x
      ring
    rw [e, MeasureTheory.integral_add hi1 hi2, MeasureTheory.integral_const_mul]
  have hbI : |∫ x, PDE.cosTest k x * (ρt x - 1 - A * Real.exp (-lam * t) * PDE.cosTest k x)| ≤
      Torus.cbNorm j (PDE.cosTest k) * (|Cj| * ε ^ 2 * Real.exp (-3 * lam * t / 2)) := by
    have h := MeasureTheory.norm_integral_le_of_norm_le_const (μ := MeasureTheory.volume)
      (f := fun x => PDE.cosTest k x * (ρt x - 1 - A * Real.exp (-lam * t) * PDE.cosTest k x))
      (C := Torus.cbNorm j (PDE.cosTest k) * (|Cj| * ε ^ 2 * Real.exp (-3 * lam * t / 2)))
      (MeasureTheory.ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hbd x)
    rw [Real.norm_eq_abs] at h
    simpa using h
  rw [hsplit, integral_cosTest_sq hk]
  have hb := (abs_le.mp hbI).1
  linarith

end Cor516Aux

/-- Corollary 5.16 (`M:E:cor:mean-threshold`, TeX M L7441-7456), critical case: take `ε > 0` as in
Proposition 5.15 (`IsMeanTransient`), `t_N = (2λ)⁻¹ log N` and `u_N → ∞`.  If `u_N - t_N → τ ∈ ℝ`, then
for every `j` and `T < ∞`, `sup_{0≤t≤T} ‖√N(ρ^{u_N+t} - 1) - A e^{-λ(τ+t)}ψ_k‖_{C^j} → 0`
(`E:eq:mean-critical`; stated as uniform convergence in `t ∈ [0,T]`).  Technical hypotheses: `2 ≤ d`
(Proposition 5.15), `k ≠ 0`, `β ĝ(k) ≤ 1/4` (`E:eq:kchoice`). -/
theorem mean_threshold_critical (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (k : Lattice d) (hk : k ≠ 0) (hkβ : β * rieszCoeff d s k ≤ 1 / 4) (ε A : ℝ) (hε : 0 < ε)
    (ρ : ℝ → Torus d → ℝ) (C : ℝ) (Cj : ℕ → ℝ)
    (hρ : IsMeanTransient d s β hs0 hsd hβ k ε A ρ C Cj) (u : ℕ → ℝ) (hu : Tendsto u atTop atTop)
    (τ : ℝ)
    (hτ : Tendsto (fun N : ℕ => u N - (2 * PDE.transientRate d s β k)⁻¹ * Real.log N) atTop (𝓝 τ))
    (j : ℕ) (T : ℝ) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Torus.cbNorm j (fun x => Real.sqrt N * (ρ (u N + t) x - 1) -
        A * Real.exp (-PDE.transientRate d s β k * (τ + t)) * PDE.cosTest k x) ≤ η := by
  intro η hη
  set lam := PDE.transientRate d s β k with hlam_def
  have hlam : 0 < lam := Cor516Aux.transientRate_pos' hd hs0 hsd hβ k hk
  have hsm : ∀ t : ℝ, 0 ≤ t → Torus.IsCk j (ρ t) := fun t ht =>
    Cor516Aux.isCk_of_isSmooth' (hρ.smooth_pos t ht).1 j
  have hq : Tendsto (fun N : ℕ => Real.exp (-(lam / 2) * u N)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => -((lam / 2) * u N)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (hu.const_mul_atTop (half_pos hlam))
    exact (Real.tendsto_exp_atBot.comp h1).congr (fun N => by
      simp only [Function.comp]
      congr 1
      ring)
  have hδ : Tendsto (fun N : ℕ => Real.exp (-lam * (u N - (2 * lam)⁻¹ * Real.log N)))
      atTop (𝓝 (Real.exp (-lam * τ))) := by
    have hc : Continuous (fun y : ℝ => Real.exp (-lam * y)) := by fun_prop
    exact (hc.tendsto τ).comp hτ
  have ha : Tendsto (fun N : ℕ => Real.sqrt N * Real.exp (-lam * u N)) atTop
      (𝓝 (Real.exp (-lam * τ))) :=
    hδ.congr' (eventually_atTop.2 ⟨1, fun N hN =>
      (Cor516Aux.sqrt_mul_exp_eq hlam N hN (u N)).symm⟩)
  have hG := ((ha.mul hq).const_mul (|Cj j| * ε ^ 2)).add
    (((ha.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => Real.exp (-lam * τ)) atTop
      (𝓝 (Real.exp (-lam * τ))))).abs.const_mul |A|).mul_const (Torus.cbNorm j (PDE.cosTest k)))
  rw [show |Cj j| * ε ^ 2 * (Real.exp (-lam * τ) * 0) +
      |A| * |Real.exp (-lam * τ) - Real.exp (-lam * τ)| * Torus.cbNorm j (PDE.cosTest k) = 0 by
    simp] at hG
  have hcomb := (((tendsto_order.1 hG).2 η hη).and (hu.eventually_ge_atTop 0)).and
    (eventually_ge_atTop 1)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hcomb
  refine ⟨N₀, fun N hN t ht => ?_⟩
  obtain ⟨⟨hGN, hu0N⟩, hN1⟩ := hN₀ N hN
  have hT0 : 0 ≤ u N + t := by linarith [ht.1]
  have key := Cor516Aux.crit_cbNorm_le (ρT := ρ (u N + t)) (τ0 := τ) (σ := Real.sqrt N) hlam hu0N
    ht.1 (Real.sqrt_nonneg _) (hsm (u N + t) hT0) (hρ.asymp j (u N + t) hT0)
  exact key.trans hGN.le

/-- Corollary 5.16, second sentence (M L7447-7448): if `u_N - t_N → +∞`, the first term
`√N(ρ^{u_N+t} - 1)` of `E:eq:mean-critical` converges to zero in `C^j`, uniformly on `[0,T]`. -/
theorem mean_threshold_late (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (k : Lattice d) (hk : k ≠ 0) (hkβ : β * rieszCoeff d s k ≤ 1 / 4) (ε A : ℝ) (hε : 0 < ε)
    (ρ : ℝ → Torus d → ℝ) (C : ℝ) (Cj : ℕ → ℝ)
    (hρ : IsMeanTransient d s β hs0 hsd hβ k ε A ρ C Cj) (u : ℕ → ℝ) (hu : Tendsto u atTop atTop)
    (hlate : Tendsto (fun N : ℕ => u N - (2 * PDE.transientRate d s β k)⁻¹ * Real.log N)
      atTop atTop) (j : ℕ) (T : ℝ) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Torus.cbNorm j (fun x => Real.sqrt N * (ρ (u N + t) x - 1)) ≤ η := by
  intro η hη
  set lam := PDE.transientRate d s β k with hlam_def
  have hlam : 0 < lam := Cor516Aux.transientRate_pos' hd hs0 hsd hβ k hk
  have hsm : ∀ t : ℝ, 0 ≤ t → Torus.IsCk j (ρ t) := fun t ht =>
    Cor516Aux.isCk_of_isSmooth' (hρ.smooth_pos t ht).1 j
  have hq : Tendsto (fun N : ℕ => Real.exp (-(lam / 2) * u N)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => -((lam / 2) * u N)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (hu.const_mul_atTop (half_pos hlam))
    exact (Real.tendsto_exp_atBot.comp h1).congr (fun N => by
      simp only [Function.comp]
      congr 1
      ring)
  have ha : Tendsto (fun N : ℕ => Real.sqrt N * Real.exp (-lam * u N)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => -lam * (u N - (2 * lam)⁻¹ * Real.log N)) atTop atBot := by
      have h0 := tendsto_neg_atTop_atBot.comp (hlate.const_mul_atTop hlam)
      exact h0.congr (fun N => by
        simp only [Function.comp]
        ring)
    have h3 : Tendsto (fun N : ℕ => Real.exp (-lam * (u N - (2 * lam)⁻¹ * Real.log N)))
        atTop (𝓝 0) := Real.tendsto_exp_atBot.comp h1
    exact h3.congr' (eventually_atTop.2 ⟨1, fun N hN =>
      (Cor516Aux.sqrt_mul_exp_eq hlam N hN (u N)).symm⟩)
  have hG := ((ha.mul hq).const_mul (|Cj j| * ε ^ 2)).add
    (((ha.const_mul |A|)).mul_const (Torus.cbNorm j (PDE.cosTest k)))
  rw [show |Cj j| * ε ^ 2 * (0 * 0) + |A| * 0 * Torus.cbNorm j (PDE.cosTest k) = 0 by ring] at hG
  have hcomb := (((tendsto_order.1 hG).2 η hη).and (hu.eventually_ge_atTop 0)).and
    (eventually_ge_atTop 1)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hcomb
  refine ⟨N₀, fun N hN t ht => ?_⟩
  obtain ⟨⟨hGN, hu0N⟩, hN1⟩ := hN₀ N hN
  have hT0 : 0 ≤ u N + t := by linarith [ht.1]
  have key := Cor516Aux.late_cbNorm_le (ρT := ρ (u N + t)) (σ := Real.sqrt N) hlam hu0N
    (le_add_of_nonneg_right ht.1) (Real.sqrt_nonneg _) (hsm (u N + t) hT0) (hρ.asymp j (u N + t) hT0)
  exact key.trans hGN.le

/-- Corollary 5.16, third sentence (M L7448-7450, `E:eq:mean-divergence`): if `u_N - t_N → -∞`, then
`√N ⟨ψ_k, μ^{u_N} - dx⟩ = √N ∫ψ_k (ρ^{u_N} - 1) dx → +∞`. -/
theorem mean_threshold_early (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (k : Lattice d) (hk : k ≠ 0) (hkβ : β * rieszCoeff d s k ≤ 1 / 4) (ε A : ℝ) (hε : 0 < ε)
    (ρ : ℝ → Torus d → ℝ) (C : ℝ) (Cj : ℕ → ℝ)
    (hρ : IsMeanTransient d s β hs0 hsd hβ k ε A ρ C Cj) (u : ℕ → ℝ) (hu : Tendsto u atTop atTop)
    (hearly : Tendsto (fun N : ℕ => u N - (2 * PDE.transientRate d s β k)⁻¹ * Real.log N)
      atTop atBot) :
    Tendsto (fun N : ℕ => Real.sqrt N * ∫ x, PDE.cosTest k x * (ρ (u N) x - 1)) atTop atTop := by
  have hApos : 0 < A := by
    have hsgn := hρ.amp.2
    rw [Real.sign_of_pos hε] at hsgn
    rcases lt_trichotomy A 0 with h | h | h
    · rw [Real.sign_of_neg h] at hsgn
      norm_num at hsgn
    · rw [h, Real.sign_zero] at hsgn
      norm_num at hsgn
    · exact h
  set lam := PDE.transientRate d s β k with hlam_def
  have hlam : 0 < lam := Cor516Aux.transientRate_pos' hd hs0 hsd hβ k hk
  have hq : Tendsto (fun N : ℕ => Real.exp (-(lam / 2) * u N)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => -((lam / 2) * u N)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (hu.const_mul_atTop (half_pos hlam))
    exact (Real.tendsto_exp_atBot.comp h1).congr (fun N => by
      simp only [Function.comp]
      congr 1
      ring)
  set M := Torus.cbNorm 0 (PDE.cosTest k) * (|Cj 0| * ε ^ 2) with hM_def
  have hMq : Tendsto (fun N : ℕ => M * Real.exp (-(lam / 2) * u N)) atTop (𝓝 0) := by
    have := hq.const_mul M
    rwa [mul_zero] at this
  have hev : ∀ᶠ N : ℕ in atTop, M * Real.exp (-(lam / 2) * u N) < A / 2 :=
    (tendsto_order.1 hMq).2 (A / 2) (half_pos hApos)
  have ha_top : Tendsto (fun N : ℕ => Real.sqrt N * Real.exp (-lam * u N)) atTop atTop := by
    have h1 : Tendsto (fun N : ℕ => -lam * (u N - (2 * lam)⁻¹ * Real.log N)) atTop atTop := by
      have h0 : Tendsto (fun N : ℕ => lam * (u N - (2 * lam)⁻¹ * Real.log N)) atTop atBot :=
        hearly.const_mul_atBot hlam
      have h0' := tendsto_neg_atBot_atTop.comp h0
      exact h0'.congr (fun N => by
        simp only [Function.comp]
        ring)
    have h2 : Tendsto (fun N : ℕ => Real.exp (-lam * (u N - (2 * lam)⁻¹ * Real.log N)))
        atTop atTop := Real.tendsto_exp_atTop.comp h1
    exact h2.congr' (eventually_atTop.2 ⟨1, fun N hN =>
      (Cor516Aux.sqrt_mul_exp_eq hlam N hN (u N)).symm⟩)
  have hlow : Tendsto (fun N : ℕ => (A / 2) * (Real.sqrt N * Real.exp (-lam * u N))) atTop atTop :=
    ha_top.const_mul_atTop (half_pos hApos)
  refine tendsto_atTop_mono' atTop ?_ hlow
  filter_upwards [hev, eventually_ge_atTop 1, hu.eventually_ge_atTop 0] with N hevN hN1 huN
  have hsm0 : Torus.IsCk 0 (ρ (u N)) := Cor516Aux.isCk_of_isSmooth' (hρ.smooth_pos (u N) huN).1 0
  have hlb := Cor516Aux.early_lower (j := 0) hk hsm0 (hρ.asymp 0 (u N) huN)
  have hstep := mul_le_mul_of_nonneg_left hlb (Real.sqrt_nonneg (N : ℝ))
  have e3 : Real.exp (-3 * lam * u N / 2) = Real.exp (-lam * u N) * Real.exp (-(lam / 2) * u N) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hEq' : Real.sqrt N * Real.exp (-3 * lam * u N / 2) =
      (Real.sqrt N * Real.exp (-lam * u N)) * Real.exp (-(lam / 2) * u N) := by
    rw [e3]
    ring
  have hfinal : (A / 2) * (Real.sqrt N * Real.exp (-lam * u N)) ≤
      Real.sqrt N * (A * Real.exp (-lam * u N) - Torus.cbNorm 0 (PDE.cosTest k) *
        (|Cj 0| * ε ^ 2 * Real.exp (-3 * lam * u N / 2))) := by
    have hid : Real.sqrt N * (A * Real.exp (-lam * u N) - Torus.cbNorm 0 (PDE.cosTest k) *
        (|Cj 0| * ε ^ 2 * Real.exp (-3 * lam * u N / 2))) =
        (Real.sqrt N * Real.exp (-lam * u N)) * (A - M * Real.exp (-(lam / 2) * u N)) := by
      rw [hM_def]
      linear_combination (-(Torus.cbNorm 0 (PDE.cosTest k) * (|Cj 0| * ε ^ 2))) * hEq'
    rw [hid]
    have ha0 : 0 ≤ Real.sqrt N * Real.exp (-lam * u N) := mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
    calc (A / 2) * (Real.sqrt N * Real.exp (-lam * u N))
        = (Real.sqrt N * Real.exp (-lam * u N)) * (A / 2) := mul_comm _ _
      _ ≤ (Real.sqrt N * Real.exp (-lam * u N)) * (A - M * Real.exp (-(lam / 2) * u N)) :=
          mul_le_mul_of_nonneg_left (by linarith) ha0
  exact hfinal.trans hstep

/-- Corollary 5.17 (`M:E:cor:mean-particles`, TeX M L7466-7485): let `0 ≤ s < 2d/3` and prepare the
particles from `ℚ_{N,β₀}(μ⁰)`, `β₀ ≥ 0`, `μ⁰ = (1 + εψ_k)dx` (`E:eq:initial-mean`; `ρ` the mean-field
solution of Proposition 5.15, `IsMeanTransient`), the dynamics being the gradient dynamics with `V = 0`
at physical inverse temperature `β` (`PDE.mfData`, global strong solutions).  Fix `T < ∞`,
`m > d + 2`, `u_N → ∞` and let `Z_stat` be the homogeneous stationary linear fluctuation process at
inverse temperature `β` (`IsStationaryGaussianField` with `V = 0`, `ρ_β = 1`) on a probability space
`(Ω', P')`.  (a) In the critical case `u_N - (2λ)⁻¹ log N → τ`,
`√N(μ_N^{u_N+·} - dx) ⇒ Z_stat^· + A e^{-λ(τ+·)}ψ_k dx` in law in `C([0,T];H^{-m}_0)` (`E:eq:mean-particle-limit`;
the centering is Haar measure, `ρ ≡ 1` in `flucPath`, and the window is the time-shifted process);
(b) on later windows (`u_N - (2λ)⁻¹ log N → +∞`) the deterministic shift vanishes and the limit is `Z_stat`;
(c) if `u_N - (2λ)⁻¹ log N → -∞`, the observation against `ψ_k` at the start of the window,
`√N(μ_N^{u_N}(ψ_k) - ∫ψ_k dx)`, tends to `+∞` in probability.  Sequences of systems are indexed by
`n ↦ N = n+2`.  Technical hypotheses: `2 ≤ d`, `k ≠ 0`, `βĝ(k) ≤ 1/4`, `0 < ε`, `0 ≤ T`, and `0 ≤ u_n`
(the observation times are nonnegative; `Real.toNNReal` of a negative time is a junk value).

Statement repair (ISSUES.md, entry "Statement sweep repairs (ADAPTSPEC3)"): the proof uses the dynamic comparison (Proposition 5.4, Itô/duality calculus) along the sequence of systems, so each `S.X n` is assumed a filtered strong solution (`hSF`, `IsFilteredSolution`, the shape of `ui_qualitative`). -/
theorem mean_particles (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (hs : s < 2 * (d : ℝ) / 3) (hβ : 0 < β) (k : Lattice d) (hk : k ≠ 0)
    (hkβ : β * rieszCoeff d s k ≤ 1 / 4) (ε A : ℝ) (hε : 0 < ε) (ρ : ℝ → Torus d → ℝ) (C : ℝ)
    (Cj : ℕ → ℝ) (hρ : IsMeanTransient d s β hs0 hsd hβ k ε A ρ C Cj) (β₀ : ℝ) (hβ₀ : 0 ≤ β₀)
    (S : ParticleSeq d)
    (hS : ∀ T' : ℝ, 0 ≤ T' → S.IsSolutionOn (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) T')
    (hSF : ∀ n, ∃ (ℱ : MeasureTheory.Filtration ℝ (S.mΩ n))
      (W' : ℝ≥0 → S.Ω n → (Fin (n + 2) × Fin d) → ℝ),
      IsFilteredSolution (S.P n) ℱ W' (S.W n) (S.X n))
    (hinit : ∀ n, (S.P n).map (S.X₀ n) =
      modulatedGibbs (periodicRiesz d s) (n + 2) β₀ (withDensityReal (ρ 0)))
    (T : ℝ) (hT : 0 ≤ T) (m : ℝ) (hm : (d : ℝ) + 2 < m) (u : ℕ → ℝ) (hu0 : ∀ n, 0 ≤ u n)
    (hu : Tendsto u atTop atTop)
    (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z : ℝ → Ω' → NegSobolev d m)
    (hZ : IsStationaryGaussianField P' s β hs0 hsd hβ (fun _ => 0) (fun _ => 1) m Z) :
    (∀ τ : ℝ,
      Tendsto (fun n : ℕ => u n - (2 * PDE.transientRate d s β k)⁻¹ * Real.log (n + 2 : ℕ)) atTop
        (𝓝 τ) →
      MeasureTheory.TendstoInDistribution
        (fun n ω => flucPath m T (Real.sqrt ((n + 2 : ℕ) : ℝ))
          (fun t ω' => S.X n ((u n).toNNReal + t) ω') (fun _ _ => (1 : ℝ)) ω) atTop
        (toPath m T (fun t ω' => Z t ω' +
          (A * Real.exp (-PDE.transientRate d s β k * (τ + t))) •
            NegSobolev.ofFun m (PDE.cosTest k)))
        S.P P') ∧
    (Tendsto (fun n : ℕ => u n - (2 * PDE.transientRate d s β k)⁻¹ * Real.log (n + 2 : ℕ)) atTop
        atTop →
      MeasureTheory.TendstoInDistribution
        (fun n ω => flucPath m T (Real.sqrt ((n + 2 : ℕ) : ℝ))
          (fun t ω' => S.X n ((u n).toNNReal + t) ω') (fun _ _ => (1 : ℝ)) ω) atTop
        (toPath m T Z) S.P P') ∧
    (Tendsto (fun n : ℕ => u n - (2 * PDE.transientRate d s β k)⁻¹ * Real.log (n + 2 : ℕ)) atTop
        atBot →
      ∀ M : ℝ, Tendsto (fun n : ℕ => S.P n {ω | linCoord (volume : Measure (Torus d))
          (PDE.cosTest k) (S.X n (u n).toNNReal ω) ≤ M}) atTop (𝓝 0)) := by
  sorry

/-! ### Proposition 5.18 (an infinite stationary supremum) -/

/-- Proposition 5.18 (`M:U:prop:unbounded`, TeX M L7506-7514): for the stationary field (the
stationary Gaussian process of `U:eq:two-sided`, M L9096-9115, represented by
`IsStationaryGaussianField`, `d ≥ 2`, smooth `V`, thermal density `ρ_β`) and every sufficiently
negative Sobolev index `-m` (`m ≥ m₀`, `m₀` depending on `d`, `s`, `β`, `V`):
(i) the field is realised as an `E_m`-valued, a.s. continuous process, so that `‖η̄^t‖_{H^{-m}} < ∞`
a.s. for each `t` (existence of such a process on some probability space);
(ii) for every such process, a.s. `sup_{t≥0} ‖η̄^t‖_{H^{-m}} = ∞`, i.e. the trajectory is unbounded:
`∀ M, ∃ t ≥ 0, M < ‖η̄^t‖_{H^{-m}}`.
AMBIGUITY: with the `E_m`-valued representation `‖η̄^t‖_{H^{-m}} < ∞` is automatic, so the first assertion
of (`U:eq:unbounded-sup`) is stated as the existence of the `E_m`-valued continuous process with the
stationary covariance; the sup statement is stated without junk `iSup` as unboundedness. -/
theorem unbounded_stationary_sup (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hρpos : ∀ x, 0 < ρβ x) :
    ∃ m₀ : ℝ, ∀ m : ℝ, m₀ ≤ m →
      (∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
          (Z : ℝ → Ω → NegSobolev d m), IsStationaryGaussianField P s β hs0 hsd hβ V ρβ m Z) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (Z : ℝ → Ω → NegSobolev d m),
        IsStationaryGaussianField P s β hs0 hsd hβ V ρβ m Z →
        ∀ᵐ ω ∂P, ∀ M : ℝ, ∃ t : ℝ, 0 ≤ t ∧ M < ‖Z t ω‖ := by
  refine ⟨(d : ℝ) + 2, fun m hm => ⟨?_, ?_⟩⟩
  · exact HRS.Q41.q41_field_exists hd hs0 hsd hβ V hV ρβ hρβ m
      (by nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
  · intro Ω _ P _ Z hZ
    exact HRS.Q41.q41_unbounded_of_field hd hs0 hsd hβ V hV ρβ hρβ hρS hρpos m P Z hZ

end HRS
