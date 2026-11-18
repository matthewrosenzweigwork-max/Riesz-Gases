/-
# HRS.Equilibrium.StaticLimits — local divergence, field singularity, examples, quadratic limit
(EQ-01e)

* Proposition 7.17 `M:E:prop:local-divergence` (source lines 9649-9687),
* Proposition 2.4 `M:H:prop:field-singularity` (source lines 701-710),
* Examples 5.11 `M:A:ex:conditioned` and 5.12 `M:A:ex:cosine` (static parts, source lines
  7092-7119, 7139-7155; the time evolution `A:eq:half-normal-evolution` is dynamics),
* Lemma 7.5 `M:N:lem:quadratic-limit` (source lines 7956-7967; setting lines 7894-7954).
-/
import HRS.Equilibrium.PairCorrection
import HRS.Equilibrium.StaticLimitsAux
import HRS.Equilibrium.FieldSingAux
import HRS.Equilibrium.LocalDivAsym
import HRS.Equilibrium.LocalDivSub

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d : ℕ}

/-! ### Proposition 7.17: the exact local divergence -/

/-- `h_{φ,ε} = 1_{dist(x,y) > ε} h_φ` (`E:eq:hphi`, source lines 9654-9657), with the periodic
Euclidean distance (the leading constant for `s > d/2` depends on the shape of the cutoff). -/
def hCut (d : ℕ) (s : ℝ) (φ : Torus d → ℝ) (ε : ℝ) (x y : Torus d) : ℝ :=
  if ε < Torus.eucDist x y then hTransport d s φ x y else 0

/-- `J_{φ,ρ} = s²|𝕊^{d-1}|/(d(d+2)) ∫ ρ² ((Δφ)² + 2|D²φ|_F²) dx` (`E:eq:J`). -/
def localDivCoeff (d : ℕ) (s : ℝ) (ρ φ : Torus d → ℝ) : ℝ :=
  s ^ 2 * sphereArea d / (d * (d + 2)) *
    ∫ x, ρ x ^ 2 * (Torus.laplacian φ x ^ 2 +
      2 * ∑ i : Fin d, ∑ j : Fin d, Torus.partialDeriv i (Torus.partialDeriv j φ) x ^ 2)

/-- Proposition 7.17, `E:eq:J`: `J_{φ,ρ} > 0` for `0 < s < d`, a smooth positive density `ρ`
and a smooth nonconstant `φ`. -/
theorem localDivCoeff_pos {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) (ρ : Torus d → ℝ)
    (hρ : SmoothPosDensity ρ) (φ : Torus d → ℝ) (hφ : Torus.IsSmooth φ)
    (hnc : ∃ x y, φ x ≠ φ y) :
    0 < localDivCoeff d s ρ φ := by
  have hρc : Continuous ρ := StaticLimitAux.continuous_of_smooth hρ.smooth
  set g : Torus d → ℝ := fun x => ρ x ^ 2 * (Torus.laplacian φ x ^ 2 +
      2 * ∑ i : Fin d, ∑ j : Fin d, Torus.partialDeriv i (Torus.partialDeriv j φ) x ^ 2) with hg
  have gcont : Continuous g := by
    refine (hρc.pow 2).mul ((( StaticLimitsAux.continuous_laplacian hφ).pow 2).add
      (continuous_const.mul (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_)))
    exact (StaticLimitsAux.continuous_second hφ i j).pow 2
  have gnn : 0 ≤ g := fun x => by
    simp only [hg]
    positivity
  have hex : ∃ x0, g x0 ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨x, y, hxy⟩ := hnc
    refine hxy (StaticLimitsAux.const_of_second_zero hφ (fun i j z => ?_) x y)
    have h0 := hcon z
    have hρz : ρ z ^ 2 ≠ 0 := (pow_pos (hρ.pos z) 2).ne'
    have h1 : Torus.laplacian φ z ^ 2 +
        2 * ∑ i : Fin d, ∑ j : Fin d, Torus.partialDeriv i (Torus.partialDeriv j φ) z ^ 2 = 0 := by
      simp only [hg] at h0
      exact (mul_eq_zero.mp h0).resolve_left hρz
    have h2 : 0 ≤ ∑ i : Fin d, ∑ j : Fin d, Torus.partialDeriv i (Torus.partialDeriv j φ) z ^ 2 :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
    have h3 : ∑ i : Fin d, ∑ j : Fin d, Torus.partialDeriv i (Torus.partialDeriv j φ) z ^ 2 = 0 := by
      nlinarith [sq_nonneg (Torus.laplacian φ z)]
    have h4 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      sq_nonneg (Torus.partialDeriv i (Torus.partialDeriv j φ) z)).mp h3 i (Finset.mem_univ _)
    have h5 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
      sq_nonneg (Torus.partialDeriv i (Torus.partialDeriv j φ) z)).mp h4 j (Finset.mem_univ _)
    exact pow_eq_zero_iff (two_ne_zero) |>.mp h5
  obtain ⟨x0, hx0⟩ := hex
  have hpos : 0 < ∫ x, g x :=
    Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero gcont
      (HasCompactSupport.of_compactSpace g) gnn hx0
  have hK : 0 < s ^ 2 * sphereArea d / (d * (d + 2)) := by
    have : (0 : ℝ) < d := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    have := StaticLimitsAux.sphereArea_pos hd
    positivity
  exact mul_pos hK hpos

/-- Proposition 7.17, `E:eq:L2-asymptotics`, critical case `s = d/2`:
`‖h°_{φ,ε}‖²_{L²(μ^{⊗2})} = J_{φ,ρ} log(1/ε) + O(1)` as `ε ↓ 0`. -/
theorem localDiv_critical {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (ρ : Torus d → ℝ)
    (hρ : SmoothPosDensity ρ) (φ : Torus d → ℝ) (hφ : Torus.IsSmooth φ)
    (hnc : ∃ x y, φ x ≠ φ y) :
    ∃ C ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) ε₀,
      |∫ p : Torus d × Torus d,
          canonicalCenter (withDensityReal ρ) (hCut d s φ ε) p.1 p.2 ^ 2
            ∂((withDensityReal ρ).prod (withDensityReal ρ)) -
        localDivCoeff d s ρ φ * Real.log (1 / ε)| ≤ C := by
  obtain ⟨C, ε₀, hε₀, H⟩ := LocalDivAux.critical_main hd hcrit hρ hφ
  exact ⟨C, ε₀, hε₀, H⟩

/-- Proposition 7.17, `E:eq:L2-asymptotics`, supercritical case `d/2 < s < d`:
`‖h°_{φ,ε}‖²_{L²(μ^{⊗2})} = J_{φ,ρ}/(2s-d) ε^{d-2s} (1 + o(1))`. -/
theorem localDiv_supercritical {s : ℝ} (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (φ : Torus d → ℝ) (hφ : Torus.IsSmooth φ)
    (hnc : ∃ x y, φ x ≠ φ y) :
    Tendsto (fun ε => (∫ p : Torus d × Torus d,
          canonicalCenter (withDensityReal ρ) (hCut d s φ ε) p.1 p.2 ^ 2
            ∂((withDensityReal ρ).prod (withDensityReal ρ))) /
        (localDivCoeff d s ρ φ / (2 * s - d) * ε ^ ((d : ℝ) - 2 * s)))
      (𝓝[>] 0) (𝓝 1) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by linarith
  exact LocalDivAux.supercritical_main hd hs hsd hρ hφ (localDivCoeff_pos hd hs0 hsd ρ hρ φ hφ hnc)

/-- Proposition 7.17, last two sentences (source lines 9684-9686): for `0 ≤ s < d/2`,
`h_φ ∈ L²(μ^{⊗2})` and the canonical cutoffs `h°_{φ,ε}` converge in `L²(μ^{⊗2})` (to the
canonical centering of `h_φ`); `s = 0` is included (bounded kernel near the diagonal). -/
theorem localDiv_subcritical {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (φ : Torus d → ℝ) (hφ : Torus.IsSmooth φ) :
    MemLp (fun p : Torus d × Torus d => hTransport d s φ p.1 p.2) 2
        ((withDensityReal ρ).prod (withDensityReal ρ)) ∧
      Tendsto (fun ε => eLpNorm (fun p : Torus d × Torus d =>
          canonicalCenter (withDensityReal ρ) (hCut d s φ ε) p.1 p.2 -
            canonicalCenter (withDensityReal ρ) (hTransport d s φ) p.1 p.2) 2
          ((withDensityReal ρ).prod (withDensityReal ρ))) (𝓝[>] 0) (𝓝 0) := by
  exact ⟨LocalDivAux.sub_memLp hd hs0 hs hρ hφ, LocalDivAux.sub_conv hd hs0 hs hρ hφ⟩

/-! ### Proposition 2.4: mutual singularity of field laws -/

/-- The covariance of a field law `γ` on `H^{-m}_0` is comparable to `‖·‖²_{L²(dx)}` on smooth
zero-Haar-mean functions (hypothesis of Proposition 2.4, source lines 703-705). -/
def HasL2ComparableCov (m : ℝ) (γ : Measure (NegSobolev d m)) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ ∀ φ : Torus d → ℝ, Torus.IsSmooth φ → Torus.mean φ = 0 →
    c * ∫ x, φ x ^ 2 ≤ ∫ F, NegSobolev.eval F φ ^ 2 ∂γ ∧
      ∫ F, NegSobolev.eval F φ ^ 2 ∂γ ≤ C * ∫ x, φ x ^ 2

/-- Proposition 2.4 `M:H:prop:field-singularity` (source lines 701-708): for `m > d/2`, a centred
Gaussian law `γ` on `H^{-m}_0` with `L²`-comparable covariance is mutually singular with the law
of `√N(μ_N - ν_N)` for every `N`, every particle law and every probability measure `ν_N`.
`hd : 1 ≤ d` excludes the point torus `d = 0`, where the statement is false; the source works
under the standing assumption `d ≥ 2` (M L419), so this is weaker than inherited (`docs/ISSUES.md` §E). -/
theorem field_singularity (hd : 1 ≤ d) (m : ℝ) (hm : (d : ℝ) / 2 < m) (γ : Measure (NegSobolev d m))
    [IsProbabilityMeasure γ] (hγ : IsCenteredGaussian γ) (hcov : HasL2ComparableCov m γ)
    (N : ℕ) (P : Measure (Config d N)) [IsProbabilityMeasure P] (ν : Measure (Torus d))
    [IsProbabilityMeasure ν] :
    γ ⟂ₘ law P (fun X => Real.sqrt N • NegSobolev.ofMeasureDiff m (empirical X) ν) := by
  obtain ⟨c, C, hc, H⟩ := hcov
  exact FieldSingAux.field_singularity_main hd hm γ hγ c hc (fun φ h1 h2 => (H φ h1 h2).1) N P ν

/-- Proposition 2.4, last sentence (source lines 708-709): the susceptibility Gaussian of a
smooth strictly positive density has `L²`-comparable covariance. -/
theorem susceptibility_hasL2ComparableCov {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (m : ℝ) (hm : (d : ℝ) / 2 < m) (β : ℝ) (hβ : 0 ≤ β) (ρ : Torus d → ℝ)
    (hρ : SmoothPosDensity ρ) (γ : Measure (NegSobolev d m))
    (hγ : IsCenteredGaussianWithCov m γ
      (susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β)) :
    HasL2ComparableCov m γ := by
  obtain ⟨c, C, hc, H⟩ := StaticLimitsAux.comparable_of_susc hd hs0 hsd β hβ hρ
  refine ⟨c, C, hc, fun φ hφ h0 => ?_⟩
  have e := hγ.2 φ φ hφ hφ
  simp only [← sq] at e
  rw [e]
  exact H φ hφ h0

/-! ### Examples 5.11 and 5.12: conditioned and tilted equilibrium samples -/

/-- `Z_N = ⟨ψ, η_N⟩ = √N(μ_N(ψ) - μ_β(ψ))` (source line 7094). -/
def linCoord {N : ℕ} (μ : Measure (Torus d)) (ψ : Torus d → ℝ) (X : Config d N) : ℝ :=
  Real.sqrt N * ((1 / (N : ℝ)) * ∑ i, ψ (X i) - pair μ ψ)

/-- The half-normal density `√(2/(πv)) e^{-z²/(2v)} 1_{z>0}` (`A:eq:half-normal`). -/
def halfNormalDensity (v z : ℝ) : ℝ :=
  if 0 < z then Real.sqrt (2 / (Real.pi * v)) * Real.exp (-z ^ 2 / (2 * v)) else 0

/-- The cosine-tilted Gaussian density `(1 + a cos z)/(1 + a e^{-v/2}) · e^{-z²/(2v)}/√(2πv)`
(`A:eq:cosine-density`). -/
def cosineTiltDensity (a v z : ℝ) : ℝ :=
  (1 + a * Real.cos z) / (1 + a * Real.exp (-v / 2)) *
    (Real.exp (-z ^ 2 / (2 * v)) / Real.sqrt (2 * Real.pi * v))

/-- Example 5.11 `M:A:ex:conditioned` (source lines 7092-7104), general part: for a smooth
nonconstant `ψ`, `v = C_β(ψ,ψ) > 0`, `P_{N,β}(Z_N > 0) → 1/2`, and the law of `Z_N` under
`P_{N,β}(· | Z_N > 0)` converges (against bounded continuous tests) to the half-normal law.
The source derives the convergence of `Z_N = ⟨ψ, η_N⟩` from Theorem 2.9, which centres at the
exact marginal; the mean-field centering used here has the same limit only for `s < 2d/3`
(source lines 989-991), which is therefore assumed (see the report). -/
theorem conditioned_example {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < 2 * (d : ℝ) / 3)
    (β : ℝ) (hβ : 0 < β) (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρ : Torus d → ℝ)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (ψ : Torus d → ℝ) (hψ : Torus.IsSmooth ψ)
    (hnc : ∃ x y, ψ x ≠ ψ y) :
    0 < susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β ψ ψ ∧
    Tendsto (fun N => (canonicalGibbs (periodicRiesz d s) V N β
        {X | 0 < linCoord (withDensityReal ρ) ψ X}).toReal) atTop (𝓝 (1 / 2)) ∧
    ∀ f : ℝ → ℝ, Continuous f → (∃ M, ∀ z, |f z| ≤ M) →
      Tendsto (fun N => ∫ X, f (linCoord (withDensityReal ρ) ψ X)
          ∂(ProbabilityTheory.cond (canonicalGibbs (periodicRiesz d s) V N β)
            {X | 0 < linCoord (withDensityReal ρ) ψ X})) atTop
        (𝓝 (∫ z, f z * halfNormalDensity
          (susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β ψ ψ) z)) := by
  sorry

/-- Example 5.11, explicit homogeneous case (source lines 7105-7113): `V = 0`,
`ψ(x) = √2 cos(2π x_1)`. Then `P_{N,β}(Z_N > 0) = 1/2` for every `N ≥ 1` (so the conditioned
density is exactly `2·1_{Z_N > 0}`), and `v = 1/(1 + β c_{d,s} (2π)^{s-d})` (`A:eq:explicit-variance`). -/
theorem conditioned_example_explicit {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ)
    (hβ : 0 < β) (N : ℕ) (hN : 1 ≤ N) :
    (canonicalGibbs (periodicRiesz d s) (fun _ => 0) N β
        {X | 0 < linCoord volume
          (fun x => Real.sqrt 2 * Torus.cosMode (Pi.single ⟨0, by omega⟩ 1) x) X}).toReal = 1 / 2 ∧
      susceptibilityCov (periodicRiesz d s) volume β
          (fun x => Real.sqrt 2 * Torus.cosMode (Pi.single ⟨0, by omega⟩ 1) x)
          (fun x => Real.sqrt 2 * Torus.cosMode (Pi.single ⟨0, by omega⟩ 1) x) =
        1 / (1 + β * rieszConst d s * (2 * Real.pi) ^ (s - d)) := by
  constructor
  · obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    have h := StaticLimitsAux.prob_cos hd hs0 hsd β hβ.le (⟨0, by omega⟩ : Fin d) n
    unfold linCoord
    exact h
  · have h := StaticLimitsAux.susc_cos hd hs0 hsd β hβ (⟨0, by omega⟩ : Fin d)
    rw [h, StaticLimitsAux.rieszCoeff_single, mul_assoc]

/-- Example 5.12 `M:A:ex:cosine` (source lines 7139-7155), general setting of Example 5.11:
for `0 < |a| < 1` the tilt density `(1 + a cos Z_N)/E[1 + a cos Z_N]` is bounded above and below
uniformly in `N` (by `(1+|a|)/(1-|a|)` and its inverse), the law of `Z_N` under the tilted law
converges to the density `A:eq:cosine-density`, and this limit is not Gaussian. -/
theorem cosine_tilt_example {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < 2 * (d : ℝ) / 3)
    (β : ℝ) (hβ : 0 < β) (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρ : Torus d → ℝ)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (ψ : Torus d → ℝ) (hψ : Torus.IsSmooth ψ)
    (hnc : ∃ x y, ψ x ≠ ψ y) (a : ℝ) (ha0 : a ≠ 0) (ha1 : |a| < 1) :
    (∀ N : ℕ, ∀ X : Config d N,
      (1 - |a|) / (1 + |a|) ≤ (1 + a * Real.cos (linCoord (withDensityReal ρ) ψ X)) /
          ∫ Y, (1 + a * Real.cos (linCoord (withDensityReal ρ) ψ Y))
            ∂(canonicalGibbs (periodicRiesz d s) V N β) ∧
        (1 + a * Real.cos (linCoord (withDensityReal ρ) ψ X)) /
          ∫ Y, (1 + a * Real.cos (linCoord (withDensityReal ρ) ψ Y))
            ∂(canonicalGibbs (periodicRiesz d s) V N β) ≤ (1 + |a|) / (1 - |a|)) ∧
    (∀ f : ℝ → ℝ, Continuous f → (∃ M, ∀ z, |f z| ≤ M) →
      Tendsto (fun N => ∫ X, f (linCoord (withDensityReal ρ) ψ X) *
          ((1 + a * Real.cos (linCoord (withDensityReal ρ) ψ X)) /
            ∫ Y, (1 + a * Real.cos (linCoord (withDensityReal ρ) ψ Y))
              ∂(canonicalGibbs (periodicRiesz d s) V N β))
          ∂(canonicalGibbs (periodicRiesz d s) V N β)) atTop
        (𝓝 (∫ z, f z * cosineTiltDensity a
          (susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β ψ ψ) z))) ∧
    (∀ (m : ℝ) (w : ℝ≥0), volume.withDensity (fun z => ENNReal.ofReal (cosineTiltDensity a
        (susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β ψ ψ) z)) ≠
      gaussianReal m w) := by
  sorry

/-! ### Lemma 7.5: joint centered quadratic limit (`s < d/2`) -/

/-- `(e_i)` is an orthonormal basis of `L²_0(μ)`: square integrable, centred, orthonormal, and
complete (a centred `L²` function orthogonal to every `e_i` vanishes a.e.). -/
structure IsONBL2Zero (μ : Measure (Torus d)) (e : ℕ → Torus d → ℝ) : Prop where
  memLp : ∀ i, MemLp (e i) 2 μ
  centered : ∀ i, ∫ x, e i x ∂μ = 0
  orthonormal : ∀ i j, l2Inner μ (e i) (e j) = if i = j then 1 else 0
  complete : ∀ f : Torus d → ℝ, MemLp f 2 μ → ∫ x, f x ∂μ = 0 →
    (∀ i, l2Inner μ f (e i) = 0) → f =ᵐ[μ] 0

/-- Lemma 7.5 `M:N:lem:quadratic-limit` (source lines 7956-7966): `s < d/2`, `Q_{N,β}(μ)` with a
smooth positive background, `w = g + c_* ≥ 1` off zero, `h` symmetric with `|h| ≤ B w`,
`B_N(h) = N(F_N^h - E F_N^h)`. Jointly with the exactly centred linear statistics
`√N(μ_N(φ_a) - m_N(φ_a))` of finitely many bounded tests, `B_N(h)` converges to
`½ I_2^{R_{β,μ}}(H_μ)`, and mixed expectations against bounded continuous functions converge.
The limit is described on a probability space carrying `G_i = G(e_i)`, jointly Gaussian with
covariance `C_{β,μ}(e_i, e_j) = ⟨e_i, R_{β,μ} e_j⟩` along an orthonormal basis `(e_i)` of
`L²_0(μ)`; `G(φ_a)` is the `L²` limit of `∑_{i<L} ⟨φ_a, e_i⟩ G_i`, and the chaos
`Q = ½ I_2^R(H_μ)` is the `L²` limit of `½ ∑_{i,j<L} ⟨e_i, H_μ e_j⟩ (G_i G_j - C(e_i,e_j))`
(this equals `½ I_2(R^{1/2} H_μ R^{1/2})`, `N:eq:second-chaos-definition`). -/
theorem quadratic_limit {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (β : ℝ)
    (hβ : 0 < β) (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (c : ℝ)
    (hc : ∀ z, z ≠ 0 → 1 ≤ periodicRiesz d s z + c) (B : ℝ) (h : Torus d → Torus d → ℝ)
    (hmeas : Measurable (Function.uncurry h)) (hsymm : ∀ x y, h x y = h y x)
    (hB : ∀ x y, x ≠ y → |h x y| ≤ B * (periodicRiesz d s (x - y) + c))
    (e : ℕ → Torus d → ℝ) (he : IsONBL2Zero (withDensityReal ρ) e)
    (p : ℕ) (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, Measurable (φ a) ∧ ∃ M, ∀ x, |φ a x| ≤ M) :
    (∀ N : ℕ, 1 ≤ N → Integrable (fun X : Config d N => modulatedEnergy h X (withDensityReal ρ))
      (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))) ∧
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (G : ℕ → Ω → ℝ) (Q : Ω → ℝ) (Lin : Fin p → Ω → ℝ),
      (∀ n : ℕ, law P (fun ω => (WithLp.toLp 2 fun i : Fin n => G i ω : EuclideanSpace ℝ (Fin n))) =
        multivariateGaussian 0 (Matrix.of fun i j : Fin n =>
          susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j))) ∧
      (∀ a, Tendsto (fun L => ∫⁻ ω, ‖Lin a ω - ∑ i ∈ Finset.range L,
          l2Inner (withDensityReal ρ) (φ a) (e i) * G i ω‖ₑ ^ 2 ∂P) atTop (𝓝 0)) ∧
      Tendsto (fun L => ∫⁻ ω, ‖Q ω - (1 / 2) * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
          (∫ x, ∫ y, h x y * e i x * e j y ∂(withDensityReal ρ) ∂(withDensityReal ρ)) *
            (G i ω * G j ω -
              susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j))‖ₑ ^ 2 ∂P)
        atTop (𝓝 0) ∧
      ∀ F : ℝ × (Fin p → ℝ) → ℝ, Continuous F → (∃ M, ∀ z, |F z| ≤ M) →
        Tendsto (fun N : ℕ => ∫ X, F ((N : ℝ) * (modulatedEnergy h X (withDensityReal ρ) -
              ∫ Y, modulatedEnergy h Y (withDensityReal ρ)
                ∂(modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))),
            fun a => Real.sqrt N * ((1 / (N : ℝ)) * ∑ i, φ a (X i) -
              pair (firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)))
                (φ a)))
            ∂(modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))) atTop
          (𝓝 (∫ ω, F (Q ω, fun a => Lin a ω) ∂P)) := by
  sorry

end HRS

end
