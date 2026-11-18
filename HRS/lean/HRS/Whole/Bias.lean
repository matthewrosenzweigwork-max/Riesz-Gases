import HRS.Whole.Static
import HRS.Whole.Thermal
import HRS.Equilibrium.PoleCavity
import HRS.Whole.Q34Aux1
import HRS.Whole.Q34Aux2
import HRS.Whole.Q34Aux3
import HRS.Whole.Q34Aux4
import HRS.Whole.Q34Aux5
import HRS.Whole.Q34Aux6
import HRS.Whole.Q34Aux7
import HRS.Whole.Q34Aux8
import HRS.Whole.Q34Aux18

/-!
# The whole-space marginal bias (spec packet SPEC-W3): Section S7

Source: HRS whole-space supplement (S), Section S7 (`S:sec:bias`), standing hypotheses
S lines 5267-5312: `d ≥ 2`, `d/2 < s < d`, `g(x) = |x|^{-s}`, `p = d/s ∈ (1,2)`,
`δ_N = N^{1-p}`, `A_{d,s} = |S^{d-1}| Γ(2-p) / (2 s p (p-1))` (`S:eq:parameters`); "no factor
`1/s` in `g` and no periodic zero-mode convention"; `μ = ρ dx` a probability measure with
`ρ ∈ W^{1,∞}(ℝ^d)` (bounded Lipschitz representative), no positive lower bound; the modulated
law `S:eq:modulated-law` with `m_N = Q^{(1)} = E[μ_N]`; the response operators
`S:eq:response`; the bias measure `S:eq:bias-measure` `b_{β,μ} = 2A β^p (R_{β,μ}P_μρ) μ`;
the exponent `S:eq:remainder-exponent`.  Section S7.2 (S lines 5380-5394): `n = N-1`,
`λ = β/N`, cavity laws `S:eq:cavity-laws`, `ν_n = (P_n^0)^{(1)}`.

* S7.1 `S:thm:sharp-bias` (S lines 5314-5338) with `S:eq:sharp-statistic`,
  `S:eq:test-remainder`, and the "Quadratic confinement" paragraph (5349-5357).
* S7.2 `S:prop:static-input` (5396-5417).
* S7.3 `S:lem:convolution` (5462-5488).
* S7.4 `S:prop:conditional-density` (5560-5578), `τ` `S:eq:tau` (5551), `u_Y`
  `S:eq:conditional-potential` (5555).
* S7.5 `S:lem:compensated-kernel` (5703-5715).
* S7.6 `S:prop:sharp-insertion` (5738-5753), `F_{N,x}`, `D_N` `S:eq:insertion-definition`
  (5673-5676).
* S7.7 `S:cor:weighted-remainder` (5924-5939).
* S7.8 `S:cor:sharp-threshold` (6011-6032).
(S7.9 `S:cor:shifted-field-path` is in `HRS/Whole/Critical.lean`, because it needs the dynamics.)

## Representation decisions

* `δ_N = N^{1-p}` is `HRS.deltaN d s N` (equal to `N^{1-d/s}` for `s > d/2`, `deltaN_eq_bias`).
* `|S^{d-1}|` is the existing `HRS.sphereArea` (`HRS/Equilibrium/PoleCavity.lean`).
* The derivative `F'_{N,x}(0)` in `D_N` is the right derivative `derivWithin … (Ici 0) 0`
  (for `t < 0` the tilt need not be integrable); its existence is part of S7.6's claim, and so is
  the well-definedness of the pole laws for `t ∈ [0,1]` (otherwise `log` of a junk-valued
  normaliser would make the derivative statement vacuous).
* Total variation uses the source's convention `sup_E |ν(E) - ν'(E)|` (`tvDist`).
* Radon–Nikodym bounds for the pole marginals are measure inequalities
  `P^{(1)} ≤ μ.withDensity (C e^{-tλ g(x-·)})`, which include absolute continuity.
* Variances are `ProbabilityTheory.evariance` (`ℝ≥0∞`); the variance bound of S7.2 carries the
  source's proviso "when its displayed integral is finite" as a hypothesis.
* Constants depend only on the displayed parameters; they are quantified before the objects
  they must not depend on.  For S7.1 the two uniformity assertions of the source (dependence
  on `d, s, β, ‖ρ‖_∞, ‖∇ρ‖_∞` only; uniformity in `β` on compact subintervals for a fixed
  background) are two theorems.  `‖∇ρ‖_∞` is a Lipschitz constant `Λ` (`LipschitzWith Λ ρ`); a bound
  stated for every admissible `Λ` is equivalent to the one for the best constant `‖∇ρ‖_∞`.
* Signed measures (S7.7) are Mathlib's `SignedMeasure`; `|r|` is `SignedMeasure.totalVariation`.
  The finiteness of the measures involved (instances) is carried as `[IsProbabilityMeasure …]`
  hypotheses; it is part of the conclusion of S7.1 (well-definedness of the law).
* "Convergence in distribution" in varying probability spaces (S7.8) is stated through
  `∫ f d(·) → ∫ f dγ` for every bounded continuous `f`, which is weak convergence of the laws.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff BoundedContinuousFunction

namespace HRS.Whole

variable {d N : ℕ}

/-! ### Parameters `S:eq:parameters` -/

/-- `p = d/s` (S line 5269). -/
def biasP (d : ℕ) (s : ℝ) : ℝ := d / s

/-- `A_{d,s} = |S^{d-1}| Γ(2-p) / (2 s p (p-1))` (S line 5271). -/
def biasConst (d : ℕ) (s : ℝ) : ℝ :=
  sphereArea d * Real.Gamma (2 - biasP d s) / (2 * s * biasP d s * (biasP d s - 1))

/-- `θ_{d,s} = min{(p-1)²/p, (2-p)/8, 3/(4s)}` (`S:eq:remainder-exponent`, S lines 5309-5310). -/
def biasTheta (d : ℕ) (s : ℝ) : ℝ :=
  min ((biasP d s - 1) ^ 2 / biasP d s) (min ((2 - biasP d s) / 8) (3 / (4 * s)))

/-- `τ = (p-1)²/p` (`S:eq:tau`, S line 5551). -/
def biasTau (d : ℕ) (s : ℝ) : ℝ := (biasP d s - 1) ^ 2 / biasP d s

/-- `M_g = M|S^{d-1}|/(d-s) + 1` (`S:eq:bounded-potential`, S line 5467). -/
def potentialBound (d : ℕ) (s M : ℝ) : ℝ := M * sphereArea d / ((d : ℝ) - s) + 1

/-- The density `db_{β,μ}/dμ = 2A_{d,s} β^p R_{β,μ}P_μρ` of the bias measure
(`S:eq:bias-measure`, S lines 5300-5302), with `R_{β,μ}P_μρ = responseInverse`. -/
def biasDensity (d : ℕ) (s β : ℝ) (ρ : Euc d → ℝ) (x : Euc d) : ℝ :=
  2 * biasConst d s * β ^ biasP d s * responseInverse (rieszKernel d s) (withDensityReal ρ) β ρ x

/-- Auxiliary: `δ_N = N^{1-p}` for `d/2 < s` (S line 5270; unfolds `deltaN`). -/
theorem deltaN_eq_bias {s : ℝ} (hs : (d : ℝ) / 2 < s) (N : ℕ) :
    deltaN d s N = (N : ℝ) ^ (1 - biasP d s) := by
  sorry

/-- Auxiliary: `θ_{d,s} > 0` for `d/2 < s < d` (S line 5310). -/
theorem biasTheta_pos {s : ℝ} (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) :
    0 < biasTheta d s := by
  sorry

/-! ### Cavity and pole laws `S:eq:cavity-laws` (S lines 5383-5394) -/

/-- The cavity weight `exp(-λ∑_{i<j} g(y_i-y_j) + β∑_i (g*μ)(y_i))`, `λ = β/N`, on
`(ℝ^d)^{N-1}`. -/
def cavityWeight (d : ℕ) (s : ℝ) (N : ℕ) (β : ℝ) (μ : Measure (Euc d))
    (Y : EucConfig d (N - 1)) : ℝ :=
  Real.exp (-(β / N) * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
      rieszKernel d s (Y i - Y j) +
    β * ∑ i, convMeasure (rieszKernel d s) μ (Y i))

/-- The cavity normaliser `∫ cavityWeight dμ^{⊗(N-1)}`. -/
def cavityNormalizer (d : ℕ) (s : ℝ) (N : ℕ) (β : ℝ) (μ : Measure (Euc d)) : ℝ :=
  ∫ Y : EucConfig d (N - 1), cavityWeight d s N β μ Y ∂(Measure.pi fun _ => μ)

/-- The cavity law `P_n^0 ∝ e^{-λ∑_{i<j} g(y_i-y_j) + β∑_i (g*μ)(y_i)} μ^{⊗n}`, `n = N-1`. -/
def cavityLaw (d : ℕ) (s : ℝ) (N : ℕ) (β : ℝ) (μ : Measure (Euc d)) :
    Measure (EucConfig d (N - 1)) :=
  (ENNReal.ofReal (cavityNormalizer d s N β μ))⁻¹ •
    (Measure.pi fun _ => μ).withDensity fun Y => ENNReal.ofReal (cavityWeight d s N β μ Y)

/-- The pole tilt `e^{-tλ∑_i g(x-y_i)}`. -/
def poleWeight (d : ℕ) (s : ℝ) (N : ℕ) (β : ℝ) (x : Euc d) (t : ℝ)
    (Y : EucConfig d (N - 1)) : ℝ :=
  Real.exp (-(t * (β / N)) * ∑ i, rieszKernel d s (x - Y i))

/-- `P_n^0[e^{-tλ∑_i g(x-y_i)}]`. -/
def poleNormalizer (d : ℕ) (s : ℝ) (N : ℕ) (β : ℝ) (μ : Measure (Euc d)) (x : Euc d)
    (t : ℝ) : ℝ :=
  ∫ Y, poleWeight d s N β x t Y ∂(cavityLaw d s N β μ)

/-- The pole law `P_n^{x,t} = e^{-tλ∑ g(x-y_i)} / P_n^0[…] · P_n^0`, `x ∈ ℝ^d`, `0 ≤ t ≤ 1`. -/
def poleLaw (d : ℕ) (s : ℝ) (N : ℕ) (β : ℝ) (μ : Measure (Euc d)) (x : Euc d) (t : ℝ) :
    Measure (EucConfig d (N - 1)) :=
  (ENNReal.ofReal (poleNormalizer d s N β μ x t))⁻¹ •
    (cavityLaw d s N β μ).withDensity fun Y => ENNReal.ofReal (poleWeight d s N β x t Y)

/-- `ν_n = (P_n^0)^{(1)}` (S line 5394). -/
def cavityMarginal (d : ℕ) (s : ℝ) (N : ℕ) (β : ℝ) (μ : Measure (Euc d)) : Measure (Euc d) :=
  firstMarginal (cavityLaw d s N β μ)

/-- Well-definedness of the cavity and pole laws: weights integrable, normalisers positive. -/
structure CavityWellDefined (d : ℕ) (s : ℝ) (N : ℕ) (β : ℝ) (μ : Measure (Euc d)) (x : Euc d)
    (t : ℝ) : Prop where
  cavity_integrable : Integrable (cavityWeight d s N β μ) (Measure.pi fun _ => μ)
  cavity_pos : 0 < cavityNormalizer d s N β μ
  pole_integrable : Integrable (poleWeight d s N β x t) (cavityLaw d s N β μ)
  pole_pos : 0 < poleNormalizer d s N β μ x t

/-- Total variation distance with the convention `sup_E |ν(E) - ν'(E)|` (S line 5416). -/
def tvDist {α : Type*} [MeasurableSpace α] (ν ν' : Measure α) : ℝ :=
  ⨆ E : {E : Set α // MeasurableSet E}, |(ν E.1).toReal - (ν' E.1).toReal|

/-! ### S7.2 `S:prop:static-input` (S lines 5396-5417) -/

section StaticInput

variable {s : ℝ}

/-- The conclusions of Proposition S7.2 for one `N` and one constant `C` (S lines 5399-5417):
the law `S:eq:modulated-law` is well defined; `S:eq:input-marginal`
(`‖dm_N/dμ - 1‖_{L²(μ)} ≤ Cδ_N`, `dm_N/dμ ≤ C`, `N Var[μ_N(f)] ≤ C‖f‖²_{L²(μ)}`); the pole
density bounds `S:eq:input-pole-one`, `S:eq:input-pole-two` (the latter used only for `n ≥ 2`);
the pole variance bound `S:eq:input-pole-variance` (when its displayed integral is finite); the
cavity total-variation bound `S:eq:input-cavity-TV` `‖m_N - ν_n‖_TV ≤ C√(δ_N/N)`.  The pole
laws are asserted well defined for `x ∈ ℝ^d`, `t ∈ [0,1]`. -/
def StaticInputConclusion (d : ℕ) (s : ℝ) (N : ℕ) (β : ℝ) (ρ : Euc d → ℝ) (C : ℝ) : Prop :=
  GibbsWellDefined (fun x y => rieszKernel d s (x - y)) N β (withDensityReal ρ) ∧
  HasMarginalDensityBounds
    (firstMarginal (modulatedGibbs (rieszKernel d s) N β (withDensityReal ρ)))
    (withDensityReal ρ) C (C * deltaN d s N) ∧
  (∀ f : Euc d → ℝ, MemLp f 2 (withDensityReal ρ) →
    ProbabilityTheory.evariance (linStat f)
      (modulatedGibbs (rieszKernel d s) N β (withDensityReal ρ)) ≤
      ENNReal.ofReal (C / N * ∫ x, f x ^ 2 ∂(withDensityReal ρ))) ∧
  (∀ (x : Euc d), ∀ t ∈ Set.Icc (0 : ℝ) 1,
    CavityWellDefined d s N β (withDensityReal ρ) x t ∧
    firstMarginal (poleLaw d s N β (withDensityReal ρ) x t) ≤
      (withDensityReal ρ).withDensity
        (fun y => ENNReal.ofReal (C * Real.exp (-(t * (β / N)) * rieszKernel d s (x - y)))) ∧
    (3 ≤ N → secondMarginal (poleLaw d s N β (withDensityReal ρ) x t) ≤
      ((withDensityReal ρ).prod (withDensityReal ρ)).withDensity
        (fun yz => ENNReal.ofReal (C * Real.exp (-(t * (β / N)) *
          (rieszKernel d s (x - yz.1) + rieszKernel d s (x - yz.2)))))) ∧
    ∀ f : Euc d → ℝ, Measurable f →
      Integrable (fun y => |f y| ^ 2 * Real.exp (-(t * (β / N)) * rieszKernel d s (x - y)))
        (withDensityReal ρ) →
      ProbabilityTheory.evariance (fun Y : EucConfig d (N - 1) => ∑ i, f (Y i))
        (poleLaw d s N β (withDensityReal ρ) x t) ≤
        ENNReal.ofReal (C * (N - 1) *
          ∫ y, |f y| ^ 2 * Real.exp (-(t * (β / N)) * rieszKernel d s (x - y))
            ∂(withDensityReal ρ))) ∧
  tvDist (firstMarginal (modulatedGibbs (rieszKernel d s) N β (withDensityReal ρ)))
    (cavityMarginal d s N β (withDensityReal ρ)) ≤ C * Real.sqrt (deltaN d s N / N)

/-- Proposition S7.2 (S:S:prop:static-input, TeX S L5396-5417) (S lines 5396-5417): under the bounded-density
hypothesis (`d ≥ 2`, `d/2 < s < d`, `β > 0` fixed, `μ = ρ dx` a probability measure with
`‖ρ‖_∞ ≤ M`), with constants independent of `x, t, N` (and of `ρ` beyond `M`: the standing
hypotheses of S7, S lines 5267-5312, make `M` the only density datum; this is how S3.3 `euc_static`
is quantified).  Technical hypothesis: `N ≥ 2` (`n = N-1 ≥ 1` cavity particles). -/
theorem static_input (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) (β M : ℝ)
    (hβ : 0 < β) :
    ∃ C : ℝ, ∀ ρ : Euc d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ M) → ∀ N, 2 ≤ N →
      StaticInputConclusion d s N β ρ C := by
  sorry

/-- Proposition S7.2 (S:S:prop:static-input, TeX S L5396-5417), uniformity in `β` (S lines 924-926, the S3.3 source of these inputs, quoted at
S lines 5399-5401): the same constant works for `β` in a compact subinterval `[βm,βp] ⊂ (0,∞)`. -/
theorem static_input_uniform_beta (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d)
    (βm βp M : ℝ) (hβm : 0 < βm) (hβ : βm ≤ βp) :
    ∃ C : ℝ, ∀ ρ : Euc d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ M) → ∀ β ∈ Set.Icc βm βp,
      ∀ N, 2 ≤ N → StaticInputConclusion d s N β ρ C := by
  sorry

end StaticInput

/-! ### S7.3 `S:lem:convolution` (S lines 5462-5488) -/

section Convolution

variable {s : ℝ}

/-- `g_H = min{g, H}` (S line 5476). -/
def truncKernel (d : ℕ) (s H : ℝ) (z : Euc d) : ℝ := min (rieszKernel d s z) H

/-- Lemma S7.3 (S:S:lem:convolution, TeX S L5462-5488), `S:eq:bounded-potential` (S lines 5464-5468): `sup_x (g*μ)(x) ≤ M_g`
(and the convolution integral converges), for a probability density with `‖ρ‖_∞ ≤ M`,
`d ≥ 2`, `d/2 < s < d`. -/
theorem convolution_bounded_potential (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d)
    (ρ : Euc d → ℝ) (hρ : IsProbDensity ρ) (M : ℝ) (hM : ∀ x, ρ x ≤ M) (x : Euc d) :
    Integrable (fun y => rieszKernel d s (x - y)) (withDensityReal ρ) ∧
      convMeasure (rieszKernel d s) (withDensityReal ρ) x ≤ potentialBound d s M := by
  have hd1 : 1 ≤ d := by omega
  have hs0 : 0 < s := by
    have : (1 : ℝ) ≤ d / 2 := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    linarith
  have hM0 : 0 ≤ M := (hρ.nonneg 0).trans (hM 0)
  have hL := Q34.lintegral_kernel_le hd1 hs0 hsd hρ hM x
  have hrk : ∀ z : Euc d, rieszKernel d s z = ‖z‖ ^ (-s) := Q34.rieszKernel_eq hs0.ne'
  have hnn : ∀ y : Euc d, 0 ≤ rieszKernel d s (x - y) := fun y => by
    rw [hrk]; exact Real.rpow_nonneg (norm_nonneg _) _
  have hmeas : Measurable (fun y : Euc d => rieszKernel d s (x - y)) :=
    (Q34.measurable_rieszKernel hs0.ne').comp (measurable_const.sub measurable_id)
  have hpos : 0 ≤ M * sphereArea d / ((d : ℝ) - s) + 1 := by
    have := Q34.sphereArea_nonneg hd1
    have : 0 < (d : ℝ) - s := by linarith
    positivity
  have hL' : ∫⁻ y, ENNReal.ofReal (rieszKernel d s (x - y)) ∂(withDensityReal ρ) ≤
      ENNReal.ofReal (M * sphereArea d / ((d : ℝ) - s) + 1) := by
    simpa only [hrk] using hL
  exact Q34.integrable_of_lintegral_le hmeas hnn hpos hL'

/-- Lemma S7.3 (S:S:lem:convolution, TeX S L5462-5488), `S:eq:conv-infty` (S lines 5469-5471): if `|f| ≤ B` and `‖f‖_1 ≤ ε ≤ 1` then
`‖g*f‖_∞ ≤ C_B ε^{1-s/d}`; `C_B` depends on `d, s, B` only (quantified before `f`).  The
convolution integrals are asserted absolutely convergent.  Technical hypothesis: `f` measurable
and integrable (`‖f‖_1` is the Lebesgue integral of `|f|`). -/
theorem convolution_sup_bound (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) (B : ℝ) :
    ∃ CB : ℝ, ∀ f : Euc d → ℝ, Measurable f → (∀ x, |f x| ≤ B) → Integrable f →
      ∀ ε : ℝ, ε ≤ 1 → ∫ x, |f x| ≤ ε →
        (∀ x, Integrable (fun y => rieszKernel d s (x - y) * f y)) ∧
        ∀ x, |convFun (rieszKernel d s) f x| ≤ CB * ε ^ (1 - s / d) := by
  have hd1 : 1 ≤ d := by omega
  have hs0 : 0 < s := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hrk : ∀ z : Euc d, rieszKernel d s z = ‖z‖ ^ (-s) := Q34.rieszKernel_eq hs0.ne'
  obtain ⟨CB, hCB⟩ := Q34.sup_bound hd1 hs0 hsd B
  refine ⟨CB, fun f hf hB hfi ε hε1 hε => ?_⟩
  simpa only [convFun, hrk] using hCB f hf hB hfi ε hε1 hε

/-- Lemma S7.3 (S:S:lem:convolution, TeX S L5462-5488), `S:eq:conv-two` (S lines 5469-5475): under the same hypotheses,
`‖g*f‖_{L²(μ)} ≤ C_{B,M} ε^{3/2-s/d}` for every probability density `ρ` with `‖ρ‖_∞ ≤ M`
(`μ = ρ dx`); `C_{B,M}` depends on `d, s, B, M` (quantified before `f` and `ρ`). -/
theorem convolution_l2_bound (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) (B M : ℝ) :
    ∃ CBM : ℝ, ∀ f : Euc d → ℝ, Measurable f → (∀ x, |f x| ≤ B) → Integrable f →
      ∀ ε : ℝ, ε ≤ 1 → ∫ x, |f x| ≤ ε →
        ∀ ρ : Euc d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ M) →
          MemLp (convFun (rieszKernel d s) f) 2 (withDensityReal ρ) ∧
          l2Norm (withDensityReal ρ) (convFun (rieszKernel d s) f) ≤
            CBM * ε ^ (3 / 2 - s / d) := by
  have hd1 : 1 ≤ d := by omega
  have hs0 : 0 < s := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hds : (d : ℝ) < 2 * s := by linarith
  have hrk : ∀ z : Euc d, rieszKernel d s z = ‖z‖ ^ (-s) := Q34.rieszKernel_eq hs0.ne'
  obtain ⟨CBM, hCBM⟩ := Q34.l2_bound hd1 hs0 hsd hds B M
  refine ⟨CBM, fun f hf hB hfi ε hε1 hε ρ hρ hM => ?_⟩
  have := hCBM f hf hB hfi ε hε1 hε ρ hρ hM
  show MemLp (fun x : Euc d => ∫ y, rieszKernel d s (x - y) * f y) 2 (withDensityReal ρ) ∧
    Real.sqrt (∫ x, (∫ y, rieszKernel d s (x - y) * f y) ^ 2 ∂(withDensityReal ρ)) ≤
      CBM * ε ^ (3 / 2 - s / d)
  simpa only [hrk] using this

/-- Lemma S7.3 (S:S:lem:convolution, TeX S L5462-5488), `S:eq:truncated-integrals` (S lines 5476-5480): for `g_H = min{g,H}`, `H ≥ 1`,
`sup_y ∫ g_H(y-z)² dμ(z) ≤ C H^{2-p}` and `sup_y ∫ (g-g_H)(y-z) dμ(z) ≤ C H^{1-p}`
(`C` depends on `d, s, M`, quantified before `ρ`). -/
theorem convolution_truncated (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) (M : ℝ) :
    ∃ C : ℝ, ∀ ρ : Euc d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ M) → ∀ H : ℝ, 1 ≤ H → ∀ y : Euc d,
      Integrable (fun z => truncKernel d s H (y - z) ^ 2) (withDensityReal ρ) ∧
      ∫ z, truncKernel d s H (y - z) ^ 2 ∂(withDensityReal ρ) ≤ C * H ^ (2 - biasP d s) ∧
      Integrable (fun z => rieszKernel d s (y - z) - truncKernel d s H (y - z)) (withDensityReal ρ) ∧
      ∫ z, rieszKernel d s (y - z) - truncKernel d s H (y - z) ∂(withDensityReal ρ) ≤
        C * H ^ (1 - biasP d s) := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by linarith
  have hds : (d : ℝ) < 2 * s := by linarith
  have hdm : 0 < (d : ℝ) - s := by linarith
  have h2sd : 0 < 2 * s - (d : ℝ) := by linarith
  have hsA := Q34.sphereArea_nonneg hd1
  refine ⟨|M| * sphereArea d * (1 / (d : ℝ) + 1 / (2 * s - d) + 1 / ((d : ℝ) - s)), ?_⟩
  intro ρ hρ hM H hH y
  have hM0 : 0 ≤ M := (hρ.nonneg 0).trans (hM 0)
  rw [abs_of_nonneg hM0]
  have hH0 : 0 < H := by linarith
  have hrk : ∀ z : Euc d, rieszKernel d s z = ‖z‖ ^ (-s) := Q34.rieszKernel_eq hs0.ne'
  have hp : biasP d s = (d : ℝ) / s := rfl
  have hmeasg : Measurable (fun z : Euc d => ‖y - z‖ ^ (-s)) :=
    (measurable_norm.comp (measurable_const.sub measurable_id)).pow_const _
  have hmin : Measurable (fun z : Euc d => min (‖y - z‖ ^ (-s)) H) :=
    hmeasg.min measurable_const
  have hg0 : ∀ z : Euc d, 0 ≤ ‖y - z‖ ^ (-s) := fun z => Real.rpow_nonneg (norm_nonneg _) _
  have hmin0 : ∀ z : Euc d, 0 ≤ min (‖y - z‖ ^ (-s)) H :=
    fun z => le_min (hg0 z) hH0.le
  have htk : ∀ z : Euc d, truncKernel d s H (y - z) = min (‖y - z‖ ^ (-s)) H := by
    intro z; simp only [truncKernel, hrk]
  have hH2 : 0 ≤ H ^ (2 - (d : ℝ) / s) := Real.rpow_nonneg hH0.le _
  have hH1 : 0 ≤ H ^ (1 - (d : ℝ) / s) := Real.rpow_nonneg hH0.le _
  have hA := Q34.trunc_sq_le hd1 hs0 hds hρ hM hH y
  have hB := Q34.trunc_diff_le hd1 hs0 hsd hρ hM hH y
  have hA0 : 0 ≤ M * sphereArea d * (1 / (d : ℝ) + 1 / (2 * s - d)) * H ^ (2 - (d : ℝ) / s) := by
    have : (0 : ℝ) < d := by linarith
    positivity
  have hB0 : 0 ≤ M * sphereArea d / ((d : ℝ) - s) * H ^ (1 - (d : ℝ) / s) := by positivity
  obtain ⟨hAi, hAv⟩ := Q34.integrable_of_lintegral_le
    (μ := withDensityReal ρ) (f := fun z : Euc d => (min (‖y - z‖ ^ (-s)) H) ^ 2)
    (hmin.pow_const 2) (fun z => by have := hmin0 z; positivity) hA0 hA
  obtain ⟨hBi, hBv⟩ := Q34.integrable_of_lintegral_le
    (μ := withDensityReal ρ) (f := fun z : Euc d => ‖y - z‖ ^ (-s) - min (‖y - z‖ ^ (-s)) H)
    (hmeasg.sub hmin) (fun z => by
      have := min_le_left (‖y - z‖ ^ (-s)) H
      linarith) hB0 hB
  simp only [htk, hrk, hp]
  refine ⟨hAi, hAv.trans ?_, hBi, hBv.trans ?_⟩
  · have : (0 : ℝ) < d := by linarith
    have h3 : 0 ≤ M * sphereArea d / ((d : ℝ) - s) := by positivity
    have h4 : 0 ≤ M * sphereArea d * (1 / (d : ℝ) + 1 / (2 * s - d)) := by positivity
    calc M * sphereArea d * (1 / (d : ℝ) + 1 / (2 * s - d)) * H ^ (2 - (d : ℝ) / s)
        ≤ M * sphereArea d * (1 / (d : ℝ) + 1 / (2 * s - d) + 1 / ((d : ℝ) - s)) *
            H ^ (2 - (d : ℝ) / s) := by
          have : 0 ≤ 1 / ((d : ℝ) - s) := by positivity
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hM0 hsA)) hH2
      _ = _ := rfl
  · have : (0 : ℝ) < d := by linarith
    have h5 : 0 ≤ M * sphereArea d := by positivity
    calc M * sphereArea d / ((d : ℝ) - s) * H ^ (1 - (d : ℝ) / s)
        = M * sphereArea d * (1 / ((d : ℝ) - s)) * H ^ (1 - (d : ℝ) / s) := by ring
      _ ≤ M * sphereArea d * (1 / (d : ℝ) + 1 / (2 * s - d) + 1 / ((d : ℝ) - s)) *
            H ^ (1 - (d : ℝ) / s) := by
          have : 0 ≤ 1 / (d : ℝ) + 1 / (2 * s - d) := by positivity
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hM0 hsA)) hH1

/-- Lemma S7.3 (S:S:lem:convolution, TeX S L5462-5488), last part (S lines 5481-5487): `K_μ` is a bounded nonnegative self-adjoint
operator on `L²_0(μ)` with `‖K_μ‖ ≤ M_g`, and `R_{β,μ} = (I+βK_μ)⁻¹` exists on `L²_0(μ)` with
`‖f‖²/(1+βM_g) ≤ ⟨f, R_{β,μ}f⟩_{L²(μ)} ≤ ‖f‖²` and `‖R_{β,μ}‖ ≤ 1`
(`S:eq:positive-inverse`).  `R_{β,μ}f` is the unique (a.e.) `h ∈ L²_0(μ)` with `h + βK_μ h = f`
(`IsResponse`, existence and uniqueness are asserted), `‖‖` is `l2Norm`. -/
theorem convolution_susceptibility (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d)
    (ρ : Euc d → ℝ) (hρ : IsProbDensity ρ) (M : ℝ) (hM : ∀ x, ρ x ≤ M) (β : ℝ) (hβ : 0 < β) :
    (∀ f : Euc d → ℝ, MemL2Zero (withDensityReal ρ) f →
      MemL2Zero (withDensityReal ρ) (Kop (rieszKernel d s) (withDensityReal ρ) f) ∧
      l2Norm (withDensityReal ρ) (Kop (rieszKernel d s) (withDensityReal ρ) f) ≤
        potentialBound d s M * l2Norm (withDensityReal ρ) f) ∧
    (∀ f h : Euc d → ℝ, MemL2Zero (withDensityReal ρ) f → MemL2Zero (withDensityReal ρ) h →
      l2Inner (withDensityReal ρ) (Kop (rieszKernel d s) (withDensityReal ρ) f) h =
        l2Inner (withDensityReal ρ) f (Kop (rieszKernel d s) (withDensityReal ρ) h)) ∧
    (∀ f : Euc d → ℝ, MemL2Zero (withDensityReal ρ) f →
      0 ≤ l2Inner (withDensityReal ρ) (Kop (rieszKernel d s) (withDensityReal ρ) f) f) ∧
    ∀ f : Euc d → ℝ, MemL2Zero (withDensityReal ρ) f →
      (∃ h, IsResponse (rieszKernel d s) (withDensityReal ρ) β f h) ∧
      (∀ h h', IsResponse (rieszKernel d s) (withDensityReal ρ) β f h →
        IsResponse (rieszKernel d s) (withDensityReal ρ) β f h' → h =ᵐ[withDensityReal ρ] h') ∧
      (∫ x, f x ^ 2 ∂(withDensityReal ρ)) / (1 + β * potentialBound d s M) ≤
        l2Inner (withDensityReal ρ) f (responseInverse (rieszKernel d s) (withDensityReal ρ) β f) ∧
      l2Inner (withDensityReal ρ) f (responseInverse (rieszKernel d s) (withDensityReal ρ) β f) ≤
        ∫ x, f x ^ 2 ∂(withDensityReal ρ) ∧
      l2Norm (withDensityReal ρ) (responseInverse (rieszKernel d s) (withDensityReal ρ) β f) ≤
        l2Norm (withDensityReal ρ) f := by
  have hd1 : 1 ≤ d := by omega
  have hs0 : 0 < s := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hq : Q34.Q34Hyp d s ρ M := ⟨hd1, hs0, hsd, hρ, hM⟩
  haveI := Q34.isProbabilityMeasure_nu hρ
  exact ⟨fun f hf => Q34.partA hq hf, fun f h hf hh => Q34.partB hq hf hh,
    fun f hf => Q34.partC hq hf, fun f hf => Q34.partD hq hβ hf⟩

end Convolution

/-! ### S7.4 `S:prop:conditional-density` (S lines 5560-5578) -/

section Conditional

variable {s : ℝ}

/-- The conditional empirical potential `u_Y(y) = λ∑_{j=2}^n g(y-y_j) - β(g*μ)(y)`
(`S:eq:conditional-potential`, S line 5555), as a function of the full cavity configuration
`Y = (y_1,…,y_n)` through `(y_2,…,y_n)` (the sum skips the coordinate with index `0`). -/
def condPotential (d : ℕ) (s : ℝ) (N : ℕ) (β : ℝ) (μ : Measure (Euc d))
    (Y : EucConfig d (N - 1)) (y : Euc d) : ℝ :=
  (β / N) * ∑ j : Fin (N - 1), (if (j : ℕ) = 0 then 0 else rieszKernel d s (y - Y j)) -
    β * convMeasure (rieszKernel d s) μ y

/-- Proposition S7.4 (S:S:prop:conditional-density, TeX S L5560-5578) (S lines 5560-5578): there is a version of
the one-particle pole density of the form `e^{-tλg(x-y)} A_{N,x,t}(y)` with
`sup_y E_{P_n^0}|u_Y(y)| ≤ CN^{-τ}` (`S:eq:potential-uniform`) and
`sup_{x, 0≤t≤1} ‖A_{N,x,t} - 1‖_{L^∞(μ)} ≤ CN^{-τ}` (`S:eq:prefactor-uniform`), with constants
requiring only the bounded-density hypothesis (and the static inputs); the pole location is
unrestricted.  The prefactor `A` is asserted nonnegative a.e. (it is a ratio of densities; this
excludes the clamping of `ENNReal.ofReal`).  Technical hypothesis: `N ≥ 2`. -/
theorem conditional_density (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) (β M : ℝ)
    (hβ : 0 < β) :
    ∃ C : ℝ, ∀ ρ : Euc d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ M) → ∀ N, 2 ≤ N →
      (∀ y : Euc d,
        Integrable (fun Y => |condPotential d s N β (withDensityReal ρ) Y y|)
          (cavityLaw d s N β (withDensityReal ρ)) ∧
        ∫ Y, |condPotential d s N β (withDensityReal ρ) Y y|
            ∂(cavityLaw d s N β (withDensityReal ρ)) ≤ C * (N : ℝ) ^ (-biasTau d s)) ∧
      ∀ (x : Euc d), ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ A : Euc d → ℝ, Measurable A ∧
        firstMarginal (poleLaw d s N β (withDensityReal ρ) x t) =
          (withDensityReal ρ).withDensity
            (fun y => ENNReal.ofReal (Real.exp (-(t * (β / N)) * rieszKernel d s (x - y)) * A y)) ∧
        (∀ᵐ y ∂(withDensityReal ρ), 0 ≤ A y) ∧
        ∀ᵐ y ∂(withDensityReal ρ), |A y - 1| ≤ C * (N : ℝ) ^ (-biasTau d s) := by
  sorry

end Conditional

/-! ### S7.5 `S:lem:compensated-kernel` (S lines 5703-5715) -/

section Compensated

variable {s : ℝ}

/-- `k_s(u) = e^{-|u|^{-s}} - 1 + |u|^{-s}` (`S:eq:compensated-kernel`, S line 5707). -/
def compKernel (d : ℕ) (s : ℝ) (u : Euc d) : ℝ :=
  Real.exp (-‖u‖ ^ (-s)) - 1 + ‖u‖ ^ (-s)

/-- Lemma S7.5 (S:S:lem:compensated-kernel, TeX S L5703-5715) (S lines 5703-5715), `d ≥ 2`, `d/2 < s < d`:
`k_s ≥ 0`, `k_s(u) = |u|^{-2s} ∫_0^1 (1-t) e^{-t|u|^{-s}} dt` (`u ≠ 0`), `k_s ∈ L¹(ℝ^d)`,
`∫ k_s = 2A_{d,s}`, and `∫_{|u|>L} k_s ≤ C L^{d-2s}` for `L ≥ 1` (`S:eq:kernel-mass`);
`C` depends on `d, s`. -/
theorem compensated_kernel (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) :
    (∀ u, 0 ≤ compKernel d s u) ∧
    (∀ u : Euc d, u ≠ 0 → compKernel d s u =
      ‖u‖ ^ (-(2 * s)) * ∫ t in Set.Icc (0 : ℝ) 1, (1 - t) * Real.exp (-t * ‖u‖ ^ (-s))) ∧
    Integrable (compKernel d s) (volume : Measure (Euc d)) ∧
    ∫ u, compKernel d s u = 2 * biasConst d s ∧
    ∃ C : ℝ, ∀ L : ℝ, 1 ≤ L →
      ∫ u in {u : Euc d | L < ‖u‖}, compKernel d s u ≤ C * L ^ ((d : ℝ) - 2 * s) := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by linarith
  have hds : (d : ℝ) < 2 * s := by linarith
  have hck : ∀ u : Euc d, compKernel d s u = Q34.kk (‖u‖ ^ (-s)) := fun u => rfl
  have hI := Q34.compKernel_integrable_integral hd1 hs0 hsd hds
  refine ⟨fun u => ?_, fun u hu => ?_, ?_, ?_, ?_⟩
  · rw [hck]; exact Q34.kk_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
  · rw [hck]; exact Q34.compKernel_taylor u hu
  · exact hI.1
  · simp only [hck]
    rw [hI.2]
    unfold biasConst biasP
    have : (d : ℝ) / s - 1 ≠ 0 := by
      have : 1 < (d : ℝ) / s := by rw [lt_div_iff₀ hs0]; linarith
      linarith
    have : (d : ℝ) / s ≠ 0 := by positivity
    field_simp
  · obtain ⟨C, hC⟩ := Q34.compKernel_tail hd1 hs0 hsd hds
    exact ⟨C, fun L hL => by simp only [hck]; exact hC L hL⟩

end Compensated

/-! ### S7.6 `S:prop:sharp-insertion` (S lines 5738-5753) -/

section Insertion

variable {s : ℝ}

/-- `F_{N,x}(t) = log P_n^0[e^{-tλ∑_i g(x-y_i)}]` (`S:eq:insertion-definition`, S line 5674). -/
def insertionPressure (d : ℕ) (s : ℝ) (N : ℕ) (β : ℝ) (μ : Measure (Euc d)) (x : Euc d)
    (t : ℝ) : ℝ :=
  Real.log (poleNormalizer d s N β μ x t)

/-- `D_N(x) = F_{N,x}(1) - F'_{N,x}(0)` (S line 5675), with the right derivative at `0`. -/
def insertionDefect (d : ℕ) (s : ℝ) (N : ℕ) (β : ℝ) (μ : Measure (Euc d)) (x : Euc d) : ℝ :=
  insertionPressure d s N β μ x 1 -
    derivWithin (insertionPressure d s N β μ x) (Set.Ici 0) 0

/-- Proposition S7.6 (S:S:prop:sharp-insertion, TeX S L5738-5753), `S:eq:insertion-radius-bound` (S lines
5738-5746): for a bounded Lipschitz probability density (`‖ρ‖_∞ ≤ M`, Lipschitz constant
`‖∇ρ‖_∞ ≤ Λ`), for every `L ≥ 1` and all sufficiently large `N`,
`‖D_N/(nλ^p) - 2A_{d,s}ρ‖_∞ ≤ C(N^{-τ} + ‖∇ρ‖_∞ λ^{1/s} L + L^{-(2s-d)/2} + nλ^p L^{2(d-s)})`,
`n = N-1`, `λ = β/N`; the supremum is over the whole space.  The pole laws are well defined for
`t ∈ [0,1]` and the derivative `F'_{N,x}(0)` exists (S line 5677), both asserted.  `C` depends on
`d, s, β, M` (quantified before `L` and `ρ`).
The threshold `N₀` is chosen before `L` (it depends on `d, s, β, M` only; this is what the proof
at S L5833 and the rate corollary `S:eq:insertion-rate` with `L = N^{1/(4s)}` need). -/
theorem sharp_insertion_radius (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) (β M : ℝ)
    (hβ : 0 < β) :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ L : ℝ, 1 ≤ L → ∀ N, N₀ ≤ N → ∀ ρ : Euc d → ℝ, IsProbDensity ρ →
      (∀ x, ρ x ≤ M) → ∀ Λ : ℝ≥0, LipschitzWith Λ ρ → ∀ x : Euc d,
        (∀ t ∈ Set.Icc (0 : ℝ) 1, CavityWellDefined d s N β (withDensityReal ρ) x t) ∧
        DifferentiableWithinAt ℝ (insertionPressure d s N β (withDensityReal ρ) x) (Set.Ici 0) 0 ∧
        |insertionDefect d s N β (withDensityReal ρ) x / ((N - 1 : ℝ) * (β / N) ^ biasP d s) -
            2 * biasConst d s * ρ x| ≤
          C * ((N : ℝ) ^ (-biasTau d s) + Λ * (β / N) ^ (1 / s) * L +
            L ^ (-((2 * s - d) / 2)) + (N - 1 : ℝ) * (β / N) ^ biasP d s * L ^ (2 * ((d : ℝ) - s))) := by
  sorry

/-- Proposition S7.6 (S:S:prop:sharp-insertion, TeX S L5738-5753), `S:eq:insertion-rate` (S lines 5747-5751): choosing `L = N^{1/(4s)}`,
`‖D_N/(nλ^p) - 2A_{d,s}ρ‖_∞ ≤ C N^{-θ_{d,s}}` for all sufficiently large `N` (`C` and the
threshold depend on `d, s, β, M` and the Lipschitz constant `Λ ≥ ‖∇ρ‖_∞`). -/
theorem sharp_insertion_rate (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) (β M : ℝ)
    (Λ : ℝ≥0) (hβ : 0 < β) :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ ρ : Euc d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      LipschitzWith Λ ρ → ∀ x : Euc d,
        |insertionDefect d s N β (withDensityReal ρ) x / ((N - 1 : ℝ) * (β / N) ^ biasP d s) -
            2 * biasConst d s * ρ x| ≤ C * (N : ℝ) ^ (-biasTheta d s) := by
  sorry

end Insertion

/-! ### S7.1 `S:thm:sharp-bias` (S lines 5314-5338) -/

section SharpBias

variable {s : ℝ}

/-- The conclusions of Theorem S7.1 for one `N`, constant `C`: the law is well defined;
`R_{β,μ}P_μρ ∈ L²(μ)` (S line 5307); `m_N ≪ μ` with a nonnegative density `φ`;
`‖(φ-1)/δ_N - 2A_{d,s}β^p R_{β,μ}P_μρ‖_{L²(μ)} ≤ CN^{-θ}` (`S:eq:sharp-bias`); and for every
`φ ∈ L²(μ)`, `m_N(φ)` is defined and
`m_N(φ) - μ(φ) = 2A_{d,s}β^p δ_N ⟨P_μφ, R_{β,μ}P_μρ⟩_{L²(μ)} + ℛ_N(φ)` with
`|ℛ_N(φ)| ≤ Cδ_N N^{-θ} ‖P_μφ‖_{L²(μ)}` (`S:eq:sharp-statistic`, `S:eq:test-remainder`). -/
def SharpBiasConclusion (d : ℕ) (s : ℝ) (N : ℕ) (β : ℝ) (ρ : Euc d → ℝ) (C : ℝ) : Prop :=
  GibbsWellDefined (fun x y => rieszKernel d s (x - y)) N β (withDensityReal ρ) ∧
  MemLp (responseInverse (rieszKernel d s) (withDensityReal ρ) β ρ) 2 (withDensityReal ρ) ∧
  (∃ φ : Euc d → ℝ, Measurable φ ∧ (∀ x, 0 ≤ φ x) ∧
    firstMarginal (modulatedGibbs (rieszKernel d s) N β (withDensityReal ρ)) =
      (withDensityReal ρ).withDensity (fun x => ENNReal.ofReal (φ x)) ∧
    MemLp (fun x => (φ x - 1) / deltaN d s N - biasDensity d s β ρ x) 2 (withDensityReal ρ) ∧
    l2Norm (withDensityReal ρ) (fun x => (φ x - 1) / deltaN d s N - biasDensity d s β ρ x) ≤
      C * (N : ℝ) ^ (-biasTheta d s)) ∧
  ∀ φ : Euc d → ℝ, MemLp φ 2 (withDensityReal ρ) →
    Integrable φ (firstMarginal (modulatedGibbs (rieszKernel d s) N β (withDensityReal ρ))) ∧
    |∫ x, φ x ∂(firstMarginal (modulatedGibbs (rieszKernel d s) N β (withDensityReal ρ))) -
        ∫ x, φ x ∂(withDensityReal ρ) -
        2 * biasConst d s * β ^ biasP d s * deltaN d s N *
          l2Inner (withDensityReal ρ) (projMean (withDensityReal ρ) φ)
            (responseInverse (rieszKernel d s) (withDensityReal ρ) β ρ)| ≤
      C * deltaN d s N * (N : ℝ) ^ (-biasTheta d s) *
        l2Norm (withDensityReal ρ) (projMean (withDensityReal ρ) φ)

/-- Theorem S7.1 (S:S:thm:sharp-bias, TeX S L5314-5338) (S lines 5314-5338): `ρ ∈ W^{1,∞}(ℝ^d)` a probability
density (bounded, Lipschitz; `‖ρ‖_∞ ≤ M`, Lipschitz constant `Λ ≥ ‖∇ρ‖_∞`), `β > 0` fixed,
`d ≥ 2`, `d/2 < s < d`.  The law `S:eq:modulated-law` is well defined and `S:eq:sharp-bias`
holds with a constant depending only on `d, s, β, ‖ρ‖_∞, ‖∇ρ‖_∞` (quantified before `ρ`),
independent of a support radius and of a positive density lower bound; together with the
consequences `S:eq:sharp-statistic`, `S:eq:test-remainder` for every `φ ∈ L²(μ)`.  No compact
support, moment, or lower-density hypothesis.  Technical hypothesis: `N ≥ 1` (the source says
"for every `N`"; `N = 0` has no meaning). -/
theorem sharp_bias (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) (β M : ℝ) (Λ : ℝ≥0)
    (hβ : 0 < β) :
    ∃ C : ℝ, ∀ ρ : Euc d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ M) → LipschitzWith Λ ρ →
      ∀ N, 1 ≤ N → SharpBiasConclusion d s N β ρ C := by
  sorry

/-- Theorem S7.1 (S:S:thm:sharp-bias, TeX S L5314-5338), uniformity clause (S lines 5325-5326): for a fixed background `ρ`, the
constant is uniform when `β` varies in a prescribed compact subinterval `[β₋,β₊] ⊂ (0,∞)`. -/
theorem sharp_bias_uniform_beta (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d)
    (ρ : Euc d → ℝ) (hρ : IsProbDensity ρ) (M : ℝ) (hM : ∀ x, ρ x ≤ M) (Λ : ℝ≥0)
    (hΛ : LipschitzWith Λ ρ) (βm βp : ℝ) (hβm : 0 < βm) (hβ : βm ≤ βp) :
    ∃ C : ℝ, ∀ β ∈ Set.Icc βm βp, ∀ N, 1 ≤ N → SharpBiasConclusion d s N β ρ C := by
  sorry

/-- Theorem S7.1 (S:S:thm:sharp-bias, TeX S L5314-5338), "Quadratic confinement" paragraph (S lines 5349-5357): for `V(x) = a|x|²/2`,
`a > 0`, the thermal equilibrium measure `μ_β` satisfies the hypotheses of Theorem S7.1 at every
fixed `β > 0` (a probability density, bounded and Lipschitz), the canonical law
`S:eq:canonical-law` equals `Q_{N,β}(μ_β)`, and hence `S:eq:sharp-bias` holds for the genuine
quadratic trap.  `μ_β` is `thermalDensity d s a β` (existence and uniqueness: S3.4,
`thermalDensity_spec`). -/
theorem sharp_bias_quadratic (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) (a β : ℝ)
    (ha : 0 < a) (hβ : 0 < β) :
    IsProbDensity (thermalDensity d s a β) ∧
    (∃ M : ℝ, ∀ x, thermalDensity d s a β x ≤ M) ∧
    (∃ Λ : ℝ≥0, LipschitzWith Λ (thermalDensity d s a β)) ∧
    (∀ N, canonicalGibbs (rieszKernel d s) (confinement a) N β =
      modulatedGibbs (rieszKernel d s) N β (thermalMeasure d s a β)) ∧
    ∃ C : ℝ, ∀ N, 1 ≤ N → SharpBiasConclusion d s N β (thermalDensity d s a β) C := by
  sorry

end SharpBias

/-! ### S7.7 `S:cor:weighted-remainder` (S lines 5924-5939) -/

section Weighted

variable {s : ℝ}

/-- Corollary S7.7 (S:S:cor:weighted-remainder, TeX S L5924-5939) (S lines 5924-5939): let
`r_N = m_N - μ - δ_N b_{β,μ}` (a signed measure; `b_{β,μ} = 2A β^p (R_{β,μ}P_μρ) μ`, the
signed measure with density `biasDensity` relative to `μ`).  For every nonnegative measurable `w`
with `μ(w²) < ∞`, `∫ w d|r_N| ≤ C δ_N N^{-θ} ‖w‖_{L²(μ)}` (`S:eq:weighted-remainder`); and for
every measurable set `E`, `|m_N-μ|(E)/δ_N + |b_{β,μ}|(E) ≤ C√μ(E)` (`S:eq:tail-tightness`).
The constant is that of Theorem S7.1 (depends only on `d, s, β, ‖ρ‖_∞, ‖∇ρ‖_∞`); it is chosen
before `ρ`.  All quantities are in `ℝ≥0∞` (`∫⁻ w d|r_N|`, total variation measures).
Technical hypotheses: `N ≥ 1`; `[IsProbabilityMeasure μ]` and `[IsFiniteMeasure m_N]` are the
instances needed to form `toSignedMeasure` (they hold by S7.1: the law is well defined and
`μ = ρ dx` is a probability measure; `m_N = firstMarginal …`); `b_{β,μ}` is
`μ.withDensityᵥ` of its density, a signed measure because that density is in `L²(μ) ⊂ L¹(μ)`
(S7.1; asserted in the conclusion). -/
theorem weighted_remainder (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) (β M : ℝ) (Λ : ℝ≥0)
    (hβ : 0 < β) :
    ∃ C : ℝ, ∀ ρ : Euc d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ M) → LipschitzWith Λ ρ →
      ∀ [IsProbabilityMeasure (withDensityReal ρ)] (N : ℕ), 1 ≤ N →
      ∀ (mN : Measure (Euc d)) [IsFiniteMeasure mN],
        mN = firstMarginal (modulatedGibbs (rieszKernel d s) N β (withDensityReal ρ)) →
        MemLp (biasDensity d s β ρ) 2 (withDensityReal ρ) ∧
        (∀ w : Euc d → ℝ, Measurable w → (∀ x, 0 ≤ w x) → MemLp w 2 (withDensityReal ρ) →
          ∫⁻ x, ENNReal.ofReal (w x) ∂(SignedMeasure.totalVariation
              (mN.toSignedMeasure - (withDensityReal ρ).toSignedMeasure -
                (deltaN d s N) • (withDensityReal ρ).withDensityᵥ (biasDensity d s β ρ))) ≤
            ENNReal.ofReal (C * deltaN d s N * (N : ℝ) ^ (-biasTheta d s) *
              l2Norm (withDensityReal ρ) w)) ∧
        ∀ E : Set (Euc d), MeasurableSet E →
          (SignedMeasure.totalVariation (mN.toSignedMeasure - (withDensityReal ρ).toSignedMeasure)) E /
              ENNReal.ofReal (deltaN d s N) +
            (SignedMeasure.totalVariation ((withDensityReal ρ).withDensityᵥ (biasDensity d s β ρ))) E ≤
          ENNReal.ofReal (C * Real.sqrt ((withDensityReal ρ E).toReal)) := by
  sorry

end Weighted

/-! ### S7.8 `S:cor:sharp-threshold` (S lines 6011-6032) -/

section Threshold

variable {s : ℝ}

/-- `V_ρ = ⟨P_μρ, R_{β,μ}P_μρ⟩_{L²(μ)}` (`S:eq:score-variance`, S line 5977), for `μ = μ_β`,
`ρ = ρ_β`. -/
def scoreVariance (d : ℕ) (s β : ℝ) (ρ : Euc d → ℝ) : ℝ :=
  susceptibilityCov (rieszKernel d s) (withDensityReal ρ) β ρ ρ

/-- Corollary S7.8 (S:S:cor:sharp-threshold, TeX S L6011-6032) (S lines 6011-6032), critical case `s = 2d/3`
(`p = 3/2`): for the canonical quadratic-trap law `P_{N,β}` (`S:eq:canonical-law`) and the test
`φ = ρ_β`, `√N(μ_N(ρ_β) - μ_β(ρ_β)) ⇒ N(2A_{d,s}β^{3/2}V_ρ, V_ρ)`
(`S:eq:critical-scalar`), `V_ρ > 0` (`S:eq:strict-nonvanishing`, S lines 5981-5984, the nonzero
mean "certified" there).  `ρ_β` is any `IsThermalEquilibrium d s a β` (S3.4).  The weak convergence
of the laws on `ℝ` (varying probability spaces `P_{N,β}`) is
`∫ f(√N(μ_N(ρ_β) - μ_β(ρ_β))) dP_{N,β} → ∫ f dγ` for every bounded continuous `f`; that the
`P_{N,β}` are probability measures is part of the conclusion. -/
theorem sharp_threshold_critical (hd : 2 ≤ d) (hs : s = 2 * (d : ℝ) / 3) (a β : ℝ)
    (ha : 0 < a) (hβ : 0 < β) :
    ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ →
      0 < scoreVariance d s β ρβ ∧
      (∀ N, 1 ≤ N → IsProbabilityMeasure (canonicalGibbs (rieszKernel d s) (confinement a) N β)) ∧
      ∀ f : ℝ →ᵇ ℝ,
        Tendsto (fun N : ℕ => ∫ X, f (Real.sqrt N *
            (linStat ρβ X - pair (withDensityReal ρβ) ρβ))
          ∂(canonicalGibbs (rieszKernel d s) (confinement a) N β)) atTop
          (𝓝 (∫ y, f y ∂(ProbabilityTheory.gaussianReal
            (2 * biasConst d s * β ^ ((3 : ℝ) / 2) * scoreVariance d s β ρβ)
            (Real.toNNReal (scoreVariance d s β ρβ))))) := by
  sorry

/-- Corollary S7.8 (S:S:cor:sharp-threshold, TeX S L6011-6032) (S lines 6011-6032), supercritical case
`2d/3 < s < d`: `N^{p-1}(μ_N(ρ_β) - μ_β(ρ_β)) → 2A_{d,s}β^pV_ρ` in `L²(P_{N,β})`
(`S:eq:supercritical-L2`), "more precisely, the `L²` error is at most `C(N^{p-3/2} + N^{-θ})`"
(`C` depending on `d, s, a, β`; the squared error is a `lintegral`, so finiteness is asserted),
and `√N(μ_N(ρ_β) - μ_β(ρ_β)) → +∞` in probability.  `V_ρ > 0`.  The subcritical range
`0 ≤ s < 2d/3` ("the existing mean-field-centered stationary Gaussian limit remains valid",
S line 6030) is a pointer to earlier results, not a new claim; the Coulomb paragraph (S lines
6035-6040) is a specialisation of this corollary to `s = d-2` and is not separately stated. -/
theorem sharp_threshold_supercritical (hd : 2 ≤ d) (hs : 2 * (d : ℝ) / 3 < s) (hsd : s < d)
    (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) :
    ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ →
      0 < scoreVariance d s β ρβ ∧
      (∃ C : ℝ, ∀ N, 1 ≤ N →
        (∫⁻ X, ENNReal.ofReal |(N : ℝ) ^ (biasP d s - 1) *
              (linStat ρβ X - pair (withDensityReal ρβ) ρβ) -
            2 * biasConst d s * β ^ biasP d s * scoreVariance d s β ρβ| ^ 2
          ∂(canonicalGibbs (rieszKernel d s) (confinement a) N β)) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (C * ((N : ℝ) ^ (biasP d s - 3 / 2) + (N : ℝ) ^ (-biasTheta d s)))) ∧
      ∀ K : ℝ, Tendsto (fun N : ℕ => canonicalGibbs (rieszKernel d s) (confinement a) N β
          {X | Real.sqrt N * (linStat ρβ X - pair (withDensityReal ρβ) ρβ) ≤ K}) atTop (𝓝 0) := by
  sorry

end Threshold

end HRS.Whole
