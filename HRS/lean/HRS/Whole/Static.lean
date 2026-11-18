import HRS.Whole.Basic
import HRS.Whole.SteinAux8

/-!
# Whole-space static estimates (package S-STAT-01, part I): Section S3

Source: HRS whole-space supplement (S).

* S3.1 `W:prop:euclidean-pressure` (S lines 497-520), with the pair-kernel energy
  `W:eq:euclidean-F` (483-485), normaliser `W:eq:euclidean-K` (486), `Q^h_{N,b}` (488),
  `δ_N` (491-495).
* S3.3 `W:prop:euc-static` (928-952), standing hypotheses S lines 903-926
  (`W:eq:euc-static-normalization`, `W:eq:euc-static-scale`), `W:eq:euc-D` (940-944).
* S3.4 `W:prop:euc-thermal` (1348-1384); existence/uniqueness is `thermalDensity_spec`
  (Basic.lean), the remaining clauses are here.
* S3.5 `W:thm:r2-log-static` (1532-1563), standing hypotheses S lines 1511-1530
  (`W:eq:r2-log-density`, `W:eq:r2-log-gibbs`), `W:eq:r2-log-K-definition` (1550-1553).
* S3.6 `W:rem:r2-log-scope` (1968-1977): a scope remark; it contains no mathematical claim
  beyond S3.5 (it says which hypotheses S3.5 uses and that it supplies no adjoint estimate).
  No statement.
* S3.7 `W:lem:r2-static-Stein` (1986-2006).

## Representation decisions

* Variances are Mathlib's `ProbabilityTheory.evariance` (`ℝ≥0∞`), so "`N Var ≤ C‖f‖²`"
  includes square integrability of the statistic (no junk value).
* "The probability measure `Q_N` is well defined" (S line 929; "the normalizer belongs to
  `(0,∞)`", line 1534) is the explicit structure `GibbsWellDefined`: the background terms of
  the energy are integrable, the Gibbs weight is integrable, and the normaliser is positive.
* A Radon–Nikodym statement "`dπ_N/dμ ≤ C`, `‖dπ_N/dμ - 1‖_{L²(μ)} ≤ Cδ_N`" is rendered as the
  existence of a measurable density `φ` with `π_N = φ μ` and the two bounds (`MemLp` included).
* Kernel bounds `|h(x,y)| ≤ B(1+|x-y|^{-s})` are imposed **off the diagonal only**
  (`IsBoundedPairKernel`); Lean's junk `‖0‖^(-s) = 0` would otherwise impose a wrong condition
  on the diagonal, which the energies delete anyway.
* Sums of suprema `‖∇χ‖_∞ + ‖D²χ‖_∞ ≤ C` are written as "for all points `x, y`,
  `‖∇χ(x)‖ + ‖D²χ(y)‖ ≤ C`", which is literally equivalent and avoids the real `iSup` junk.
* Centered Gaussians are `HRS.IsCenteredGaussian` (Mathlib's `IsGaussian`, zero mean); the
  covariance of S3.7 is read off from `G` (`C_ij = E[G_i G_j]`), so degenerate `C` is allowed.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole

variable {d N : ℕ}

/-! ### Pair-kernel energies, Gibbs laws, well-definedness -/

/-- The pair-kernel modulated energy `𝖥_N^h(X_N,μ)` of `W:eq:euclidean-F` (S lines 483-485),
with the original deleted particle pair diagonal. -/
def pairEnergy (h : Euc d → Euc d → ℝ) (X : EucConfig d N) (μ : Measure (Euc d)) : ℝ :=
  (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, h (X i) (X j)
    - (1 / (N : ℝ)) * ∑ i, ∫ y, h (X i) y ∂μ
    + (1 / 2) * ∫ x, ∫ y, h x y ∂μ ∂μ

/-- `K^h_{N,b}(μ) = ∫ e^{-bN 𝖥_N^h} dμ^{⊗N}` (`W:eq:euclidean-K`, S line 486). -/
def pairNormalizer (h : Euc d → Euc d → ℝ) (N : ℕ) (b : ℝ) (μ : Measure (Euc d)) : ℝ :=
  ∫ X : EucConfig d N, Real.exp (-b * N * pairEnergy h X μ) ∂(Measure.pi fun _ => μ)

/-- `Q^h_{N,b} = (K^h_{N,b})⁻¹ e^{-bN 𝖥_N^h} μ^{⊗N}` (S line 488). -/
def pairGibbs (h : Euc d → Euc d → ℝ) (N : ℕ) (b : ℝ) (μ : Measure (Euc d)) :
    Measure (EucConfig d N) :=
  (ENNReal.ofReal (pairNormalizer h N b μ))⁻¹ •
    (Measure.pi fun _ => μ).withDensity
      fun X => ENNReal.ofReal (Real.exp (-b * N * pairEnergy h X μ))

/-- For a difference kernel `h(x,y) = g(x-y)` the pair energy is the modulated energy of
`W:r2:normalization` (definitional). -/
theorem pairEnergy_diff (g : Euc d → ℝ) (X : EucConfig d N) (μ : Measure (Euc d)) :
    pairEnergy (fun x y => g (x - y)) X μ = modulatedEnergy g X μ := rfl

theorem pairNormalizer_diff (g : Euc d → ℝ) (b : ℝ) (μ : Measure (Euc d)) :
    pairNormalizer (fun x y => g (x - y)) N b μ = gibbsNormalizer g N b μ := rfl

theorem pairGibbs_diff (g : Euc d → ℝ) (b : ℝ) (μ : Measure (Euc d)) :
    pairGibbs (fun x y => g (x - y)) N b μ = modulatedGibbs g N b μ := rfl

/-- "The law is well defined": every background term of the energy is integrable, the Gibbs
weight is integrable against `μ^{⊗N}`, and the normaliser is strictly positive (so the
Bochner integrals in `pairEnergy`, `pairNormalizer` are the source's integrals and `pairGibbs`
is a probability measure). -/
structure GibbsWellDefined (h : Euc d → Euc d → ℝ) (N : ℕ) (b : ℝ) (μ : Measure (Euc d)) :
    Prop where
  conv_integrable : ∀ x, Integrable (fun y => h x y) μ
  pair_integrable : Integrable (fun p : Euc d × Euc d => h p.1 p.2) (μ.prod μ)
  weight_integrable :
    Integrable (fun X : EucConfig d N => Real.exp (-b * N * pairEnergy h X μ))
      (Measure.pi fun _ => μ)
  normalizer_pos : 0 < pairNormalizer h N b μ

/-- The weight `W_s(z) - 1`: `|z|^{-s}` for `s > 0`, `(-log|z|)_+` for `s = 0`
(S lines 508-509, 528-529). -/
def rieszWeight (s : ℝ) (z : Euc d) : ℝ :=
  if s = 0 then max (-Real.log ‖z‖) 0 else ‖z‖ ^ (-s)

/-- A real measurable symmetric kernel with `|h(x,y)| ≤ B(1 + W_s(x-y) - 1)` off the diagonal
(S lines 507-509; S lines 937-938 "off the diagonal"). -/
structure IsBoundedPairKernel (s B : ℝ) (h : Euc d → Euc d → ℝ) : Prop where
  measurable : Measurable fun p : Euc d × Euc d => h p.1 p.2
  symm : ∀ x y, h x y = h y x
  bound : ∀ x y, x ≠ y → |h x y| ≤ B * (1 + rieszWeight s (x - y))

/-- The physical commutator kernel `h_v(x,y) = (v(x) - v(y))·∇g(x-y)` (S lines 950, 1561). -/
def commutatorKernel (d : ℕ) (s : ℝ) (v : Euc d → Euc d) (x y : Euc d) : ℝ :=
  inner ℝ (v x - v y) (rieszKernelGrad d s (x - y))

open Classical in
/-- The second marginal `P^{(2)}` of a law on configurations (`0` if `N < 2`). -/
def secondMarginal (P : Measure (EucConfig d N)) : Measure (Euc d × Euc d) :=
  if h : 2 ≤ N then P.map (fun X => (X ⟨0, by omega⟩, X ⟨1, by omega⟩)) else 0

/-- `‖f‖_{L²(μ)} = (∫ f² dμ)^{1/2}`. -/
def l2Norm (μ : Measure (Euc d)) (f : Euc d → ℝ) : ℝ := Real.sqrt (∫ x, f x ^ 2 ∂μ)

/-- The linear statistic `μ_N(f)` as a function of the configuration. -/
def linStat (f : Euc d → ℝ) (X : EucConfig d N) : ℝ := pair (empirical X) f

/-- "`dπ/dμ` is a density bounded by `C` with `‖dπ/dμ - 1‖_{L²(μ)} ≤ r`": existence of a
measurable version. -/
def HasMarginalDensityBounds (π μ : Measure (Euc d)) (C r : ℝ) : Prop :=
  ∃ φ : Euc d → ℝ, Measurable φ ∧ π = μ.withDensity (fun x => ENNReal.ofReal (φ x)) ∧
    (∀ x, 0 ≤ φ x ∧ φ x ≤ C) ∧ MemLp (fun x => φ x - 1) 2 μ ∧ l2Norm μ (fun x => φ x - 1) ≤ r

/-! ### S3.1 `W:prop:euclidean-pressure` (S lines 497-520) -/

section Pressure

variable {s : ℝ}

/-- The logarithmic moment hypothesis `∫ log(2+|x|) dμ ≤ L` (S line 501), with the
integrability that makes the Bochner integral the source's integral. -/
def HasLogMoment (μ : Measure (Euc d)) (L : ℝ) : Prop :=
  Integrable (fun x => Real.log (2 + ‖x‖)) μ ∧ ∫ x, Real.log (2 + ‖x‖) ∂μ ≤ L

/-- The second logarithmic moment hypothesis `∫ log(2+|x|)² dμ ≤ L` (the manuscript's own condition
for the `s = 0` static field, S4.5), with integrability.  Needed for `K_μ` to be a bounded operator
on `L²_0(μ)` when `s = 0` (the first log moment does not suffice). -/
def HasLogMoment2 (μ : Measure (Euc d)) (L : ℝ) : Prop :=
  Integrable (fun x => Real.log (2 + ‖x‖) ^ 2) μ ∧ ∫ x, Real.log (2 + ‖x‖) ^ 2 ∂μ ≤ L

/-- Proposition S3.1 `W:prop:euclidean-pressure`, main bound `W:eq:euclidean-pressure-bound`
(S lines 497-510): `d ≥ 2`, `0 ≤ s < d`, `μ = ρ dx` a probability measure with `‖ρ‖_∞ ≤ M`
(and `∫ log(2+|x|) dμ ≤ L` when `s = 0`), `0 < b₋ < b₊`.  For every `B` there are `θ₀ > 0`
and `C` such that `|log K^{g-θh}_{N,b}(μ)| ≤ C N δ_N` for `N ≥ 2`, `b ∈ [b₋,b₊]`, `|θ| ≤ θ₀`
and every real measurable symmetric `h` with `|h(x,y)| ≤ B(1+|x-y|^{-s})` (`s > 0`), resp.
`B(1+(-log|x-y|)_+)` (`s = 0`).  The constants depend only on the displayed parameters
`(d, s, M, L, b₋, b₊, B)`, hence are quantified before `ρ` and `h`.  The normaliser being in
`(0,∞)` is part of the claim (`GibbsWellDefined`). -/
theorem euclidean_pressure (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (M L bm bp B : ℝ)
    (hbm : 0 < bm) (hb : bm < bp) :
    ∃ θ₀ > 0, ∃ C : ℝ, ∀ ρ : Euc d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      (s = 0 → HasLogMoment (withDensityReal ρ) L) →
      ∀ h : Euc d → Euc d → ℝ, IsBoundedPairKernel s B h →
      ∀ N, 2 ≤ N → ∀ b ∈ Set.Icc bm bp, ∀ θ : ℝ, |θ| ≤ θ₀ →
        GibbsWellDefined (fun x y => rieszKernel d s (x - y) - θ * h x y) N b (withDensityReal ρ) ∧
        |Real.log (pairNormalizer (fun x y => rieszKernel d s (x - y) - θ * h x y) N b
          (withDensityReal ρ))| ≤ C * N * deltaN d s N := by
  sorry

/-- Proposition S3.1, the two consequences `W:eq:euclidean-pair-entropy` (S lines 510-518):
`log E_{Q^g_{N,b}}[e^{cN|𝖥_N^h|}] ≤ C N δ_N` and, for every probability law `f` with finite
relative entropy `H(f | Q^g_{N,b})`, `E_f[N|𝖥_N^h|] ≤ C{H(f|Q^g_{N,b}) + N δ_N}`.  The small
exponent `c > 0` and `C` depend only on the displayed parameters. -/
theorem euclidean_pair_entropy (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (M L bm bp B : ℝ)
    (hbm : 0 < bm) (hb : bm < bp) :
    ∃ c > 0, ∃ C : ℝ, ∀ ρ : Euc d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      (s = 0 → HasLogMoment (withDensityReal ρ) L) →
      ∀ h : Euc d → Euc d → ℝ, IsBoundedPairKernel s B h →
      ∀ N, 2 ≤ N → ∀ b ∈ Set.Icc bm bp,
        (Integrable (fun X : EucConfig d N => Real.exp (c * N * |pairEnergy h X (withDensityReal ρ)|))
            (modulatedGibbs (rieszKernel d s) N b (withDensityReal ρ)) ∧
          Real.log (∫ X : EucConfig d N, Real.exp (c * N * |pairEnergy h X (withDensityReal ρ)|)
            ∂(modulatedGibbs (rieszKernel d s) N b (withDensityReal ρ))) ≤ C * N * deltaN d s N) ∧
        ∀ f : Measure (EucConfig d N), IsProbabilityMeasure f →
          relEntropy f (modulatedGibbs (rieszKernel d s) N b (withDensityReal ρ)) < ⊤ →
          Integrable (fun X : EucConfig d N => N * |pairEnergy h X (withDensityReal ρ)|) f ∧
          ∫ X, N * |pairEnergy h X (withDensityReal ρ)| ∂f ≤
            C * ((relEntropy f (modulatedGibbs (rieszKernel d s) N b (withDensityReal ρ))).toReal +
              N * deltaN d s N) := by
  sorry

/-- Proposition S3.1, last sentence (S lines 518-519): "the same two assertions hold with
`h = g`, including for the whole-space logarithm" (for `s = 0` the kernel `g` is not in the
class of `IsBoundedPairKernel`, so this is a separate claim). -/
theorem euclidean_pair_entropy_self (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (M L bm bp : ℝ)
    (hbm : 0 < bm) (hb : bm < bp) :
    ∃ c > 0, ∃ C : ℝ, ∀ ρ : Euc d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      (s = 0 → HasLogMoment (withDensityReal ρ) L) →
      ∀ N, 2 ≤ N → ∀ b ∈ Set.Icc bm bp,
        (Integrable (fun X : EucConfig d N =>
            Real.exp (c * N * |modulatedEnergy (rieszKernel d s) X (withDensityReal ρ)|))
            (modulatedGibbs (rieszKernel d s) N b (withDensityReal ρ)) ∧
          Real.log (∫ X : EucConfig d N,
            Real.exp (c * N * |modulatedEnergy (rieszKernel d s) X (withDensityReal ρ)|)
            ∂(modulatedGibbs (rieszKernel d s) N b (withDensityReal ρ))) ≤ C * N * deltaN d s N) ∧
        ∀ f : Measure (EucConfig d N), IsProbabilityMeasure f →
          relEntropy f (modulatedGibbs (rieszKernel d s) N b (withDensityReal ρ)) < ⊤ →
          Integrable (fun X : EucConfig d N =>
            N * |modulatedEnergy (rieszKernel d s) X (withDensityReal ρ)|) f ∧
          ∫ X, N * |modulatedEnergy (rieszKernel d s) X (withDensityReal ρ)| ∂f ≤
            C * ((relEntropy f (modulatedGibbs (rieszKernel d s) N b (withDensityReal ρ))).toReal +
              N * deltaN d s N) := by
  sorry

end Pressure

/-! ### S3.3 `W:prop:euc-static` (S lines 928-952) -/

section EucStatic

variable {s : ℝ}

/-- The quadratic-estimate conclusion `W:eq:euc-quadratic` for the reference `ν`:
`D_N(h;ν)` has integrable background terms and `N Var_Q[D_N(h;ν)] ≤ C B² δ_N`. -/
def QuadraticVarianceBound (h : Euc d → Euc d → ℝ) (Q : Measure (EucConfig d N))
    (ν : Measure (Euc d)) (bound : ℝ) : Prop :=
  (∀ x, Integrable (fun y => h x y) ν) ∧
    Integrable (fun p : Euc d × Euc d => h p.1 p.2) (ν.prod ν) ∧
    ProbabilityTheory.evariance (fun X => centeredPairFunctional h X ν) Q ≤ ENNReal.ofReal bound

/-- Proposition S3.3 `W:prop:euc-static` (S lines 928-952), under the standing hypotheses of
S lines 903-926: `d ≥ 2`, `0 < s < d`, `β > 0`, `μ = ρ dx` a probability measure with
`ρ ∈ L^∞`, no lower bound on `ρ`; `g = |x|^{-s}` with the original normalisation and
`Q_N = e^{-βN F_N^g}/K_N μ^{⊗N}`.  Constants depend only on `d, s, β` and an upper bound `M`
for `‖ρ‖_∞`, not on a support radius, and are uniform for `β` in compact subsets of
`(0,∞)`: hence `C` is quantified before `ρ` and before `β ∈ [β₋,β₊]`.

Conclusions: `Q_N` is well defined; with `π_N = Q_N^{(1)}`:
`N Var_{Q_N}[μ_N(f)] ≤ C‖f‖²_{L²(μ)}`, `‖dπ_N/dμ - 1‖_{L²(μ)} ≤ Cδ_N`, `dπ_N/dμ ≤ C`
(`W:eq:euc-linear-marginal`); and for every symmetric measurable `h` with
`|h(x,y)| ≤ B(1+|x-y|^{-s})` off the diagonal and both `ν = μ`, `ν = π_N`,
`N Var_{Q_N}[D_N(h;ν)] ≤ C B² δ_N` (`W:eq:euc-quadratic`). -/
theorem euc_static (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) (βm βp M : ℝ) (hβm : 0 < βm)
    (hβ : βm ≤ βp) :
    ∃ C : ℝ, ∀ ρ : Euc d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ M) → ∀ β ∈ Set.Icc βm βp,
      ∀ N, 2 ≤ N →
        GibbsWellDefined (fun x y => rieszKernel d s (x - y)) N β (withDensityReal ρ) ∧
        (∀ f : Euc d → ℝ, MemLp f 2 (withDensityReal ρ) →
          ProbabilityTheory.evariance (linStat f) (modulatedGibbs (rieszKernel d s) N β (withDensityReal ρ)) ≤
            ENNReal.ofReal (C / N * ∫ x, f x ^ 2 ∂(withDensityReal ρ))) ∧
        HasMarginalDensityBounds
          (firstMarginal (modulatedGibbs (rieszKernel d s) N β (withDensityReal ρ)))
          (withDensityReal ρ) C (C * deltaN d s N) ∧
        ∀ B : ℝ, ∀ h : Euc d → Euc d → ℝ, IsBoundedPairKernel s B h →
          QuadraticVarianceBound h (modulatedGibbs (rieszKernel d s) N β (withDensityReal ρ))
            (withDensityReal ρ) (C * B ^ 2 * deltaN d s N / N) ∧
          QuadraticVarianceBound h (modulatedGibbs (rieszKernel d s) N β (withDensityReal ρ))
            (firstMarginal (modulatedGibbs (rieszKernel d s) N β (withDensityReal ρ)))
            (C * B ^ 2 * deltaN d s N / N) := by
  sorry

/-- The commutator kernel of a globally Lipschitz `v` (Lipschitz constant `Λ`) is in the
class of S3.3 with `B = sΛ` (S lines 949-951: "`B = s‖∇v‖_∞`"), for `0 < s < d`. -/
theorem commutatorKernel_isBounded (hs0 : 0 < s) (Λ : ℝ≥0) (v : Euc d → Euc d)
    (hv : LipschitzWith Λ v) : IsBoundedPairKernel s (s * Λ) (commutatorKernel d s v) := by
  sorry

/-- S3.3, "in particular" clause (S lines 949-951): the quadratic estimate for the physical
commutator `h(x,y) = (v(x)-v(y))·∇g(x-y)` of a globally Lipschitz `v`, with `B = s‖∇v‖_∞`
(`‖∇v‖_∞` = Lipschitz constant `Λ`). -/
theorem euc_static_commutator (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) (βm βp M : ℝ)
    (hβm : 0 < βm) (hβ : βm ≤ βp) :
    ∃ C : ℝ, ∀ ρ : Euc d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ M) → ∀ β ∈ Set.Icc βm βp,
      ∀ N, 2 ≤ N → ∀ (Λ : ℝ≥0) (v : Euc d → Euc d), LipschitzWith Λ v →
        QuadraticVarianceBound (commutatorKernel d s v)
          (modulatedGibbs (rieszKernel d s) N β (withDensityReal ρ)) (withDensityReal ρ)
          (C * (s * Λ) ^ 2 * deltaN d s N / N) ∧
        QuadraticVarianceBound (commutatorKernel d s v)
          (modulatedGibbs (rieszKernel d s) N β (withDensityReal ρ))
          (firstMarginal (modulatedGibbs (rieszKernel d s) N β (withDensityReal ρ)))
          (C * (s * Λ) ^ 2 * deltaN d s N / N) := by
  sorry

end EucStatic

/-! ### S3.4 `W:prop:euc-thermal` (S lines 1348-1384), remaining clauses -/

section EucThermal

variable {s : ℝ}

/-- Proposition S3.4, Gaussian comparison `W:eq:euc-thermal-bounds`
`c γ_{βa} ≤ ρ_β ≤ C γ_{βa}` (S lines 1357-1362) and the Poincaré inequality
`W:eq:euc-one-body-gap` `Var_{μ_β}(f) ≤ C/(cβa) ∫|∇f|² dμ_β` (S lines 1373-1377), with the
same `c, C` (the source writes `C/(cβa)` with the comparison constants).  The Poincaré
inequality is stated for `C¹` functions in `L²(μ_β)` with `∇f ∈ L²(μ_β)` (the closed form
domain is its closure). -/
theorem euc_thermal_gaussian_bounds (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) (a β : ℝ)
    (ha : 0 < a) (hβ : 0 < β) :
    ∃ c > 0, ∃ C : ℝ,
      (∀ x, c * gaussianComparison d a β x ≤ thermalDensity d s a β x ∧
        thermalDensity d s a β x ≤ C * gaussianComparison d a β x) ∧
      ∀ f : Euc d → ℝ, ContDiff ℝ 1 f → MemLp f 2 (thermalMeasure d s a β) →
        Integrable (fun x => ‖gradient f x‖ ^ 2) (thermalMeasure d s a β) →
        ProbabilityTheory.variance f (thermalMeasure d s a β) ≤
          C / (c * β * a) * ∫ x, ‖gradient f x‖ ^ 2 ∂(thermalMeasure d s a β) := by
  sorry

/-- Proposition S3.4, moments (S lines 1363-1364): `∫ e^{b|x|²} dμ_β < ∞` for `b < βa/2`
(in particular all polynomial moments exist). -/
theorem euc_thermal_moments (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) (a β : ℝ)
    (ha : 0 < a) (hβ : 0 < β) :
    (∀ b : ℝ, b < β * a / 2 →
      Integrable (fun x => Real.exp (b * ‖x‖ ^ 2)) (thermalMeasure d s a β)) ∧
    ∀ p : ℝ, 0 ≤ p → Integrable (fun x => ‖x‖ ^ p) (thermalMeasure d s a β) := by
  sorry

/-- Proposition S3.4, regularity (S lines 1365-1372): `ρ_β ∈ C^∞`, every derivative of
`g*μ_β` is bounded, `|∂^ℓ ρ_β(x)| ≤ C_ℓ (1+|x|)^{|ℓ|} e^{-βa|x|²/2}`
(`W:eq:euc-thermal-derivatives`, with the operator norm of the `|ℓ|`-th derivative), hence
`ρ_β ∈ W^{k,1} ∩ W^{k,∞}` for every `k` and all polynomially weighted derivatives are
integrable. -/
theorem euc_thermal_regularity (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) (a β : ℝ)
    (ha : 0 < a) (hβ : 0 < β) :
    ContDiff ℝ ∞ (thermalDensity d s a β) ∧
    ContDiff ℝ ∞ (convMeasure (rieszKernel d s) (thermalMeasure d s a β)) ∧
    (∀ k : ℕ, ∃ C : ℝ, ∀ x,
      ‖iteratedFDeriv ℝ k (convMeasure (rieszKernel d s) (thermalMeasure d s a β)) x‖ ≤ C) ∧
    (∀ k : ℕ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ k (thermalDensity d s a β) x‖ ≤
      C * (1 + ‖x‖) ^ k * Real.exp (-β * a * ‖x‖ ^ 2 / 2)) ∧
    (∀ k : ℕ, Integrable (fun x => ‖iteratedFDeriv ℝ k (thermalDensity d s a β) x‖) ∧
      ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ k (thermalDensity d s a β) x‖ ≤ C) ∧
    ∀ (k : ℕ) (p : ℝ), 0 ≤ p →
      Integrable (fun x => ‖x‖ ^ p * ‖iteratedFDeriv ℝ k (thermalDensity d s a β) x‖) := by
  sorry

/-- Proposition S3.4, last clauses (S lines 1378-1384): the canonical Gibbs ensemble
`P_N ∝ exp[-β(∑ V(x_i) + N⁻¹∑_{i<j} g(x_i-x_j))] dX_N` equals `Q_N(μ_β)` exactly, and its one-
and two-particle densities are bounded by `C μ_β` and `C μ_β^{⊗2}`, uniformly in `N`.
(That S3.3 applies to this class is the instantiation of `euc_static` with
`ρ = thermalDensity d s a β`, which is bounded by `thermalDensity_spec`.) -/
theorem euc_thermal_canonical (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) (a β : ℝ)
    (ha : 0 < a) (hβ : 0 < β) :
    (∀ N, canonicalGibbs (rieszKernel d s) (confinement a) N β =
      modulatedGibbs (rieszKernel d s) N β (thermalMeasure d s a β)) ∧
    ∃ C : ℝ≥0, ∀ N, 2 ≤ N →
      firstMarginal (canonicalGibbs (rieszKernel d s) (confinement a) N β) ≤
        C • thermalMeasure d s a β ∧
      secondMarginal (canonicalGibbs (rieszKernel d s) (confinement a) N β) ≤
        C • (thermalMeasure d s a β).prod (thermalMeasure d s a β) := by
  sorry

end EucThermal

/-! ### S3.5 `W:thm:r2-log-static` (S lines 1532-1563) -/

section LogStatic

/-- `ℓ(x) = ½ log(1+|x|²)` (`W:eq:r2-log-K-definition`, S line 1551). -/
def logWeight (x : Euc d) : ℝ := (1 / 2) * Real.log (1 + ‖x‖ ^ 2)

/-- `K(x,y) = -log|x-y| + ℓ(x) + ℓ(y)` (S line 1552; nonnegative, `W:eq:r2-log-positive-kernel`). -/
def sphericalLogKernel (x y : Euc d) : ℝ := -Real.log ‖x - y‖ + logWeight x + logWeight y

/-- A symmetric measurable kernel with `|h(x,y)| ≤ B(1 + K(x,y))` off the diagonal
(S line 1554). -/
structure IsLogBoundedPairKernel (B : ℝ) (h : Euc d → Euc d → ℝ) : Prop where
  measurable : Measurable fun p : Euc d × Euc d => h p.1 p.2
  symm : ∀ x y, h x y = h y x
  bound : ∀ x y, x ≠ y → |h x y| ≤ B * (1 + sphericalLogKernel x y)

/-- The spherical density upper bound `W:eq:r2-log-density` (S lines 1513-1515):
`ρ(x) ≤ A(1+|x|²)^{-d}` for a.e. `x`. -/
def HasSphericalBound (A : ℝ) (ρ : Euc d → ℝ) : Prop :=
  ∀ᵐ x ∂(volume : Measure (Euc d)), ρ x ≤ A * (1 + ‖x‖ ^ 2) ^ (-(d : ℝ))

/-- "`dπ_N/dμ(x) ≤ C(1+|x|²)^{-β/(2N)}`, `‖dπ_N/dμ - 1‖_{L²(μ)} ≤ C/N`"
(`W:eq:r2-log-main-linear`, S lines 1539-1540). -/
def HasLogMarginalDensityBounds (π μ : Measure (Euc d)) (C β : ℝ) (N : ℕ) : Prop :=
  ∃ φ : Euc d → ℝ, Measurable φ ∧ π = μ.withDensity (fun x => ENNReal.ofReal (φ x)) ∧
    (∀ x, 0 ≤ φ x ∧ φ x ≤ C * (1 + ‖x‖ ^ 2) ^ (-(β / (2 * N)))) ∧
    MemLp (fun x => φ x - 1) 2 μ ∧ l2Norm μ (fun x => φ x - 1) ≤ C / N

/-- Theorem S3.5 `W:thm:r2-log-static` (S lines 1532-1563), under the standing hypotheses of
S lines 1511-1530: `d ≥ 2`, `β > 0`, `g = -log|x|`, `μ = ρ dx` a probability measure with
`ρ(x) ≤ A(1+|x|²)^{-d}` a.e.; no lower bound on `ρ`.  Constants depend on `d, β, A` only, are
uniform for `β` in a compact subset of `(0,∞)` and bounded `A` (so `C` is quantified before
`ρ` and `β ∈ [β₋,β₊]`).

Conclusions: the normaliser of `W:eq:r2-log-gibbs` is in `(0,∞)` (every background term is
finite); with `π_N = Q_N^{(1)}`, for every `f ∈ L²(μ)`: `N Var(μ_N(f)) ≤ C‖f‖²_{L²(μ)}`,
`‖dπ_N/dμ - 1‖_{L²(μ)} ≤ C/N`, `dπ_N/dμ(x) ≤ C(1+|x|²)^{-β/(2N)}`; and for every symmetric
measurable `h` with `|h| ≤ B(1+K)` off the diagonal, for `ν = μ` and `ν = π_N`,
`N Var(D_N(h;ν)) ≤ CB²/N` (`W:eq:r2-log-main-quadratic`). -/
theorem r2_log_static (hd : 2 ≤ d) (βm βp A : ℝ) (hβm : 0 < βm) (hβ : βm ≤ βp) :
    ∃ C : ℝ, ∀ ρ : Euc d → ℝ, IsProbDensity ρ → HasSphericalBound A ρ → ∀ β ∈ Set.Icc βm βp,
      ∀ N, 2 ≤ N →
        GibbsWellDefined (fun x y => rieszKernel d 0 (x - y)) N β (withDensityReal ρ) ∧
        (∀ f : Euc d → ℝ, MemLp f 2 (withDensityReal ρ) →
          ProbabilityTheory.evariance (linStat f) (modulatedGibbs (rieszKernel d 0) N β (withDensityReal ρ)) ≤
            ENNReal.ofReal (C / N * ∫ x, f x ^ 2 ∂(withDensityReal ρ))) ∧
        HasLogMarginalDensityBounds
          (firstMarginal (modulatedGibbs (rieszKernel d 0) N β (withDensityReal ρ)))
          (withDensityReal ρ) C β N ∧
        ∀ B : ℝ, ∀ h : Euc d → Euc d → ℝ, IsLogBoundedPairKernel B h →
          QuadraticVarianceBound h (modulatedGibbs (rieszKernel d 0) N β (withDensityReal ρ))
            (withDensityReal ρ) (C * B ^ 2 / N / N) ∧
          QuadraticVarianceBound h (modulatedGibbs (rieszKernel d 0) N β (withDensityReal ρ))
            (firstMarginal (modulatedGibbs (rieszKernel d 0) N β (withDensityReal ρ)))
            (C * B ^ 2 / N / N) := by
  sorry

/-- The physical logarithmic commutator of a globally Lipschitz `v` satisfies
`|h| ≤ ‖∇v‖_∞ ≤ ‖∇v‖_∞ (1 + K)` (S lines 1559-1564, 1963-1964): it is in the class of S3.5
with `B = ‖∇v‖_∞` (= Lipschitz constant `Λ`), for `d ≥ 1`. -/
theorem commutatorKernel_log_isBounded (hd : 1 ≤ d) (Λ : ℝ≥0) (v : Euc d → Euc d)
    (hv : LipschitzWith Λ v) : IsLogBoundedPairKernel Λ (commutatorKernel d 0 v) := by
  sorry

/-- Theorem S3.5, "in particular" clause (S lines 1559-1562): the quadratic estimate for the
physical commutator `(v(x)-v(y))·∇g(x-y)` with `B = ‖∇v‖_∞`. -/
theorem r2_log_static_commutator (hd : 2 ≤ d) (βm βp A : ℝ) (hβm : 0 < βm) (hβ : βm ≤ βp) :
    ∃ C : ℝ, ∀ ρ : Euc d → ℝ, IsProbDensity ρ → HasSphericalBound A ρ → ∀ β ∈ Set.Icc βm βp,
      ∀ N, 2 ≤ N → ∀ (Λ : ℝ≥0) (v : Euc d → Euc d), LipschitzWith Λ v →
        QuadraticVarianceBound (commutatorKernel d 0 v)
          (modulatedGibbs (rieszKernel d 0) N β (withDensityReal ρ)) (withDensityReal ρ)
          (C * (Λ : ℝ) ^ 2 / N / N) ∧
        QuadraticVarianceBound (commutatorKernel d 0 v)
          (modulatedGibbs (rieszKernel d 0) N β (withDensityReal ρ))
          (firstMarginal (modulatedGibbs (rieszKernel d 0) N β (withDensityReal ρ)))
          (C * (Λ : ℝ) ^ 2 / N / N) := by
  sorry

end LogStatic

/-! ### S3.7 `W:lem:r2-static-Stein` (S lines 1986-2006) -/

section StaticStein

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- The finite-coordinate Stein-type identity of S3.7 (S lines 1990-1994):
`E[X_i f(X)] = E[R_i f(X)] + ∑_j E[T_ij ∂_j f(X)]` for every bounded smooth `f` with bounded
first derivative. -/
def SteinIdentity {n : ℕ} (X R : Ω → EuclideanSpace ℝ (Fin n))
    (T : Ω → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ f → (∃ Cf, ∀ x, |f x| ≤ Cf) →
    (∃ Cf, ∀ x, ‖fderiv ℝ f x‖ ≤ Cf) → ∀ i : Fin n,
      ∫ w, X w i * f (X w) ∂P =
        ∫ w, R w i * f (X w) ∂P +
          ∑ j : Fin n, ∫ w, T w i j * fderiv ℝ f (X w) (EuclideanSpace.single j 1) ∂P

/-- Lemma S3.7 `W:lem:r2-static-Stein`, finite-dimensional part (S lines 1986-2001):
`X, R` integrable random vectors in `ℝⁿ`, `T` a random matrix with integrable trace norm
satisfying the Stein-type identity; `G` a centered Gaussian of any positive semidefinite
covariance `C` (`C_ij = E[G_i G_j]`, degenerate allowed); `F ∈ C²` with bounded first and
second derivatives.  Then
`|E F(X) - E F(G)| ≤ ‖DF‖_∞ E|R| + ½ ‖D²F‖_∞ E‖T - C‖₁` (`W:eq:r2-owning-static-Stein`). -/
theorem static_stein {n : ℕ} (X R : Ω → EuclideanSpace ℝ (Fin n))
    (T : Ω → Matrix (Fin n) (Fin n) ℝ) (hX : Integrable X P) (hR : Integrable R P)
    (hTm : ∀ i j, AEStronglyMeasurable (fun w => T w i j) P)
    (hT : Integrable (fun w => traceNormMatrix (T w)) P) (hid : SteinIdentity P X R T)
    (G : Ω → EuclideanSpace ℝ (Fin n)) (hG : AEMeasurable G P)
    (hGauss : IsCenteredGaussian (law P G)) (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : ∀ i j, C i j = ∫ w, G w i * G w j ∂P)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ContDiff ℝ 2 F) (D₁ D₂ : ℝ)
    (hD₁ : ∀ x, ‖fderiv ℝ F x‖ ≤ D₁) (hD₂ : ∀ x, ‖iteratedFDeriv ℝ 2 F x‖ ≤ D₂) :
    Integrable (fun w => F (X w)) P ∧ Integrable (fun w => F (G w)) P ∧
    |∫ w, F (X w) ∂P - ∫ w, F (G w) ∂P| ≤
      D₁ * ∫ w, ‖R w‖ ∂P + (1 / 2) * D₂ * ∫ w, traceNormMatrix (T w - C) ∂P :=
  HRS.Whole.Stein.stein_c2 P X R T hX hR hTm hT hid G hG hGauss C hC F hF D₁ D₂ hD₁ hD₂

/-- The orthogonal projection onto the first `n` coordinates of a Hilbert basis. -/
def hilbertProj {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (e : HilbertBasis ℕ ℝ H) (n : ℕ) (x : H) : H :=
  ∑ i ∈ Finset.range n, inner ℝ (e i) x • e i

/-- The first `n` coordinates `(⟨x, e_i⟩)_{i<n}` as a vector of `ℝⁿ`. -/
def hilbertCoords {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (e : HilbertBasis ℕ ℝ H) (n : ℕ) (x : H) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i => inner ℝ (e i) x

/-- Lemma S3.7, Hilbert-space clause (S lines 2002-2005): on a separable Hilbert space, if the
finite-coordinate identities hold for the coordinate vectors `(⟨X,e_i⟩)_{i<n}` with remainders
`R_n`, matrices `T_n` and the Gaussian coordinate covariances `C_n`, with the uniform bounds
`E|R_n| ≤ r`, `E‖T_n - C_n‖₁ ≤ τ`, and the particle and Gaussian projection tails tend to zero
in `L¹`, then `|E F(X) - E F(G)| ≤ ‖DF‖_∞ r + ½ ‖D²F‖_∞ τ`. -/
theorem static_stein_hilbert {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] (e : HilbertBasis ℕ ℝ H)
    (X G : Ω → H) (hX : Integrable X P) (hG : AEMeasurable G P)
    (hGauss : IsCenteredGaussian (law P G)) (r τ : ℝ)
    (hfin : ∀ n : ℕ, ∃ (R : Ω → EuclideanSpace ℝ (Fin n)) (T : Ω → Matrix (Fin n) (Fin n) ℝ),
      Integrable R P ∧ (∀ i j, AEStronglyMeasurable (fun w => T w i j) P) ∧
      Integrable (fun w => traceNormMatrix (T w)) P ∧
      SteinIdentity P (fun w => hilbertCoords e n (X w)) R T ∧
      ∫ w, ‖R w‖ ∂P ≤ r ∧
      ∫ w, traceNormMatrix (T w - Matrix.of fun i j : Fin n =>
        ∫ w', inner ℝ (e i) (G w') * inner ℝ (e j) (G w') ∂P) ∂P ≤ τ)
    (htailX : Tendsto (fun n => ∫ w, ‖X w - hilbertProj e n (X w)‖ ∂P) atTop (𝓝 0))
    (htailG : Tendsto (fun n => ∫ w, ‖G w - hilbertProj e n (G w)‖ ∂P) atTop (𝓝 0))
    (F : H → ℝ) (hF : ContDiff ℝ 2 F) (D₁ D₂ : ℝ)
    (hD₁ : ∀ x, ‖fderiv ℝ F x‖ ≤ D₁) (hD₂ : ∀ x, ‖iteratedFDeriv ℝ 2 F x‖ ≤ D₂) :
    Integrable (fun w => F (X w)) P ∧ Integrable (fun w => F (G w)) P ∧
    |∫ w, F (X w) ∂P - ∫ w, F (G w) ∂P| ≤ D₁ * r + (1 / 2) * D₂ * τ :=
  HRS.Whole.Stein.hilbert_main P e X G hX hG hGauss r τ hfin htailX htailG F hF D₁ D₂ hD₁ hD₂

end StaticStein

end HRS.Whole
