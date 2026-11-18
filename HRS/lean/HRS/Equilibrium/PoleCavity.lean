/-
# HRS.Equilibrium.PoleCavity — pole insertion, first marginals, critical cavity (EQ-01a)

Section 4 of the main manuscript, results 4.1-4.9 (source lines 3547-4424):

* Lemma 4.1 `M:A:lem:pole` (variance and densities with an external pole),
* Proposition 4.2 `M:A:prop:marginal` (full first marginal, `L²` and uniform),
* Proposition 4.3 `M:A:prop:quadratic` (centered singular quadratic statistic),
* Lemmas 4.4-4.7 and Propositions 4.8-4.9 at the critical exponent `s = d/2`
  (`M:R:lem:product-transfer`, `M:R:lem:integrals`, `M:R:lem:cavity`, `M:R:lem:Taylor`,
  `M:R:prop:conditional-expectation`, `M:R:prop:insertion-coefficient`).

Standing hypotheses of Section 4 (source lines 3339-3396): `d ≥ 2`, `0 ≤ s < d`, a fixed
physical inverse temperature `β > 0` (constants may depend on it), and a fixed smooth positive
background `μ = ρ dx` (`SmoothPosDensity ρ`); `Q_{N,β}(μ)` is `modulatedGibbs`. Sections
`R:sec:*` (Lemmas 4.4-4.9) are the proof of Proposition 2.10 and assume `s = d/2`
(source line 1037).

Objects that the source introduces only inside proofs and whose construction depends on
choices (the weak calibrated reference `R_N` of `A:eq:split`/`A:eq:calibration`) are not
specified here; see the report for the affected clauses (last sentence of Lemma 4.1, second
summand of Proposition 4.2).

Junk-value conventions: variances are `evariance` (`ℝ≥0∞`); integrals of nonnegative
quantities are `lintegral`s; `L²` norms are `eLpNorm`; densities are `Measure.rnDeriv` together
with an absolute-continuity conjunct, and `.toReal` of a density is used only under `∀ᵐ` or
`eLpNorm`, where the density is finite a.e. Kernel envelopes are imposed only off the diagonal.
-/
import HRS.Energy.Modulated
import HRS.Kernel.GradBasic

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d : ℕ}

/-! ### Shared definitions for Section 4 -/

/-- The Euclidean periodic distance `|x - y|` on `𝕋^d` (each coordinate of `UnitAddCircle`
has the norm "distance to the nearest integer"). -/
def Torus.eucDist (x y : Torus d) : ℝ := Real.sqrt (∑ i, ‖x i - y i‖ ^ 2)

/-- A smooth strictly positive probability density (the standing background of Section 4,
source line 3388). -/
structure SmoothPosDensity (ρ : Torus d → ℝ) : Prop where
  density : IsProbDensity ρ
  smooth : Torus.IsSmooth ρ
  pos : ∀ x, 0 < ρ x

/-- Normalised exponential tilt `e^{w} P / ∫ e^{w} dP`, with a `lintegral` normaliser (so an
infinite normaliser gives the zero measure rather than a junk positive multiple). -/
def tiltMeasure {α : Type*} [MeasurableSpace α] (P : Measure α) (w : α → ℝ) : Measure α :=
  (∫⁻ a, ENNReal.ofReal (Real.exp (w a)) ∂P)⁻¹ •
    P.withDensity fun a => ENNReal.ofReal (Real.exp (w a))

/-- The ordered pair sum `∑_{i<j} g(y_i - y_j)`. -/
def pairSum (g : Torus d → ℝ) {n : ℕ} (Y : Config d n) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), g (Y i - Y j)

/-- The cavity law `A:eq:cavity-law` / `R:eq:cavity` (source lines 3553-3554, 4179):
`dP_n^0 ∝ exp(-λ ∑_{i<j} g(y_i - y_j) + β ∑_i (g*μ)(y_i)) dμ^{⊗n}`. In the source `n = N - 1`
and `λ = β/N`. -/
def cavityLaw (g : Torus d → ℝ) (μ : Measure (Torus d)) (n : ℕ) (lam β : ℝ) :
    Measure (Config d n) :=
  tiltMeasure (Measure.pi fun _ : Fin n => μ)
    fun Y => -lam * pairSum g Y + β * ∑ i, convMeasure g μ (Y i)

/-- The pole law `A:eq:pole-law` / `R:eq:pole` (source lines 3556-3559, 4180):
`dP_n^{x,t} = e^{-tλ∑_i g(x - y_i)} dP_n^0 / E_{P_n^0}[e^{-tλ∑_i g(x - y_i)}]`. -/
def poleLaw (g : Torus d → ℝ) (μ : Measure (Torus d)) (n : ℕ) (lam β : ℝ) (x : Torus d)
    (t : ℝ) : Measure (Config d n) :=
  tiltMeasure (cavityLaw g μ n lam β) fun Y => -(t * lam) * ∑ i, g (x - Y i)

/-- The two-coordinate marginal `Law(y_i, y_j)`. -/
def twoMarginal {n : ℕ} (P : Measure (Config d n)) (i j : Fin n) :
    Measure (Torus d × Torus d) :=
  P.map fun Y => (Y i, Y j)

/-- The singular kernel envelope `1 + r^{-s}` (`s > 0`) or `1 + |log r|` (`s = 0`) of
Proposition 4.3 (source lines 3764-3765). -/
def singEnvelope (s r : ℝ) : ℝ := if s = 0 then 1 + |Real.log r| else 1 + r ^ (-s)

/-- `D_N(h;ν) = N⁻² ∑_{i≠j} h(x_i,x_j) - 2 μ_N(∫ h(·,y) dν(y)) + ∬ h dν^{⊗2}`
(`A:eq:D-definition`, source lines 3766-3770; also `Q:eq:deleted-D` with `ν = μ`). -/
def quadStat {N : ℕ} (h : Torus d → Torus d → ℝ) (ν : Measure (Torus d)) (X : Config d N) : ℝ :=
  (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, h (X i) (X j)
    - 2 * ((1 / (N : ℝ)) * ∑ i, ∫ y, h (X i) y ∂ν)
    + ∫ x, ∫ y, h x y ∂ν ∂ν

/-- The shifted kernel `g_+ = g + c` (source line 4172; `c` is chosen with `g + c ≥ 0`). -/
def gPlus (d : ℕ) (s c : ℝ) (z : Torus d) : ℝ := periodicRiesz d s z + c

/-- The cavity law of `R:eq:cavity` with `n = N - 1`, `λ = β/N`, kernel `g_+` and common
field `β h`, `h = g_+ * μ`. (Adding the constant `c` does not change the normalised law.) -/
def critCavity (d : ℕ) (s c β : ℝ) (ρ : Torus d → ℝ) (N : ℕ) : Measure (Config d (N - 1)) :=
  cavityLaw (gPlus d s c) (withDensityReal ρ) (N - 1) (β / N) β

/-- The pole law `P_n^{x,t}` of `R:eq:pole`. -/
def critPole (d : ℕ) (s c β : ℝ) (ρ : Torus d → ℝ) (N : ℕ) (x : Torus d) (t : ℝ) :
    Measure (Config d (N - 1)) :=
  poleLaw (gPlus d s c) (withDensityReal ρ) (N - 1) (β / N) β x t

/-- The insertion pressure `F_{N,x}(t) = log E_{P_n^0}[e^{-tλ∑_i g_+(x - y_i)}]`
(`R:eq:insertion`, source line 4249; `A:eq:insertion-pressure`, line 3624). -/
def insertionPressure (d : ℕ) (s c β : ℝ) (ρ : Torus d → ℝ) (N : ℕ) (x : Torus d) (t : ℝ) : ℝ :=
  Real.log (∫ Y, Real.exp (-(t * (β / N)) * ∑ i, gPlus d s c (x - Y i))
    ∂(critCavity d s c β ρ N))

/-- The insertion defect `D_N(x) = F_{N,x}(1) - F_{N,x}'(0)` with
`F_{N,x}'(0) = -λ E_{P_n^0}[∑_i g_+(x - y_i)]` (`R:eq:insertion`, source line 4250). The
theorem `cavity_response` asserts that this one-sided derivative exists and has this value. -/
def insertionDefect (d : ℕ) (s c β : ℝ) (ρ : Torus d → ℝ) (N : ℕ) (x : Torus d) : ℝ :=
  insertionPressure d s c β ρ N x 1 +
    (β / N) * ∫ Y, ∑ i, gPlus d s c (x - Y i) ∂(critCavity d s c β ρ N)

/-- The truncation `g_H = min(g_+, H)` of Lemma 4.5 (source line 4211). -/
def gTrunc (d : ℕ) (s c H : ℝ) (z : Torus d) : ℝ := min (gPlus d s c z) H

/-- `H(v) = e^{-v} - 1 + v` (Lemma 4.7, source line 4300). -/
def taylorH (v : ℝ) : ℝ := Real.exp (-v) - 1 + v

/-- The conditional field `v_Y(y) = λ ∑_{j ≠ i} g_+(y - y_j) - β h(y)`, `h = g_+ * μ`
(`R:eq:conditional-density`, source line 4279), as a function of the whole cavity
configuration (it does not depend on the coordinate `i`). -/
def cavityField (d : ℕ) (s c β : ℝ) (ρ : Torus d → ℝ) (N : ℕ) {n : ℕ} (i : Fin n)
    (Y : Config d n) (y : Torus d) : ℝ :=
  (β / N) * ∑ j ∈ Finset.univ.erase i, gPlus d s c (y - Y j)
    - β * convMeasure (gPlus d s c) (withDensityReal ρ) y

/-- The σ-algebra generated by all coordinates except `i` (conditioning on `y_2,…,y_n`). -/
@[reducible] def othersSigma {n : ℕ} (i : Fin n) : MeasurableSpace (Config d n) :=
  MeasurableSpace.comap (fun (Y : Config d n) (j : {j : Fin n // j ≠ i}) => Y j)
    MeasurableSpace.pi

/-- `|𝕊^{d-1}| = 2π^{d/2}/Γ(d/2)`. -/
def sphereArea (d : ℕ) : ℝ := 2 * Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2)

/-! ### Lemma 4.1: one repulsive pole (all `0 ≤ s < d`) -/

/-! ### Helpers for Lemma 4.1 (probability measures) -/

namespace PoleCavityAux

variable {s : ℝ}

theorem measurable_periodicRiesz (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    Measurable (periodicRiesz d s) := by
  let εn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hεn : Tendsto εn atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
    exact Filter.Eventually.of_forall fun n => by simp only [εn, Set.mem_Ioi]; positivity
  refine measurable_of_tendsto_metrizable
    (f := fun n x => if x = 0 then periodicRiesz d s 0 else heatRiesz d s (εn n) x)
    (fun n => ?_) ?_
  · exact Measurable.ite (measurableSet_singleton 0) measurable_const
      (continuous_heatRiesz hsd _ (by simp only [εn]; positivity)).measurable
  · rw [tendsto_pi_nhds]
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · simp only [hx, ite_false]
      exact (periodicRiesz_tendsto hd hs0 hsd x hx).comp hεn


theorem continuous_of_lift' {E : Type*} [TopologicalSpace E] {f : Torus d → E}
    (h : Continuous (Torus.lift f)) : Continuous f := by
  have h1 : IsOpenQuotientMap
      (Pi.map (fun _ : Fin d => ((↑) : ℝ → UnitAddCircle))) :=
    IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk
  have h2 : IsOpenQuotientMap (Torus.mk : Euc d → Torus d) :=
    h1.comp (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).isOpenQuotientMap
  exact h2.isQuotientMap.continuous_iff.2 h

theorem continuous_of_smoothPos {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) : Continuous ρ :=
  continuous_of_lift' (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift ρ) from hρ.smooth).continuous

theorem exists_density_bound {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ x, ρ x ≤ Λ := by
  obtain ⟨Λ, hΛ⟩ := isCompact_univ.exists_bound_of_continuousOn (f := ρ) (continuous_of_smoothPos hρ).continuousOn
  exact ⟨max Λ 1, by positivity, fun x => (le_abs_self _).trans ((hΛ x trivial).trans (le_max_left _ _))⟩


theorem isProbabilityMeasure_mu {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) :
    IsProbabilityMeasure (withDensityReal ρ) := by
  refine ⟨?_⟩
  unfold withDensityReal
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hint : Integrable ρ := by
    by_contra h
    have := hρ.density.integral_one
    rw [integral_undef h] at this
    norm_num at this
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hρ.density.nonneg),
    hρ.density.integral_one]
  simp

theorem tilt_isProb {α : Type*} [MeasurableSpace α] (P : Measure α) [IsProbabilityMeasure P]
    (w : α → ℝ) (hw : Measurable w) (W : ℝ) (hW : ∀ a, w a ≤ W) :
    IsProbabilityMeasure (tiltMeasure P w) := by
  set Z := ∫⁻ a, ENNReal.ofReal (Real.exp (w a)) ∂P with hZ
  have hZfin : Z ≠ ∞ := by
    apply ne_of_lt
    calc Z ≤ ∫⁻ _a, ENNReal.ofReal (Real.exp W) ∂P :=
          lintegral_mono fun a => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (hW a))
      _ = ENNReal.ofReal (Real.exp W) := by simp
      _ < ∞ := ENNReal.ofReal_lt_top
  have hZpos : Z ≠ 0 := by
    intro h0
    have hm : Measurable fun a => ENNReal.ofReal (Real.exp (w a)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hw)
    rw [hZ, lintegral_eq_zero_iff hm] at h0
    have h1 : ∀ᵐ a ∂P, False := h0.mono fun a ha => by
      have := (ENNReal.ofReal_eq_zero.1 ha)
      exact absurd this (not_le.2 (Real.exp_pos _))
    obtain ⟨a, ha⟩ := h1.exists
    exact ha
  refine ⟨?_⟩
  unfold tiltMeasure
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hZpos hZfin


theorem pairSum_ge (g : Torus d → ℝ) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ z, -B ≤ g z) {n : ℕ}
    (Y : Config d n) : -(B * n * n) ≤ pairSum g Y := by
  unfold pairSum
  have h1 : ∀ i : Fin n, -(B * n) ≤ ∑ j ∈ Finset.univ.filter (fun j => i < j), g (Y i - Y j) := by
    intro i
    calc -(B * n) ≤ -(B * ((Finset.univ.filter (fun j : Fin n => i < j)).card : ℝ)) := by
          have : ((Finset.univ.filter (fun j : Fin n => i < j)).card : ℝ) ≤ n := by
            exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
          nlinarith
      _ = ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), (-B) := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun j _ => hB _
  calc -(B * n * n) = ∑ _i : Fin n, -(B * n) := by simp; ring
    _ ≤ _ := Finset.sum_le_sum fun i _ => h1 i

theorem measurable_pairSum {g : Torus d → ℝ} (hg : Measurable g) {n : ℕ} :
    Measurable (fun Y : Config d n => pairSum g Y) := by
  unfold pairSum
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  exact hg.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))

theorem measurable_convMeasure {g : Torus d → ℝ} (hg : Measurable g) (μ : Measure (Torus d))
    [SFinite μ] : Measurable (convMeasure g μ) := by
  unfold convMeasure
  have : StronglyMeasurable (Function.uncurry fun x y : Torus d => g (x - y)) :=
    (hg.comp (measurable_fst.sub measurable_snd)).stronglyMeasurable
  exact (this.integral_prod_right' (ν := μ)).measurable

theorem sum_ge_of_ge (g : Torus d → ℝ) {B : ℝ} (hB : ∀ z, -B ≤ g z) {n : ℕ} (x : Torus d)
    (Y : Config d n) : -(B * n) ≤ ∑ i, g (x - Y i) := by
  calc -(B * n) = ∑ _i : Fin n, (-B) := by simp [mul_comm]
    _ ≤ _ := Finset.sum_le_sum fun i _ => hB _

theorem cavity_weight_le (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) (n : ℕ) (lam : ℝ) (hlam : 0 ≤ lam) :
    ∃ W : ℝ, ∀ Y : Config d n,
      -lam * pairSum (periodicRiesz d s) Y +
        β * ∑ i, convMeasure (periodicRiesz d s) (withDensityReal ρ) (Y i) ≤ W := by
  obtain ⟨B, hB⟩ := periodicRiesz_ge (d := d) hd hs0 hsd
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_density_bound hρ
  obtain ⟨C, hC⟩ := convMeasure_bounded hd hs0 hsd ρ hρ.density Λ hΛ
  have hB' : ∀ z, -(max B 0) ≤ periodicRiesz d s z := fun z =>
    (neg_le_neg (le_max_left _ _)).trans (hB z)
  refine ⟨lam * (max B 0 * n * n) + |β| * (n * |C|), fun Y => ?_⟩
  have h1 := pairSum_ge (periodicRiesz d s) (le_max_right B 0) hB' Y
  have h2 : -lam * pairSum (periodicRiesz d s) Y ≤ lam * (max B 0 * n * n) := by
    have := mul_le_mul_of_nonneg_left (neg_le_neg h1) hlam
    linarith
  have h3 : β * ∑ i, convMeasure (periodicRiesz d s) (withDensityReal ρ) (Y i) ≤
      |β| * (n * |C|) := by
    have h4 : |∑ i, convMeasure (periodicRiesz d s) (withDensityReal ρ) (Y i)| ≤ n * |C| := by
      calc _ ≤ ∑ i, |convMeasure (periodicRiesz d s) (withDensityReal ρ) (Y i)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin n, |C| := Finset.sum_le_sum fun i _ => (hC _).trans (le_abs_self C)
        _ = n * |C| := by simp
    calc _ ≤ |β * ∑ i, convMeasure (periodicRiesz d s) (withDensityReal ρ) (Y i)| := le_abs_self _
      _ = |β| * |∑ i, convMeasure (periodicRiesz d s) (withDensityReal ρ) (Y i)| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left h4 (abs_nonneg _)
  linarith


theorem cavity_isProb (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) (n : ℕ) (lam : ℝ) (hlam : 0 ≤ lam) :
    IsProbabilityMeasure (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) := by
  have := isProbabilityMeasure_mu hρ
  obtain ⟨W, hW⟩ := cavity_weight_le hd hs0 hsd β hρ n lam hlam
  have hg := measurable_periodicRiesz hd hs0 hsd
  unfold cavityLaw
  refine tilt_isProb _ _ ?_ W hW
  exact ((measurable_pairSum hg).const_mul _).add
    ((Finset.measurable_sum _ fun i _ =>
      (measurable_convMeasure hg _).comp (measurable_pi_apply i)).const_mul _)

theorem pole_isProb (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) (n : ℕ) (lam : ℝ) (hlam : 0 ≤ lam) (x : Torus d) (t : ℝ)
    (ht : 0 ≤ t) :
    IsProbabilityMeasure (poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x t) := by
  have := cavity_isProb hd hs0 hsd β hρ n lam hlam
  obtain ⟨B, hB⟩ := periodicRiesz_ge (d := d) hd hs0 hsd
  have hg := measurable_periodicRiesz hd hs0 hsd
  have hB' : ∀ z, -(max B 0) ≤ periodicRiesz d s z := fun z =>
    (neg_le_neg (le_max_left _ _)).trans (hB z)
  unfold poleLaw
  refine tilt_isProb _ _ ?_ ((t * lam) * (max B 0 * n)) fun Y => ?_
  · exact (Finset.measurable_sum _ fun i _ =>
      hg.comp (measurable_const.sub (measurable_pi_apply i))).const_mul _
  · have h1 := sum_ge_of_ge (periodicRiesz d s) hB' x Y
    have := mul_le_mul_of_nonneg_left (neg_le_neg h1) (mul_nonneg ht hlam)
    linarith

end PoleCavityAux

section AllExponents

variable {s : ℝ}

/-- The cavity and pole laws are probability measures (`N ≥ 2`, `0 ≤ t ≤ 1`, kernel bounded
below so the tilts are bounded above). Makes the bounds below non-vacuous. -/
theorem isProbabilityMeasure_poleLaw (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ)
    (hβ : 0 < β) (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (N : ℕ) (hN : 2 ≤ N)
    (x : Torus d) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β) ∧
      IsProbabilityMeasure
        (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam : 0 ≤ β / N := by positivity
  exact ⟨PoleCavityAux.cavity_isProb hd hs0 hsd β hρ _ _ hlam,
    PoleCavityAux.pole_isProb hd hs0 hsd β hρ _ _ hlam x t ht.1⟩

/-! ### Route for Lemma 4.1 (EQ-01a-1)

One- and two-particle densities (`pole_density_clauses`, proved): the pole law is
`c • (μ^{⊗n}).withDensity (exp E)` with `E = -λ pairSum + β ∑ g*μ(y_i) - tλ ∑ g(x - y_i)`
(`poleLaw_eq`).  For a set `S` of `k ≤ 2` coordinates split `E = E_S(u) + E_{Sᶜ}(v) - λ X(u,v)`
(`blockExpo_split`, evenness of `g`).  The cross term is `≥ -B k n` so the `u`-dependence of the
weight is at most `e^{K} e^{-tλ ∑_{a∈S} g(x-u_a)}`, and the normaliser of the conditional
density of `u` given `v` is at least `e^{-K'}` by Jensen (`jensen_lintegral`,
`KerData.jensen_block`; uses `λ n ≤ β`, `g ≥ -B`, `‖g*μ‖_∞ ≤ Cc`, `g ∈ L¹(μ)`).  Hence
`W(u,v) ≤ C φ(u) ∫ W(u',v) du'` (`H_pole`), and Fubini over `Fin n ≃ S ⊔ Sᶜ`
(`marginal_le_of_cond`, `pole_restr_le`) gives the marginal bounds.

Variance clause (`pole_variance_clause`, proved in `HRS.Equilibrium.PoleVariance`): not provable by the
conditional-density bounds, since `P` is not a product measure (Efron-Stein fails).  The source
argument uses the split `g = g_L + q - c` (`A:eq:split`, heat decomposition), Wu's conditional
variance inequality for the weak reference with Dobrushin coefficients `κ/N`, the calibration of the
finite positive block (`A:eq:calibration`) and the bounded-density transfer
`A:eq:bounded-transfer`; see the route comment of `PoleVariance.lean`. -/

namespace PoleCavityAux

section PoleDensity

set_option linter.unusedSectionVars false

theorem rnDeriv_le_of_le_withDensity {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    [SigmaFinite μ] [IsFiniteMeasure ν] (f : α → ℝ≥0∞) (h : ν ≤ μ.withDensity f) :
    ν ≪ μ ∧ ∀ᵐ y ∂μ, ν.rnDeriv μ y ≤ f y := by
  have hac : ν ≪ μ := by
    refine (Measure.absolutelyContinuous_of_le h).trans ?_
    exact withDensity_absolutelyContinuous μ f
  refine ⟨hac, ?_⟩
  refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv ν μ) ?_
  intro s hs _
  rw [Measure.setLIntegral_rnDeriv hac, ← withDensity_apply _ hs]
  exact h s

section Cond

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
  {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p]

local notation "eP" => MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => α) p

/-- Restriction of a configuration to the coordinates satisfying `p`. -/
def restrS (Y : ι → α) : {a // p a} → α := fun a => Y a.1

/-- Replace the `p`-coordinates of `Y` by `u`. -/
def modifyS (Y : ι → α) (u : {a // p a} → α) : ι → α :=
  (eP).symm (u, fun a => Y a.1)

theorem measurable_restrS : Measurable (restrS (α := α) p) :=
  measurable_pi_iff.2 fun a => measurable_pi_apply a.1

theorem lintegral_pi_split (F : (ι → α) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ Y, F Y ∂(Measure.pi fun _ : ι => μ) =
      ∫⁻ v, ∫⁻ u, F ((eP).symm (u, v))
        ∂(Measure.pi fun _ : {a // p a} => μ) ∂(Measure.pi fun _ : {a // ¬ p a} => μ) := by
  have hmp := MeasureTheory.measurePreserving_piEquivPiSubtypeProd (fun _ : ι => μ) p
  have h1 : ∫⁻ Y, F Y ∂(Measure.pi fun _ : ι => μ) =
      ∫⁻ q, F ((eP).symm q) ∂((Measure.pi fun _ : {a // p a} => μ).prod
        (Measure.pi fun _ : {a // ¬ p a} => μ)) := by
    have := hmp.lintegral_comp_emb (eP).measurableEmbedding (fun q => F ((eP).symm q))
    refine Eq.trans ?_ this
    refine lintegral_congr fun a => ?_
    exact congrArg F ((eP).symm_apply_apply a).symm
  rw [h1, lintegral_prod_symm']
  exact hF.comp (eP).symm.measurable

theorem restrS_symm (u : {a // p a} → α) (v : {a // ¬ p a} → α) :
    restrS p ((eP).symm (u, v)) = u := by
  funext a
  simp [restrS, a.2]

theorem modifyS_symm (u u' : {a // p a} → α) (v : {a // ¬ p a} → α) :
    modifyS p ((eP).symm (u, v)) u' =
      (eP).symm (u', v) := by
  unfold modifyS
  congr 2
  funext a
  simp [a.2]

theorem lintegral_restrS (G : ({a // p a} → α) → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ Y, G (restrS p Y) ∂(Measure.pi fun _ : ι => μ) =
      ∫⁻ u, G u ∂(Measure.pi fun _ : {a // p a} => μ) := by
  have := lintegral_pi_split μ p (G ∘ restrS p) (hG.comp (measurable_restrS p))
  simp only [Function.comp_apply, restrS_symm] at this
  rw [this]
  simp

theorem marginal_le_of_cond (W : (ι → α) → ℝ≥0∞) (hW : Measurable W) (c : ℝ≥0∞)
    (hc : c * ∫⁻ Y, W Y ∂(Measure.pi fun _ : ι => μ) = 1)
    (φ : ({a // p a} → α) → ℝ≥0∞) (hφ : Measurable φ) (C : ℝ≥0∞)
    (H : ∀ Y, W Y ≤ C * φ (restrS p Y) *
      ∫⁻ u, W (modifyS p Y u) ∂(Measure.pi fun _ : {a // p a} => μ))
    (T : Set ({a // p a} → α)) (hT : MeasurableSet T) :
    c * ∫⁻ Y, (restrS p ⁻¹' T).indicator W Y ∂(Measure.pi fun _ : ι => μ) ≤
      C * ∫⁻ Y, T.indicator φ (restrS p Y) ∂(Measure.pi fun _ : ι => μ) := by
  set νS := Measure.pi fun _ : {a // p a} => μ with hνS
  set νC := Measure.pi fun _ : {a // ¬ p a} => μ with hνC
  have hI : Measurable fun v => ∫⁻ u, W ((eP).symm (u, v)) ∂νS := by
    have : Measurable fun q : ({a // p a} → α) × ({a // ¬ p a} → α) => W ((eP).symm q) :=
      hW.comp (eP).symm.measurable
    exact this.lintegral_prod_left'
  have hind : Measurable ((restrS p ⁻¹' T).indicator W) :=
    hW.indicator ((measurable_restrS p) hT)
  have h1 := lintegral_pi_split μ p _ hind
  have h2 := lintegral_pi_split μ p _ hW
  have h3 := lintegral_restrS μ p (T.indicator φ) (hφ.indicator hT)
  have key : ∀ v, ∫⁻ u, (restrS p ⁻¹' T).indicator W ((eP).symm (u, v)) ∂νS ≤
      C * (∫⁻ u, T.indicator φ u ∂νS) * ∫⁻ u, W ((eP).symm (u, v)) ∂νS := by
    intro v
    have : ∀ u, (restrS p ⁻¹' T).indicator W ((eP).symm (u, v)) ≤
        (T.indicator φ u) * (C * ∫⁻ u', W ((eP).symm (u', v)) ∂νS) := by
      intro u
      by_cases hu : u ∈ T
      · have hmem : (eP).symm (u, v) ∈ restrS p ⁻¹' T := by
          rw [Set.mem_preimage, restrS_symm]; exact hu
        rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hu]
        refine (H _).trans ?_
        rw [restrS_symm]
        simp only [modifyS_symm]
        calc _ = φ u * (C * ∫⁻ u', W ((eP).symm (u', v)) ∂νS) := by ring
          _ ≤ _ := le_rfl
      · have hmem : (eP).symm (u, v) ∉ restrS p ⁻¹' T := by
          rw [Set.mem_preimage, restrS_symm]; exact hu
        rw [Set.indicator_of_notMem hmem]
        exact bot_le
    calc _ ≤ ∫⁻ u, (T.indicator φ u) * (C * ∫⁻ u', W ((eP).symm (u', v)) ∂νS) ∂νS :=
          lintegral_mono this
      _ = (∫⁻ u, T.indicator φ u ∂νS) * (C * ∫⁻ u', W ((eP).symm (u', v)) ∂νS) :=
          lintegral_mul_const _ (hφ.indicator hT)
      _ = _ := by ring
  calc c * ∫⁻ Y, (restrS p ⁻¹' T).indicator W Y ∂(Measure.pi fun _ : ι => μ)
      = c * ∫⁻ v, ∫⁻ u, (restrS p ⁻¹' T).indicator W ((eP).symm (u, v)) ∂νS ∂νC := by rw [h1]
    _ ≤ c * ∫⁻ v, C * (∫⁻ u, T.indicator φ u ∂νS) * ∫⁻ u, W ((eP).symm (u, v)) ∂νS ∂νC := by
        gcongr with v
        exact key v
    _ = c * (C * (∫⁻ u, T.indicator φ u ∂νS) * ∫⁻ v, ∫⁻ u, W ((eP).symm (u, v)) ∂νS ∂νC) := by
        rw [lintegral_const_mul _ hI]
    _ = (c * ∫⁻ Y, W Y ∂(Measure.pi fun _ : ι => μ)) * (C * (∫⁻ u, T.indicator φ u ∂νS)) := by
        rw [h2]; ring
    _ = _ := by rw [hc, one_mul, h3]

end Cond
section Split


/-- exponent of the (unnormalised) pole weight -/
def poleExpo (g : Torus d → ℝ) (μ : Measure (Torus d)) {n : ℕ} (lam β t : ℝ) (x : Torus d)
    (Y : Config d n) : ℝ :=
  (-lam * pairSum g Y + β * ∑ i, convMeasure g μ (Y i)) + (-(t * lam) * ∑ i, g (x - Y i))

/-- single-site part of the exponent -/
def site (g : Torus d → ℝ) (μ : Measure (Torus d)) (β t lam : ℝ) (x y : Torus d) : ℝ :=
  β * convMeasure g μ y - (t * lam) * g (x - y)

/-- the exponent of a block of coordinates `κ` (without the interaction with the rest) -/
def blockExpo (g : Torus d → ℝ) (μ : Measure (Torus d)) {κ : Type*} [Fintype κ]
    (lam β t : ℝ) (x : Torus d) (w : κ → Torus d) : ℝ :=
  ∑ a, site g μ β t lam x (w a) -
    (lam / 2) * (∑ a, ∑ b, g (w a - w b) - (Fintype.card κ : ℝ) * g 0)

/-- cross interaction between two blocks -/
def crossSum (g : Torus d → ℝ) {κ κ' : Type*} [Fintype κ] [Fintype κ']
    (u : κ → Torus d) (v : κ' → Torus d) : ℝ := ∑ a, ∑ b, g (u a - v b)

theorem pairSum_eq {g : Torus d → ℝ} (hg : ∀ z, g (-z) = g z) {n : ℕ} (Y : Config d n) :
    pairSum g Y = (1 / 2) * (∑ a, ∑ b, g (Y a - Y b) - (n : ℝ) * g 0) := by
  have h := sum_erase_eq_two_mul_sum_lt (fun i j => g (Y i - Y j)) (fun i j => by
    rw [← hg, neg_sub])
  have h2 : ∀ i : Fin n, ∑ j ∈ Finset.univ.erase i, g (Y i - Y j) =
      ∑ j, g (Y i - Y j) - g 0 := by
    intro i
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
    simp
  simp_rw [h2] at h
  rw [Finset.sum_sub_distrib] at h
  unfold pairSum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h ⊢
  linarith

theorem poleExpo_eq_blockExpo {g : Torus d → ℝ} (hg : ∀ z, g (-z) = g z) (μ : Measure (Torus d))
    {n : ℕ} (lam β t : ℝ) (x : Torus d) (Y : Config d n) :
    poleExpo g μ lam β t x Y = blockExpo g μ lam β t x Y := by
  unfold poleExpo blockExpo site
  rw [pairSum_eq hg, Fintype.card_fin, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

theorem blockExpo_split {g : Torus d → ℝ} (hg : ∀ z, g (-z) = g z) (μ : Measure (Torus d))
    {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p]
    (lam β t : ℝ) (x : Torus d) (Y : ι → Torus d) :
    blockExpo g μ lam β t x Y =
      blockExpo g μ lam β t x (fun a : {a // p a} => Y a.1) +
      blockExpo g μ lam β t x (fun a : {a // ¬ p a} => Y a.1) -
      lam * crossSum g (fun a : {a // p a} => Y a.1) (fun a : {a // ¬ p a} => Y a.1) := by
  have hcard : (Fintype.card ι : ℝ) = Fintype.card {a // p a} + Fintype.card {a // ¬ p a} := by
    rw [← Nat.cast_add, Fintype.card_subtype_compl, Nat.add_sub_cancel' (Fintype.card_subtype_le p)]
  have h1 := Fintype.sum_subtype_add_sum_subtype p (fun a => site g μ β t lam x (Y a))
  -- double sum
  have h2 : ∑ a, ∑ b, g (Y a - Y b) =
      ∑ a : {a // p a}, ∑ b : {a // p a}, g (Y a - Y b) +
      ∑ a : {a // ¬ p a}, ∑ b : {a // ¬ p a}, g (Y a - Y b) +
      2 * ∑ a : {a // p a}, ∑ b : {a // ¬ p a}, g (Y a - Y b) := by
    have e1 : ∀ a : ι, ∑ b, g (Y a - Y b) =
        ∑ b : {b // p b}, g (Y a - Y b) + ∑ b : {b // ¬ p b}, g (Y a - Y b) := fun a =>
      (Fintype.sum_subtype_add_sum_subtype p (fun b => g (Y a - Y b))).symm
    simp_rw [e1]
    rw [Finset.sum_add_distrib]
    rw [← Fintype.sum_subtype_add_sum_subtype p (fun a => ∑ b : {b // p b}, g (Y a - Y b)),
      ← Fintype.sum_subtype_add_sum_subtype p (fun a => ∑ b : {b // ¬ p b}, g (Y a - Y b))]
    have e3 : ∑ a : {a // ¬ p a}, ∑ b : {b // p b}, g (Y a - Y b) =
        ∑ a : {a // p a}, ∑ b : {b // ¬ p b}, g (Y a - Y b) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [← hg, neg_sub]
    rw [e3]; ring
  unfold blockExpo crossSum
  rw [← h1, h2, hcard]
  ring

end Split

theorem jensen_lintegral {β' : Type*} [MeasurableSpace β'] (ν : Measure β') [IsProbabilityMeasure ν]
    (Φ : β' → ℝ) (hΦ : Integrable Φ ν) :
    ENNReal.ofReal (Real.exp (∫ x, Φ x ∂ν)) ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (Φ x)) ∂ν := by
  by_cases hi : Integrable (fun x => Real.exp (Φ x)) ν
  · have h1 : Real.exp (∫ x, Φ x ∂ν) ≤ ∫ x, Real.exp (Φ x) ∂ν :=
      convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
        (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hΦ hi
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal h1
  · have hm : AEStronglyMeasurable (fun x => Real.exp (Φ x)) ν :=
      (Real.continuous_exp.comp_aestronglyMeasurable hΦ.aestronglyMeasurable)
    have : ¬ HasFiniteIntegral (fun x => Real.exp (Φ x)) ν := fun h => hi ⟨hm, h⟩
    unfold HasFiniteIntegral at this
    have h2 : ∫⁻ x, ENNReal.ofReal (Real.exp (Φ x)) ∂ν = ⊤ := by
      by_contra hne
      refine this ?_
      refine lt_of_eq_of_lt ?_ (lt_top_iff_ne_top.2 hne)
      refine lintegral_congr fun x => ?_
      exact Real.enorm_of_nonneg (Real.exp_pos _).le
    rw [h2]; exact le_top

section Kernel


structure KerData (g : Torus d → ℝ) (μ : Measure (Torus d)) (B Cc : ℝ) : Prop where
  meas : Measurable g
  even : ∀ z, g (-z) = g z
  lower : ∀ z, -B ≤ g z
  int : ∀ x, Integrable (fun y => g (x - y)) μ
  int2 : Integrable (fun q : Torus d × Torus d => g (q.1 - q.2)) (μ.prod μ)
  conv : ∀ x, |convMeasure g μ x| ≤ Cc

variable {g : Torus d → ℝ} {μ : Measure (Torus d)} {B Cc : ℝ} [IsProbabilityMeasure μ]
  (hK : KerData g μ B Cc)
include hK

theorem KerData.Cc_nonneg : 0 ≤ Cc := (abs_nonneg _).trans (hK.conv 0)

theorem KerData.measurable_conv : Measurable (convMeasure g μ) :=
  measurable_convMeasure hK.meas μ

theorem KerData.integrable_conv : Integrable (convMeasure g μ) μ :=
  Integrable.of_bound hK.measurable_conv.aestronglyMeasurable Cc
    (Filter.Eventually.of_forall fun x => by simpa using hK.conv x)

theorem KerData.integral_conv_ge : -Cc ≤ ∫ y, convMeasure g μ y ∂μ := by
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := convMeasure g μ) (C := Cc)
    (Filter.Eventually.of_forall fun x => by simpa using hK.conv x)
  simp at h
  have := neg_abs_le (∫ y, convMeasure g μ y ∂μ)
  linarith

theorem KerData.integral_conv_le : ∫ y, convMeasure g μ y ∂μ ≤ Cc := by
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := convMeasure g μ) (C := Cc)
    (Filter.Eventually.of_forall fun x => by simpa using hK.conv x)
  simp at h
  have := le_abs_self (∫ y, convMeasure g μ y ∂μ)
  linarith

theorem KerData.integrable_shift (v : Torus d) : Integrable (fun y => g (y - v)) μ := by
  have := hK.int v
  refine this.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [← hK.even, neg_sub]

theorem KerData.integral_shift (v : Torus d) : ∫ y, g (y - v) ∂μ = convMeasure g μ v := by
  unfold convMeasure
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [← hK.even, neg_sub]

theorem KerData.integral_pair_le : ∫ q : Torus d × Torus d, g (q.1 - q.2) ∂(μ.prod μ) ≤ Cc := by
  rw [integral_prod _ hK.int2]
  have : ∀ x, ∫ y, g (x - y) ∂μ = convMeasure g μ x := fun x => rfl
  simp only [this]
  exact hK.integral_conv_le

theorem KerData.integrable_site (β t lam : ℝ) (x : Torus d) :
    Integrable (site g μ β t lam x) μ := by
  unfold site
  exact (hK.integrable_conv.const_mul β).sub ((hK.int x).const_mul _)

theorem KerData.integral_site_ge {β t lam : ℝ} (hβ : 0 ≤ β) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hl : 0 ≤ lam) (x : Torus d) :
    -((β + lam) * Cc) ≤ ∫ y, site g μ β t lam x y ∂μ := by
  unfold site
  rw [integral_sub (hK.integrable_conv.const_mul β) ((hK.int x).const_mul _),
    integral_const_mul, integral_const_mul]
  have h1 := hK.integral_conv_ge
  have h2 := hK.conv x
  have h3 : convMeasure g μ x ≤ Cc := (le_abs_self _).trans h2
  have h4 : 0 ≤ t * lam := mul_nonneg ht0 hl
  have h5 : t * lam ≤ lam := by nlinarith
  have hC := hK.Cc_nonneg
  have h6 : β * (-Cc) ≤ β * ∫ y, convMeasure g μ y ∂μ := mul_le_mul_of_nonneg_left h1 hβ
  have h7 : t * lam * convMeasure g μ x ≤ lam * Cc := by
    calc _ ≤ t * lam * Cc := mul_le_mul_of_nonneg_left h3 h4
      _ ≤ lam * Cc := mul_le_mul_of_nonneg_right h5 hC
  show -((β + lam) * Cc) ≤ β * ∫ y, convMeasure g μ y ∂μ - t * lam * ∫ y, g (x - y) ∂μ
  have : ∫ y, g (x - y) ∂μ = convMeasure g μ x := rfl
  rw [this]
  nlinarith

end Kernel

section Block

variable {g : Torus d → ℝ} {μ : Measure (Torus d)} {B Cc : ℝ} [IsProbabilityMeasure μ]
  (hK : KerData g μ B Cc)
include hK

theorem KerData.blockExpo_le {κ : Type*} [Fintype κ] {β t lam : ℝ} (hβ : 0 ≤ β) (hl : 0 ≤ lam)
    (x : Torus d) (w : κ → Torus d) :
    blockExpo g μ lam β t x w ≤ -(t * lam) * ∑ a, g (x - w a) +
      ((Fintype.card κ : ℝ) * β * Cc +
        (lam / 2) * (B * (Fintype.card κ : ℝ) ^ 2 + (Fintype.card κ : ℝ) * |g 0|)) := by
  unfold blockExpo site
  set k : ℝ := (Fintype.card κ : ℝ) with hk
  have h1 : ∑ a, (β * convMeasure g μ (w a) - t * lam * g (x - w a)) =
      β * ∑ a, convMeasure g μ (w a) - t * lam * ∑ a, g (x - w a) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h2 : ∑ a, convMeasure g μ (w a) ≤ k * Cc := by
    calc _ ≤ ∑ _a : κ, Cc := Finset.sum_le_sum fun a _ => (le_abs_self _).trans (hK.conv _)
      _ = k * Cc := by simp [hk]
  have h3 : -(B * k ^ 2) ≤ ∑ a, ∑ b, g (w a - w b) := by
    calc -(B * k ^ 2) = ∑ _a : κ, ∑ _b : κ, (-B) := by simp [hk]; ring
      _ ≤ _ := Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hK.lower _
  have h4 : k * g 0 ≤ k * |g 0| := mul_le_mul_of_nonneg_left (le_abs_self _) (by simp [hk])
  have h5 : β * ∑ a, convMeasure g μ (w a) ≤ β * (k * Cc) := mul_le_mul_of_nonneg_left h2 hβ
  rw [h1]
  have h6 : (lam / 2) * (-(B * k ^ 2) - k * |g 0|) ≤
      (lam / 2) * (∑ a, ∑ b, g (w a - w b) - k * g 0) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  nlinarith

theorem KerData.crossSum_ge {κ κ' : Type*} [Fintype κ] [Fintype κ'] (u : κ → Torus d)
    (v : κ' → Torus d) :
    -(B * (Fintype.card κ : ℝ) * (Fintype.card κ' : ℝ)) ≤ crossSum g u v := by
  unfold crossSum
  calc -(B * (Fintype.card κ : ℝ) * (Fintype.card κ' : ℝ)) = ∑ _a : κ, ∑ _b : κ', (-B) := by
        simp; ring
    _ ≤ _ := Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hK.lower _

end Block

section Jen0

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ]

theorem integrable_eval_pi {κ : Type*} [Fintype κ] {f : Torus d → ℝ} (hf : Integrable f μ) (a : κ) :
    Integrable (fun u : κ → Torus d => f (u a)) (Measure.pi fun _ : κ => μ) :=
  (measurePreserving_eval (fun _ : κ => μ) a).integrable_comp_of_integrable hf

theorem integral_eval_pi {κ : Type*} [Fintype κ] {f : Torus d → ℝ} (hf : AEStronglyMeasurable f μ)
    (a : κ) :
    ∫ u : κ → Torus d, f (u a) ∂(Measure.pi fun _ : κ => μ) = ∫ y, f y ∂μ := by
  have h := (measurePreserving_eval (fun _ : κ => μ) a)
  have := integral_map (μ := Measure.pi fun _ : κ => μ) (φ := fun u : κ → Torus d => u a)
    (measurable_pi_apply a).aemeasurable (f := f) (by rw [h.map_eq]; exact hf)
  rw [← this, h.map_eq]

end Jen0

section Jen

variable {g : Torus d → ℝ} {μ : Measure (Torus d)} {B Cc : ℝ} [IsProbabilityMeasure μ]
  (hK : KerData g μ B Cc)
include hK

theorem KerData.integrable_pair {κ : Type*} [Fintype κ] (a b : κ) :
    Integrable (fun u : κ → Torus d => g (u a - u b)) (Measure.pi fun _ : κ => μ) := by
  by_cases hab : a = b
  · subst hab
    simp only [sub_self]
    exact integrable_const _
  · exact integrable_pair_comp μ hab (H := fun q => g (q.1 - q.2)) hK.int2

theorem KerData.integral_pair_le' {κ : Type*} [Fintype κ] (a b : κ) :
    ∫ u : κ → Torus d, g (u a - u b) ∂(Measure.pi fun _ : κ => μ) ≤ |g 0| + Cc := by
  by_cases hab : a = b
  · subst hab
    simp only [sub_self, integral_const, probReal_univ, smul_eq_mul, one_mul]
    linarith [le_abs_self (g 0), hK.Cc_nonneg]
  · rw [integral_pair_comp μ hab (H := fun q => g (q.1 - q.2)) hK.int2]
    linarith [hK.integral_pair_le, abs_nonneg (g 0)]

theorem KerData.jensen_block {κ κ' : Type*} [Fintype κ] [Fintype κ'] {β t lam : ℝ} (hβ : 0 ≤ β)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hl : 0 ≤ lam) (x : Torus d) (v : κ' → Torus d) :
    Integrable (fun u : κ → Torus d =>
        blockExpo g μ lam β t x u - lam * crossSum g u v) (Measure.pi fun _ : κ => μ) ∧
    -(((Fintype.card κ : ℝ) * (β + lam) * Cc +
        (lam / 2) * ((Fintype.card κ : ℝ) ^ 2 * (|g 0| + Cc) + (Fintype.card κ : ℝ) * |g 0|) +
        lam * (Fintype.card κ : ℝ) * (Fintype.card κ' : ℝ) * Cc)) ≤
      ∫ u : κ → Torus d, (blockExpo g μ lam β t x u - lam * crossSum g u v)
        ∂(Measure.pi fun _ : κ => μ) := by
  set ν := Measure.pi fun _ : κ => μ with hν
  set k : ℝ := (Fintype.card κ : ℝ) with hk
  set k' : ℝ := (Fintype.card κ' : ℝ) with hk'
  have iS : Integrable (fun u : κ → Torus d => ∑ a, site g μ β t lam x (u a)) ν :=
    integrable_finsetSum _ fun a _ => integrable_eval_pi (hK.integrable_site β t lam x) a
  have iD : Integrable (fun u : κ → Torus d => ∑ a, ∑ b, g (u a - u b)) ν :=
    integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hK.integrable_pair a b
  have iX : Integrable (fun u : κ → Torus d => crossSum g u v) ν := by
    unfold crossSum
    exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
      integrable_eval_pi (hK.integrable_shift (v b)) a
  have iAll : Integrable (fun u : κ → Torus d =>
      blockExpo g μ lam β t x u - lam * crossSum g u v) ν := by
    unfold blockExpo
    exact (iS.sub (((iD.sub (integrable_const _)).const_mul _))).sub (iX.const_mul _)
  refine ⟨iAll, ?_⟩
  have eS : ∫ u : κ → Torus d, ∑ a, site g μ β t lam x (u a) ∂ν ≥ -(k * ((β + lam) * Cc)) := by
    rw [integral_finsetSum _ fun a _ => integrable_eval_pi (hK.integrable_site β t lam x) a]
    have : ∀ a : κ, ∫ u : κ → Torus d, site g μ β t lam x (u a) ∂ν ≥ -((β + lam) * Cc) := by
      intro a
      rw [integral_eval_pi (hK.integrable_site β t lam x).aestronglyMeasurable a]
      exact hK.integral_site_ge hβ ht0 ht1 hl x
    calc _ ≥ ∑ _a : κ, (-((β + lam) * Cc)) := Finset.sum_le_sum fun a _ => this a
      _ = _ := by simp [hk]
  have eD : ∫ u : κ → Torus d, ∑ a, ∑ b, g (u a - u b) ∂ν ≤ k ^ 2 * (|g 0| + Cc) := by
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hK.integrable_pair a b]
    have : ∀ a : κ, ∫ u : κ → Torus d, ∑ b, g (u a - u b) ∂ν ≤ k * (|g 0| + Cc) := by
      intro a
      rw [integral_finsetSum _ fun b _ => hK.integrable_pair a b]
      calc _ ≤ ∑ _b : κ, (|g 0| + Cc) := Finset.sum_le_sum fun b _ => hK.integral_pair_le' a b
        _ = _ := by simp [hk]; ring
    calc _ ≤ ∑ _a : κ, k * (|g 0| + Cc) := Finset.sum_le_sum fun a _ => this a
      _ = _ := by simp [hk]; ring
  have eX : ∫ u : κ → Torus d, crossSum g u v ∂ν ≤ k * k' * Cc := by
    unfold crossSum
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
      integrable_eval_pi (hK.integrable_shift (v b)) a]
    have : ∀ a : κ, ∫ u : κ → Torus d, ∑ b, g (u a - v b) ∂ν ≤ k' * Cc := by
      intro a
      rw [integral_finsetSum _ fun b _ => integrable_eval_pi (hK.integrable_shift (v b)) a]
      calc _ ≤ ∑ _b : κ', Cc := by
            refine Finset.sum_le_sum fun b _ => ?_
            rw [integral_eval_pi (hK.integrable_shift (v b)).aestronglyMeasurable a,
              hK.integral_shift]
            exact (le_abs_self _).trans (hK.conv _)
        _ = _ := by simp [hk']
    calc _ ≤ ∑ _a : κ, k' * Cc := Finset.sum_le_sum fun a _ => this a
      _ = _ := by simp [hk]; ring
  have iA : Integrable (fun u : κ → Torus d =>
      (lam / 2) * (∑ a, ∑ b, g (u a - u b) - k * g 0)) ν :=
    (iD.sub (integrable_const _)).const_mul _
  have hA : ∫ u : κ → Torus d, (lam / 2) * (∑ a, ∑ b, g (u a - u b) - k * g 0) ∂ν =
      (lam / 2) * ((∫ u : κ → Torus d, ∑ a, ∑ b, g (u a - u b) ∂ν) - k * g 0) := by
    rw [integral_const_mul, integral_sub iD (integrable_const _)]
    simp
  have hint : ∫ u : κ → Torus d, (blockExpo g μ lam β t x u - lam * crossSum g u v) ∂ν =
      (∫ u : κ → Torus d, ∑ a, site g μ β t lam x (u a) ∂ν) -
        (lam / 2) * ((∫ u : κ → Torus d, ∑ a, ∑ b, g (u a - u b) ∂ν) - k * g 0) -
        lam * ∫ u : κ → Torus d, crossSum g u v ∂ν := by
    have e : ∫ u : κ → Torus d, (blockExpo g μ lam β t x u - lam * crossSum g u v) ∂ν =
        ∫ u : κ → Torus d, ((∑ a, site g μ β t lam x (u a) -
          (lam / 2) * (∑ a, ∑ b, g (u a - u b) - k * g 0)) - lam * crossSum g u v) ∂ν := rfl
    have iSA : Integrable (fun u : κ → Torus d => ∑ a, site g μ β t lam x (u a) -
        (lam / 2) * (∑ a, ∑ b, g (u a - u b) - k * g 0)) ν := iS.sub iA
    have iXl : Integrable (fun u : κ → Torus d => lam * crossSum g u v) ν := iX.const_mul lam
    rw [e, integral_sub iSA iXl, integral_sub iS iA, hA, integral_const_mul]
  rw [hint]
  have h1 : k * g 0 ≥ -(k * |g 0|) := by
    have := neg_abs_le (g 0)
    have hk0 : 0 ≤ k := by simp [hk]
    nlinarith
  have h2 : (lam / 2) * ((∫ u : κ → Torus d, ∑ a, ∑ b, g (u a - u b) ∂ν) - k * g 0) ≤
      (lam / 2) * (k ^ 2 * (|g 0| + Cc) + k * |g 0|) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h3 : lam * ∫ u : κ → Torus d, crossSum g u v ∂ν ≤ lam * (k * k' * Cc) :=
    mul_le_mul_of_nonneg_left eX hl
  nlinarith

end Jen

section HPole

variable {g : Torus d → ℝ} {μ : Measure (Torus d)} {B Cc : ℝ} [IsProbabilityMeasure μ]
  (hK : KerData g μ B Cc)

theorem compl_symm {n : ℕ} (p : Fin n → Prop) [DecidablePred p]
    (u : {a // p a} → Torus d) (v : {a // ¬ p a} → Torus d) :
    (fun a : {a // ¬ p a} => (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => Torus d) p).symm
      (u, v) a.1) = v := by
  funext a
  simp [a.2]

/-- the constants in the conditional bound -/
def Kup (g : Torus d → ℝ) (B Cc β lam : ℝ) (k k' : ℝ) : ℝ :=
  k * β * Cc + (lam / 2) * (B * k ^ 2 + k * |g 0|) + lam * B * k * k'

def Klow (g : Torus d → ℝ) (Cc β lam : ℝ) (k k' : ℝ) : ℝ :=
  k * (β + lam) * Cc + (lam / 2) * (k ^ 2 * (|g 0| + Cc) + k * |g 0|) + lam * k * k' * Cc

include hK in
theorem H_pole {n : ℕ} (p : Fin n → Prop) [DecidablePred p] {β t lam : ℝ} (hβ : 0 ≤ β)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hl : 0 ≤ lam) (x : Torus d) (Y : Config d n) :
    ENNReal.ofReal (Real.exp (poleExpo g μ lam β t x Y)) ≤
      ENNReal.ofReal (Real.exp (Kup g B Cc β lam (Fintype.card {a // p a} : ℝ)
          (Fintype.card {a // ¬ p a} : ℝ) +
        Klow g Cc β lam (Fintype.card {a // p a} : ℝ) (Fintype.card {a // ¬ p a} : ℝ))) *
      ENNReal.ofReal (Real.exp (-(t * lam) * ∑ a : {a // p a}, g (x - restrS p Y a))) *
      ∫⁻ u, ENNReal.ofReal (Real.exp (poleExpo g μ lam β t x (modifyS p Y u)))
        ∂(Measure.pi fun _ : {a // p a} => μ) := by
  set kS : ℝ := (Fintype.card {a // p a} : ℝ) with hkS
  set kC : ℝ := (Fintype.card {a // ¬ p a} : ℝ) with hkC
  set v : {a // ¬ p a} → Torus d := fun a => Y a.1 with hv
  set G : ℝ := blockExpo g μ lam β t x v with hG
  have hsplit : ∀ Y' : Config d n, poleExpo g μ lam β t x Y' =
      blockExpo g μ lam β t x (restrS p Y') + blockExpo g μ lam β t x (fun a : {a // ¬ p a} => Y' a.1)
        - lam * crossSum g (restrS p Y') (fun a : {a // ¬ p a} => Y' a.1) := fun Y' => by
    rw [poleExpo_eq_blockExpo hK.even]
    exact blockExpo_split hK.even μ p lam β t x Y'
  have hmod : ∀ u, poleExpo g μ lam β t x (modifyS p Y u) =
      G + (blockExpo g μ lam β t x u - lam * crossSum g u v) := by
    intro u
    rw [hsplit]
    have h1 : restrS p (modifyS p Y u) = u := restrS_symm p u _
    have h2 : (fun a : {a // ¬ p a} => modifyS p Y u a.1) = v := compl_symm p u _
    rw [h1, h2]; ring
  have hlow := (hK.jensen_block (κ := {a // p a}) (κ' := {a // ¬ p a}) hβ ht0 ht1 hl x v)
  have hJ := jensen_lintegral (Measure.pi fun _ : {a // p a} => μ) _ hlow.1
  have hJ' : ENNReal.ofReal (Real.exp (-(Klow g Cc β lam kS kC))) ≤
      ∫⁻ u, ENNReal.ofReal (Real.exp (blockExpo g μ lam β t x u - lam * crossSum g u v))
        ∂(Measure.pi fun _ : {a // p a} => μ) := by
    refine le_trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)) hJ
    exact hlow.2
  have hint : ∫⁻ u, ENNReal.ofReal (Real.exp (poleExpo g μ lam β t x (modifyS p Y u)))
        ∂(Measure.pi fun _ : {a // p a} => μ) =
      ENNReal.ofReal (Real.exp G) * ∫⁻ u, ENNReal.ofReal (Real.exp
        (blockExpo g μ lam β t x u - lam * crossSum g u v)) ∂(Measure.pi fun _ : {a // p a} => μ) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun u => ?_
    rw [hmod, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  -- upper bound for the weight
  have hup : poleExpo g μ lam β t x Y ≤
      -(t * lam) * ∑ a : {a // p a}, g (x - restrS p Y a) + Kup g B Cc β lam kS kC + G := by
    rw [hsplit]
    have h1 := hK.blockExpo_le (t := t) hβ hl x (restrS p Y)
    have h2 := hK.crossSum_ge (restrS p Y) (fun a : {a // ¬ p a} => Y a.1)
    have h3 : -(lam * crossSum g (restrS p Y) (fun a : {a // ¬ p a} => Y a.1)) ≤
        lam * B * kS * kC := by nlinarith
    unfold Kup
    simp only [hG, hv]
    linarith
  calc ENNReal.ofReal (Real.exp (poleExpo g μ lam β t x Y))
      ≤ ENNReal.ofReal (Real.exp (-(t * lam) * ∑ a : {a // p a}, g (x - restrS p Y a) +
          Kup g B Cc β lam kS kC + G)) :=
        ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hup)
    _ = ENNReal.ofReal (Real.exp (Kup g B Cc β lam kS kC)) *
          ENNReal.ofReal (Real.exp (-(t * lam) * ∑ a : {a // p a}, g (x - restrS p Y a))) *
          ENNReal.ofReal (Real.exp G) := by
        rw [Real.exp_add, Real.exp_add, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity)]
        ring
    _ ≤ ENNReal.ofReal (Real.exp (Kup g B Cc β lam kS kC)) *
          ENNReal.ofReal (Real.exp (-(t * lam) * ∑ a : {a // p a}, g (x - restrS p Y a))) *
          (ENNReal.ofReal (Real.exp (Klow g Cc β lam kS kC)) *
            (ENNReal.ofReal (Real.exp G) * ∫⁻ u, ENNReal.ofReal (Real.exp
              (blockExpo g μ lam β t x u - lam * crossSum g u v)) ∂(Measure.pi fun _ : {a // p a} => μ))) := by
        gcongr
        calc ENNReal.ofReal (Real.exp G) = ENNReal.ofReal (Real.exp (Klow g Cc β lam kS kC)) *
              (ENNReal.ofReal (Real.exp G) * ENNReal.ofReal (Real.exp (-(Klow g Cc β lam kS kC)))) := by
              rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
                ← Real.exp_add, ← Real.exp_add]
              congr 2; ring
          _ ≤ _ := by gcongr
    _ = _ := by
        rw [hint, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
        ring

end HPole

section PerRiesz


theorem kerData_periodicRiesz (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) :
    ∃ B Cc : ℝ, 0 ≤ B ∧ KerData (periodicRiesz d s) (withDensityReal ρ) B Cc := by
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨B, hB⟩ := periodicRiesz_ge (d := d) hd hs0 hsd
  have hB' : ∀ z, -(max B 0) ≤ periodicRiesz d s z := fun z =>
    (neg_le_neg (le_max_left _ _)).trans (hB z)
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_density_bound hρ
  obtain ⟨Cc, hC⟩ := convMeasure_bounded hd hs0 hsd ρ hρ.density Λ hΛ
  have hgm := measurable_periodicRiesz hd hs0 hsd
  have hgi := KernelAux.integrable_periodicRiesz hd hs0 hsd
  set g := periodicRiesz d s with hg
  have hint : ∀ x, Integrable (fun y => g (x - y)) (withDensityReal ρ) := by
    intro x
    refine ⟨(hgm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    refine lt_of_le_of_lt (KernelAux2.lintegral_conv_le ρ Λ hΛ (fun z => ‖g z‖ₑ) x) ?_
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    exact hgi.hasFiniteIntegral
  have hCc : ∀ x, |convMeasure g (withDensityReal ρ) x| ≤ |Cc| := fun x => (hC x).trans (le_abs_self _)
  have hkd : KerData g (withDensityReal ρ) (max B 0) |Cc| :=
    { meas := hgm
      even := fun z => periodicRiesz_neg z
      lower := hB'
      int := hint
      int2 := ?_
      conv := hCc }
  · exact ⟨max B 0, |Cc|, le_max_right _ _, hkd⟩
  · -- integrability on the product
    have hm : AEStronglyMeasurable (fun q : Torus d × Torus d => g (q.1 - q.2))
        ((withDensityReal ρ).prod (withDensityReal ρ)) :=
      (hgm.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable
    rw [integrable_prod_iff hm]
    refine ⟨Filter.Eventually.of_forall hint, ?_⟩
    have hmeas : Measurable fun x => ∫ y, ‖g (x - y)‖ ∂(withDensityReal ρ) := by
      have : StronglyMeasurable (Function.uncurry fun x y : Torus d => ‖g (x - y)‖) :=
        (hgm.comp (measurable_fst.sub measurable_snd)).norm.stronglyMeasurable
      exact (this.integral_prod_right' (ν := withDensityReal ρ)).measurable
    refine Integrable.of_bound hmeas.aestronglyMeasurable (|Cc| + 2 * max B 0)
      (Filter.Eventually.of_forall fun x => ?_)
    have h1 : ∫ y, ‖g (x - y)‖ ∂(withDensityReal ρ) ≤
        ∫ y, (g (x - y) + 2 * max B 0) ∂(withDensityReal ρ) := by
      refine integral_mono (hint x).norm ((hint x).add (integrable_const _)) fun y => ?_
      have := hB' (x - y)
      have h0 := le_max_right B 0
      simp only [Real.norm_eq_abs]
      rcases le_total 0 (g (x - y)) with h | h
      · rw [abs_of_nonneg h]; linarith
      · rw [abs_of_nonpos h]; linarith
    rw [integral_add (hint x) (integrable_const _)] at h1
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h1
    have h2 : ∫ y, g (x - y) ∂(withDensityReal ρ) = convMeasure g (withDensityReal ρ) x := rfl
    have h3 := hCc x
    have h4 : 0 ≤ ∫ y, ‖g (x - y)‖ ∂(withDensityReal ρ) := integral_nonneg fun _ => norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg h4]
    have := le_abs_self (convMeasure g (withDensityReal ρ) x)
    linarith

end PerRiesz

section PoleRep


theorem poleLaw_eq {g : Torus d → ℝ} (hg : Measurable g) (μ : Measure (Torus d)) [SFinite μ]
    (n : ℕ) (lam β x_t : ℝ) (x : Torus d) :
    ∃ c : ℝ≥0∞, poleLaw g μ n lam β x x_t =
      c • (Measure.pi fun _ : Fin n => μ).withDensity
        (fun Y => ENNReal.ofReal (Real.exp (poleExpo g μ lam β x_t x Y))) := by
  have hm1 : Measurable fun Y : Config d n => -lam * pairSum g Y + β * ∑ i, convMeasure g μ (Y i) :=
    ((measurable_pairSum hg).const_mul _).add
      ((Finset.measurable_sum _ fun i _ =>
        (measurable_convMeasure hg μ).comp (measurable_pi_apply i)).const_mul _)
  have hm2 : Measurable fun Y : Config d n => -(x_t * lam) * ∑ i, g (x - Y i) :=
    (Finset.measurable_sum _ fun i _ =>
      hg.comp (measurable_const.sub (measurable_pi_apply i))).const_mul _
  set f1 : Config d n → ℝ≥0∞ := fun Y => ENNReal.ofReal (Real.exp (-lam * pairSum g Y +
    β * ∑ i, convMeasure g μ (Y i))) with hf1
  set f2 : Config d n → ℝ≥0∞ := fun Y => ENNReal.ofReal (Real.exp (-(x_t * lam) * ∑ i, g (x - Y i)))
    with hf2
  have hmf1 : Measurable f1 := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hm1)
  have hmf2 : Measurable f2 := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hm2)
  have hprod : (fun Y : Config d n => ENNReal.ofReal (Real.exp (poleExpo g μ lam β x_t x Y))) =
      f1 * f2 := by
    funext Y
    simp only [Pi.mul_apply, hf1, hf2, poleExpo]
    rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  unfold poleLaw cavityLaw tiltMeasure
  set Z1 := ∫⁻ a, ENNReal.ofReal (Real.exp (-lam * pairSum g a + β * ∑ i, convMeasure g μ (a i)))
    ∂(Measure.pi fun _ : Fin n => μ) with hZ1
  refine ⟨(∫⁻ a, ENNReal.ofReal (Real.exp (-(x_t * lam) * ∑ i, g (x - a i)))
      ∂((Z1⁻¹ • (Measure.pi fun _ : Fin n => μ).withDensity
        fun a => ENNReal.ofReal (Real.exp (-lam * pairSum g a +
          β * ∑ i, convMeasure g μ (a i))))))⁻¹ * Z1⁻¹, ?_⟩
  rw [hprod, withDensity_mul _ hmf1 hmf2, withDensity_smul_measure, smul_smul]

end PoleRep

section Restr

variable {g : Torus d → ℝ} {μ : Measure (Torus d)} {B Cc : ℝ} [IsProbabilityMeasure μ]
  (hK : KerData g μ B Cc)

include hK in
theorem pole_restr_le {n : ℕ} (p : Fin n → Prop) [DecidablePred p] {β t lam : ℝ} (hβ : 0 ≤ β)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hl : 0 ≤ lam) (x : Torus d)
    [hP : IsProbabilityMeasure (poleLaw g μ n lam β x t)]
    (T : Set ({a // p a} → Torus d)) (hT : MeasurableSet T) :
    poleLaw g μ n lam β x t (restrS p ⁻¹' T) ≤
      ENNReal.ofReal (Real.exp (Kup g B Cc β lam (Fintype.card {a // p a} : ℝ)
          (Fintype.card {a // ¬ p a} : ℝ) +
        Klow g Cc β lam (Fintype.card {a // p a} : ℝ) (Fintype.card {a // ¬ p a} : ℝ))) *
      ∫⁻ Y, T.indicator (fun u => ENNReal.ofReal (Real.exp
          (-(t * lam) * ∑ a : {a // p a}, g (x - u a)))) (restrS p Y)
        ∂(Measure.pi fun _ : Fin n => μ) := by
  obtain ⟨c, hc⟩ := poleLaw_eq hK.meas μ n lam β t x
  have hm1 : Measurable fun Y : Config d n =>
      poleExpo g μ lam β t x Y := by
    unfold poleExpo
    exact (((measurable_pairSum hK.meas).const_mul _).add
      ((Finset.measurable_sum _ fun i _ =>
        (measurable_convMeasure hK.meas μ).comp (measurable_pi_apply i)).const_mul _)).add
      ((Finset.measurable_sum _ fun i _ =>
        hK.meas.comp (measurable_const.sub (measurable_pi_apply i))).const_mul _)
  set W : Config d n → ℝ≥0∞ := fun Y => ENNReal.ofReal (Real.exp (poleExpo g μ lam β t x Y)) with hWdef
  have hW : Measurable W := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hm1)
  have hnorm : c * ∫⁻ Y, W Y ∂(Measure.pi fun _ : Fin n => μ) = 1 := by
    have h := hP.measure_univ
    rw [hc, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      smul_eq_mul] at h
    exact h
  have hφ : Measurable fun u : {a // p a} → Torus d => ENNReal.ofReal (Real.exp
      (-(t * lam) * ∑ a : {a // p a}, g (x - u a))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((Finset.measurable_sum _ fun a _ =>
        hK.meas.comp (measurable_const.sub (measurable_pi_apply a))).const_mul _))
  have hG := marginal_le_of_cond μ p W hW c hnorm _ hφ
    (ENNReal.ofReal (Real.exp (Kup g B Cc β lam (Fintype.card {a // p a} : ℝ)
          (Fintype.card {a // ¬ p a} : ℝ) +
        Klow g Cc β lam (Fintype.card {a // p a} : ℝ) (Fintype.card {a // ¬ p a} : ℝ))))
    (fun Y => H_pole hK p hβ ht0 ht1 hl x Y) T hT
  have hS : MeasurableSet (restrS p ⁻¹' T) := (measurable_restrS p) hT
  rw [hc, Measure.smul_apply, withDensity_apply _ hS, smul_eq_mul, ← lintegral_indicator hS]
  exact hG

end Restr

section One

variable {g : Torus d → ℝ} {μ : Measure (Torus d)} {B Cc : ℝ} [IsProbabilityMeasure μ]
  (hK : KerData g μ B Cc)

/-- uniform constant -/
def Kbound (g : Torus d → ℝ) (B Cc β : ℝ) (k : ℝ) : ℝ :=
  k * β * Cc + (β / 2) * (B * k ^ 2 + k * |g 0|) + β * B * k + k * (2 * β) * Cc +
    (β / 2) * (k ^ 2 * (|g 0| + Cc) + k * |g 0|) + k * β * Cc

theorem Kup_Klow_le (hB : 0 ≤ B) (hCc : 0 ≤ Cc) {β lam k k' : ℝ} (hβ : 0 ≤ β) (hl : 0 ≤ lam)
    (hlb : lam ≤ β) (hk : 0 ≤ k) (hlk : lam * k' ≤ β) :
    Kup g B Cc β lam k k' + Klow g Cc β lam k k' ≤ Kbound g B Cc β k := by
  unfold Kup Klow Kbound
  have h0 : 0 ≤ |g 0| := abs_nonneg _
  have e1 : (lam / 2) * (B * k ^ 2 + k * |g 0|) ≤ (β / 2) * (B * k ^ 2 + k * |g 0|) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have e2 : lam * B * k * k' ≤ β * B * k := by
    have : lam * B * k * k' = (B * k) * (lam * k') := by ring
    rw [this]
    nlinarith [mul_nonneg hB hk]
  have e3 : k * (β + lam) * Cc ≤ k * (2 * β) * Cc := by
    have : k * (β + lam) ≤ k * (2 * β) := mul_le_mul_of_nonneg_left (by linarith) hk
    exact mul_le_mul_of_nonneg_right this hCc
  have e4 : (lam / 2) * (k ^ 2 * (|g 0| + Cc) + k * |g 0|) ≤
      (β / 2) * (k ^ 2 * (|g 0| + Cc) + k * |g 0|) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have e5 : lam * k * k' * Cc ≤ k * β * Cc := by
    have : lam * k * k' * Cc = (k * Cc) * (lam * k') := by ring
    rw [this]
    nlinarith [mul_nonneg hk hCc]
  linarith

end One

section One2

variable {g : Torus d → ℝ} {μ : Measure (Torus d)} {B Cc : ℝ} [IsProbabilityMeasure μ]
  (hK : KerData g μ B Cc)

include hK in
theorem pole_one_le (hB : 0 ≤ B) {n : ℕ} (i : Fin n) {β t lam : ℝ} (hβ : 0 ≤ β)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hl : 0 ≤ lam) (hlb : lam ≤ β) (hln : lam * n ≤ β) (x : Torus d)
    [hP : IsProbabilityMeasure (poleLaw g μ n lam β x t)] :
    (poleLaw g μ n lam β x t).map (fun Y : Config d n => Y i) ≤
      μ.withDensity (fun y => ENNReal.ofReal (Real.exp (Kbound g B Cc β 1)) *
        ENNReal.ofReal (Real.exp (-(t * lam) * g (x - y)))) := by
  rw [Measure.le_iff]
  intro A hA
  rw [Measure.map_apply (measurable_pi_apply i) hA]
  set p : Fin n → Prop := fun a => a = i with hp
  set T : Set ({a // p a} → Torus d) := {u | u ⟨i, rfl⟩ ∈ A} with hT
  have hTm : MeasurableSet T := (measurable_pi_apply (⟨i, rfl⟩ : {a // p a})) hA
  have hpre : restrS p ⁻¹' T = (fun Y : Config d n => Y i) ⁻¹' A := rfl
  have h1 := pole_restr_le hK p hβ ht0 ht1 hl x T hTm
  rw [hpre] at h1
  refine h1.trans ?_
  have hcard1 : ∀ [inst : Fintype {a // p a}], Fintype.card {a // p a} = 1 := by
    intro inst
    rw [Fintype.card_eq_one_iff]
    exact ⟨⟨i, rfl⟩, fun b => Subtype.ext b.2⟩
  have hcardC : (Fintype.card {a // ¬ p a} : ℝ) ≤ n := by
    exact_mod_cast (Fintype.card_subtype_le _).trans (by simp)
  have hKK := Kup_Klow_le (g := g) hB hK.Cc_nonneg hβ hl hlb (k := 1) (k' := (Fintype.card {a // ¬ p a} : ℝ))
    zero_le_one (by
      have : lam * (Fintype.card {a // ¬ p a} : ℝ) ≤ lam * n := mul_le_mul_of_nonneg_left hcardC hl
      linarith)
  simp only [hcard1, Nat.cast_one]
  have hexp : ENNReal.ofReal (Real.exp (Kup g B Cc β lam 1 (Fintype.card {a // ¬ p a} : ℝ) +
      Klow g Cc β lam 1 (Fintype.card {a // ¬ p a} : ℝ))) ≤
      ENNReal.ofReal (Real.exp (Kbound g B Cc β 1)) :=
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hKK)
  have hsum : ∀ [inst : Fintype {a // p a}], ∀ u : {a // p a} → Torus d,
      ∑ a : {a // p a}, g (x - u a) = g (x - u ⟨i, rfl⟩) := by
    intro inst u
    rw [Fintype.sum_eq_single ⟨i, rfl⟩]
    intro b hb
    exact absurd (Subtype.ext b.2) hb
  set a : Torus d → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp (-(t * lam) * g (x - y))) with ha
  have ham : Measurable a := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    ((hK.meas.comp (measurable_const.sub measurable_id)).const_mul _))
  have hint : ∀ [inst : Fintype {a // p a}], ∫⁻ Y : Fin n → Torus d, T.indicator (fun u => ENNReal.ofReal (Real.exp
          (-(t * lam) * ∑ a : {a // p a}, g (x - u a)))) (restrS p Y)
        ∂(Measure.pi fun _ : Fin n => μ) = ∫⁻ y, A.indicator a y ∂μ := by
    intro inst
    rw [← (measurePreserving_eval (fun _ : Fin n => μ) i).lintegral_comp (ham.indicator hA)]
    refine lintegral_congr fun Y => ?_
    by_cases hY : Y i ∈ A
    · have hY' : restrS p Y ∈ T := hY
      simp only [Set.indicator, hY, hY', if_true, hsum, ha, restrS, Function.eval]
    · have hY' : restrS p Y ∉ T := hY
      simp only [Set.indicator, hY, hY', if_false, Function.eval]
  refine (mul_le_mul' hexp (hint (inst := Subtype.fintype p)).le).trans ?_
  rw [withDensity_apply _ hA, ← lintegral_indicator hA]
  calc ENNReal.ofReal (Real.exp (Kbound g B Cc β 1)) * ∫⁻ y, A.indicator a y ∂μ
      = ∫⁻ y, ENNReal.ofReal (Real.exp (Kbound g B Cc β 1)) * A.indicator a y ∂μ :=
        (lintegral_const_mul _ (ham.indicator hA)).symm
    _ ≤ _ := by
        refine le_of_eq (lintegral_congr fun y => ?_)
        by_cases hy : y ∈ A <;> simp [Set.indicator, hy, ha]

end One2

section Two

variable {g : Torus d → ℝ} {μ : Measure (Torus d)} {B Cc : ℝ} [IsProbabilityMeasure μ]
  (hK : KerData g μ B Cc)

include hK in
theorem pole_two_le (hB : 0 ≤ B) {n : ℕ} (i j : Fin n) (hij : i ≠ j) {β t lam : ℝ} (hβ : 0 ≤ β)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hl : 0 ≤ lam) (hlb : lam ≤ β) (hln : lam * n ≤ β) (x : Torus d)
    [hP : IsProbabilityMeasure (poleLaw g μ n lam β x t)] :
    twoMarginal (poleLaw g μ n lam β x t) i j ≤
      (μ.prod μ).withDensity (fun q => ENNReal.ofReal (Real.exp (Kbound g B Cc β 2)) *
        ENNReal.ofReal (Real.exp (-(t * lam) * (g (x - q.1) + g (x - q.2))))) := by
  rw [Measure.le_iff]
  intro A hA
  have hmeas : Measurable (fun Y : Config d n => (Y i, Y j)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  unfold twoMarginal
  rw [Measure.map_apply hmeas hA]
  set p : Fin n → Prop := fun a => a = i ∨ a = j with hp
  set T : Set ({a // p a} → Torus d) :=
    {u | (u ⟨i, Or.inl rfl⟩, u ⟨j, Or.inr rfl⟩) ∈ A} with hT
  have hTm : MeasurableSet T :=
    ((measurable_pi_apply (⟨i, Or.inl rfl⟩ : {a // p a})).prodMk
      (measurable_pi_apply (⟨j, Or.inr rfl⟩ : {a // p a}))) hA
  have hpre : restrS p ⁻¹' T = (fun Y : Config d n => (Y i, Y j)) ⁻¹' A := rfl
  have h1 := pole_restr_le hK p hβ ht0 ht1 hl x T hTm
  rw [hpre] at h1
  refine h1.trans ?_
  have hcard2 : ∀ [inst : Fintype {a // p a}], Fintype.card {a // p a} = 2 := by
    intro inst
    rw [Fintype.card_subtype]
    have : Finset.univ.filter p = {i, j} := by
      ext a; simp [hp]
    rw [this, Finset.card_pair hij]
  have hcardC : (Fintype.card {a // ¬ p a} : ℝ) ≤ n := by
    exact_mod_cast (Fintype.card_subtype_le _).trans (by simp)
  have hKK := Kup_Klow_le (g := g) hB hK.Cc_nonneg hβ hl hlb (k := 2)
    (k' := (Fintype.card {a // ¬ p a} : ℝ)) (by norm_num) (by
      have : lam * (Fintype.card {a // ¬ p a} : ℝ) ≤ lam * n := mul_le_mul_of_nonneg_left hcardC hl
      linarith)
  simp only [hcard2, Nat.cast_ofNat]
  have hexp : ENNReal.ofReal (Real.exp (Kup g B Cc β lam 2 (Fintype.card {a // ¬ p a} : ℝ) +
      Klow g Cc β lam 2 (Fintype.card {a // ¬ p a} : ℝ))) ≤
      ENNReal.ofReal (Real.exp (Kbound g B Cc β 2)) :=
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hKK)
  have hsum : ∀ [inst : Fintype {a // p a}], ∀ u : {a // p a} → Torus d,
      ∑ a : {a // p a}, g (x - u a) = g (x - u ⟨i, Or.inl rfl⟩) + g (x - u ⟨j, Or.inr rfl⟩) := by
    intro inst u
    have hne : (⟨i, Or.inl rfl⟩ : {a // p a}) ≠ ⟨j, Or.inr rfl⟩ := fun h => hij (congrArg Subtype.val h)
    refine Finset.sum_eq_add (s := Finset.univ) _ _ hne ?_ (fun h => absurd (Finset.mem_univ _) h)
      (fun h => absurd (Finset.mem_univ _) h)
    intro c _ hc
    exfalso
    rcases c.2 with h | h
    · exact hc.1 (Subtype.ext h)
    · exact hc.2 (Subtype.ext h)
  set a : Torus d × Torus d → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (Real.exp (-(t * lam) * (g (x - q.1) + g (x - q.2)))) with ha
  have ham : Measurable a := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (((hK.meas.comp (measurable_const.sub measurable_fst)).add
      (hK.meas.comp (measurable_const.sub measurable_snd))).const_mul _))
  have hint : ∀ [inst : Fintype {a // p a}], ∫⁻ Y : Fin n → Torus d, T.indicator (fun u => ENNReal.ofReal (Real.exp
          (-(t * lam) * ∑ a : {a // p a}, g (x - u a)))) (restrS p Y)
        ∂(Measure.pi fun _ : Fin n => μ) = ∫⁻ q, A.indicator a q ∂(μ.prod μ) := by
    intro inst
    have h2 := lintegral_map (μ := Measure.pi fun _ : Fin n => μ) (ham.indicator hA) hmeas
    rw [pi_map_pair μ hij] at h2
    rw [h2]
    refine lintegral_congr fun Y => ?_
    by_cases hY : (Y i, Y j) ∈ A
    · have hY' : restrS p Y ∈ T := hY
      simp only [Set.indicator, hY, hY', if_true, hsum, ha, restrS]
    · have hY' : restrS p Y ∉ T := hY
      simp only [Set.indicator, hY, hY', if_false]
  refine (mul_le_mul' hexp (hint (inst := Subtype.fintype p)).le).trans ?_
  rw [withDensity_apply _ hA, ← lintegral_indicator hA]
  calc ENNReal.ofReal (Real.exp (Kbound g B Cc β 2)) * ∫⁻ q, A.indicator a q ∂(μ.prod μ)
      = ∫⁻ q, ENNReal.ofReal (Real.exp (Kbound g B Cc β 2)) * A.indicator a q ∂(μ.prod μ) :=
        (lintegral_const_mul _ (ham.indicator hA)).symm
    _ ≤ _ := by
        refine le_of_eq (lintegral_congr fun q => ?_)
        by_cases hy : q ∈ A <;> simp [Set.indicator, hy, ha]

end Two

section Final


theorem pole_density_clauses (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ≪
          withDensityReal ρ ∧
        ∀ᵐ y ∂(withDensityReal ρ),
          (firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)).rnDeriv
              (withDensityReal ρ) y ≤
            ENNReal.ofReal (C * Real.exp (-(t * (β / N)) * periodicRiesz d s (x - y)))) ∧
      (∀ i j : Fin (N - 1), i ≠ j →
        twoMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) i j ≪
            (withDensityReal ρ).prod (withDensityReal ρ) ∧
          ∀ᵐ p ∂((withDensityReal ρ).prod (withDensityReal ρ)),
            (twoMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)
                i j).rnDeriv ((withDensityReal ρ).prod (withDensityReal ρ)) p ≤
              ENNReal.ofReal (C * Real.exp (-(t * (β / N)) *
                (periodicRiesz d s (x - p.1) + periodicRiesz d s (x - p.2))))) := by
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨B, Cc, hB, hK⟩ := kerData_periodicRiesz hd hs0 hsd hρ
  refine ⟨max (Real.exp (Kbound (periodicRiesz d s) B Cc β 1))
    (Real.exp (Kbound (periodicRiesz d s) B Cc β 2)), lt_max_of_lt_left (Real.exp_pos _), ?_⟩
  intro N hN x t ht
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hl : 0 ≤ β / N := by positivity
  have hlb : β / N ≤ β := by
    rw [div_le_iff₀ hN0]
    have : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    nlinarith
  have hln : β / N * ((N - 1 : ℕ) : ℝ) ≤ β := by
    rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
    have : β / N * ((N : ℝ) - 1) = β - β / N := by field_simp
    rw [this]
    linarith
  have := (isProbabilityMeasure_poleLaw hd hs0 hsd β hβ ρ hρ N hN x t ht).2
  have hn : 0 < N - 1 := by omega
  have hC1 : Real.exp (Kbound (periodicRiesz d s) B Cc β 1) ≤
      max (Real.exp (Kbound (periodicRiesz d s) B Cc β 1))
        (Real.exp (Kbound (periodicRiesz d s) B Cc β 2)) := le_max_left _ _
  have hC2 : Real.exp (Kbound (periodicRiesz d s) B Cc β 2) ≤
      max (Real.exp (Kbound (periodicRiesz d s) B Cc β 1))
        (Real.exp (Kbound (periodicRiesz d s) B Cc β 2)) := le_max_right _ _
  constructor
  · have h1 := pole_one_le hK hB (⟨0, hn⟩ : Fin (N - 1)) hβ.le ht.1 ht.2 hl hlb hln x
      (hP := ‹_›)
    have hfm : firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) =
        (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t).map
          (fun Y : Config d (N - 1) => Y ⟨0, hn⟩) := by
      unfold firstMarginal
      rw [dif_pos hn]
    rw [hfm]
    have : IsProbabilityMeasure ((poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t).map
          (fun Y : Config d (N - 1) => Y ⟨0, hn⟩)) :=
      inferInstance
    obtain ⟨hac, hle⟩ := rnDeriv_le_of_le_withDensity _ _ _ h1
    refine ⟨hac, hle.mono fun y hy => hy.trans ?_⟩
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC1 (Real.exp_pos _).le)
  · intro i j hij
    have h2 := pole_two_le hK hB i j hij hβ.le ht.1 ht.2 hl hlb hln x (hP := ‹_›)
    have : IsProbabilityMeasure (twoMarginal
        (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) i j) :=
      by unfold twoMarginal; infer_instance
    obtain ⟨hac, hle⟩ := rnDeriv_le_of_le_withDensity _ _ _ h2
    refine ⟨hac, hle.mono fun y hy => hy.trans ?_⟩
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC2 (Real.exp_pos _).le)

end Final


/- `pole_variance_clause` (the variance clause of Lemma 4.1) is proved in `HRS.Equilibrium.PoleVariance`:
its proof uses the heat split, the weak reference and its calibration (`HeatSplit`, `WeakSpec`,
`CalibratedReference`), and these modules import this file (import cycle), so the theorem
`HRS.PoleCavityAux.pole_variance_clause` and the assembly `HRS.pole_variance_density` live there
(same names and statements). -/

end PoleDensity

end PoleCavityAux

/- `pole_variance_density` (Lemma 4.1 `M:A:lem:pole`, all three clauses) is stated and proved in
`HRS.Equilibrium.PoleVariance` (see the note above `end PoleDensity`). -/

/- `firstMarginal_density_L2` and `firstMarginal_density_uniform` (Prop 4.2, full law) are proved in `HRS.Equilibrium.MarginalDensity` (same names and statements; relocated, import cycle). -/

/- `quadStat_variance` (Prop 4.3) and `quadStat_variance_transport` (with `TransportAux`) are proved in
`HRS.Equilibrium.QuadraticVariance` (same names and statements; the proof needs modules that import this file). -/

end AllExponents

/-! ### Helpers for Lemma 4.5 (critical integrals) -/

namespace PoleCavityAux

variable {s : ℝ}
open KernelAux KernelAux2

/-- Pointwise envelope of `g_+` in box coordinates: `g_+ ≤ A ‖y‖^{-s}`. -/
theorem gPlus_envelope (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) (c : ℝ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ y ∈ Box d, y ≠ 0 → gPlus d s c (boxPt y) ≤ A * ‖y‖ ^ (-s) := by
  have hd0 : 0 < d := by omega
  obtain ⟨r, δ, hδ, hr, hloc⟩ := periodicRiesz_local_singularity (d := d) hd hs0 hsd
  obtain ⟨R, hR⟩ := (isCompact_closedBall (0 : Euc d) δ).exists_bound_of_continuousOn
    (f := Torus.lift r) (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift r) from hr).continuous.continuousOn
  obtain ⟨C1, C2, hC1, hC2, hbd⟩ := periodicRiesz_box_bound (d := d) (s := s) hd hs0.le hsd
  set θ : ℝ := δ / d with hθ
  have hθ0 : 0 < θ := by positivity
  set M : ℝ := C1 * θ ^ (-((s + (d:ℝ)) / 2)) + C2 with hM
  have hM0 : 0 ≤ M := by
    have : 0 ≤ C1 * θ ^ (-((s + (d:ℝ)) / 2)) := mul_nonneg hC1 (Real.rpow_nonneg hθ0.le _)
    linarith
  have hR0 : 0 ≤ |R| := abs_nonneg R
  refine ⟨1 + |R| + M + |c|, by linarith [abs_nonneg c], fun y hyB hy => ?_⟩
  have hypos : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hy12 : ‖y‖ ≤ 1 / 2 := Box_norm_le hyB
  -- the power is at least one
  have hone : 1 ≤ ‖y‖ ^ (-s) := by
    have h1 : (1 : ℝ) ≤ ‖y‖⁻¹ := by
      rw [le_inv_comm₀ one_pos hypos]; linarith
    calc (1 : ℝ) ≤ ‖y‖⁻¹ ^ s := Real.one_le_rpow h1 hs0.le
      _ = ‖y‖ ^ (-s) := by rw [Real.rpow_neg hypos.le, Real.inv_rpow hypos.le]
  have hpow0 : 0 ≤ ‖y‖ ^ (-s) := Real.rpow_nonneg hypos.le _
  have key : periodicRiesz d s (boxPt y) ≤ ‖y‖ ^ (-s) + |R| + M := by
    by_cases hcase : θ ≤ ‖y‖
    · have h1 := hbd y hyB hy
      have h2 : ‖y‖ ^ (-((s + (d:ℝ)) / 2)) ≤ θ ^ (-((s + (d:ℝ)) / 2)) :=
        Real.rpow_le_rpow_of_nonpos hθ0 hcase (by
          have : (0:ℝ) ≤ (s + (d:ℝ))/2 := by positivity
          linarith)
      have h3 : |periodicRiesz d s (boxPt y)| ≤ M := by
        refine h1.trans ?_
        rw [hM]
        have := mul_le_mul_of_nonneg_left h2 hC1
        linarith
      linarith [le_abs_self (periodicRiesz d s (boxPt y))]
    · replace hcase := not_le.1 hcase
      set x : Euc d := WithLp.toLp 2 y with hx
      have hxn : ‖x‖ < δ := by
        have := norm_toLp_le_card_mul hd0 y
        have hdpos : (0:ℝ) < d := by positivity
        calc ‖x‖ ≤ d * ‖y‖ := this
          _ < d * θ := by gcongr
          _ = δ := by rw [hθ]; field_simp
      have hx0 : x ≠ 0 := by
        intro h0
        apply hy
        ext i
        have := congrArg (fun z : Euc d => z i) h0
        simpa [hx] using this
      have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
      have hg : periodicRiesz d s (boxPt y) = ‖x‖ ^ (-s) + r (Torus.mk x) := by
        have := hloc x hxn hx0
        exact this
      have hrR : |r (Torus.mk x)| ≤ |R| := by
        have := hR x (by simpa using hxn.le)
        simp only [Torus.lift, Function.comp, Real.norm_eq_abs] at this
        exact this.trans (le_abs_self R)
      have h5 : ‖x‖ ^ (-s) ≤ ‖y‖ ^ (-s) :=
        Real.rpow_le_rpow_of_nonpos hypos (norm_le_norm_toLp y) (by linarith)
      rw [hg]
      linarith [le_abs_self (r (Torus.mk x))]
  unfold gPlus
  have hcc : c ≤ |c| := le_abs_self c
  have : (|R| + M + |c|) ≤ (|R| + M + |c|) * ‖y‖ ^ (-s) := by
    have h0 : 0 ≤ |R| + M + |c| := by positivity
    nlinarith
  nlinarith


theorem measurable_gPlus (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (c : ℝ) :
    Measurable (gPlus d s c) :=
  (measurable_periodicRiesz hd hs0 hsd).add_const c

theorem volume_tail (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 0 < t →
      (volume : Measure (Torus d)) {z | t ≤ gPlus d s c z} ≤ ENNReal.ofReal (K / t ^ 2) := by
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have hs0 : 0 < s := by rw [hcrit]; positivity
  have hsd : s < d := by rw [hcrit]; linarith
  obtain ⟨A, hA1, hA⟩ := gPlus_envelope hd hs0 hsd c
  have hA0 : 0 < A := by linarith
  refine ⟨2 ^ d * A ^ 2, by positivity, fun t ht => ?_⟩
  have hmeasS : MeasurableSet {z : Torus d | t ≤ gPlus d s c z} :=
    measurableSet_le measurable_const (measurable_gPlus hd hs0.le hsd c)
  set r : ℝ := (A / t) ^ (1 / s) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by positivity) _
  have hsub : ((fun y : Fin d → ℝ => boxPt y) ⁻¹' {z : Torus d | t ≤ gPlus d s c z}) ∩ Box d ⊆
      Metric.closedBall (0 : Fin d → ℝ) r := by
    rintro y ⟨hyS, hyB⟩
    rw [mem_closedBall_zero_iff]
    by_cases hy : y = 0
    · rw [hy, norm_zero]; exact hr0
    · have hypos : 0 < ‖y‖ := norm_pos_iff.2 hy
      have h1 : t ≤ A * ‖y‖ ^ (-s) := hyS.trans (hA y hyB hy)
      have h2 : ‖y‖ ^ s ≤ A / t := by
        rw [Real.rpow_neg hypos.le] at h1
        have hp : 0 < ‖y‖ ^ s := Real.rpow_pos_of_pos hypos _
        rw [le_div_iff₀ ht]
        have := (le_div_iff₀ hp).1 (show t ≤ A / ‖y‖ ^ s by simpa [div_eq_mul_inv] using h1)
        linarith
      calc ‖y‖ = (‖y‖ ^ s) ^ (1 / s) := by
            rw [← Real.rpow_mul hypos.le, mul_one_div_cancel hs0.ne', Real.rpow_one]
        _ ≤ r := Real.rpow_le_rpow (Real.rpow_nonneg hypos.le _) h2 (by positivity)
  calc (volume : Measure (Torus d)) {z | t ≤ gPlus d s c z}
      = ∫⁻ z, ({z : Torus d | t ≤ gPlus d s c z}).indicator 1 z := by
        rw [lintegral_indicator_one hmeasS]
    _ = ∫⁻ y in Box d, ({z : Torus d | t ≤ gPlus d s c z}).indicator (1 : Torus d → ℝ≥0∞) (boxPt y) :=
        lintegral_torus_box _
    _ = (volume.restrict (Box d)) ((fun y : Fin d → ℝ => boxPt y) ⁻¹' {z : Torus d | t ≤ gPlus d s c z}) := by
        rw [← lintegral_indicator_one (hmeasS.preimage (continuous_boxPt d).measurable)]
        rfl
    _ = volume (((fun y : Fin d → ℝ => boxPt y) ⁻¹' {z : Torus d | t ≤ gPlus d s c z}) ∩ Box d) := by
        rw [Measure.restrict_apply' (measurableSet_Box d)]
    _ ≤ volume (Metric.closedBall (0 : Fin d → ℝ) r) := measure_mono hsub
    _ = ENNReal.ofReal ((2 * r) ^ d) := by rw [Real.volume_pi_closedBall _ hr0]; simp
    _ = ENNReal.ofReal (2 ^ d * A ^ 2 / t ^ 2) := by
        congr 1
        have : r ^ d = (A / t) ^ (2 : ℕ) := by
          rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), hcrit]
          have : 1 / ((d : ℝ) / 2) * (d : ℝ) = ((2 : ℕ) : ℝ) := by
            push_cast; field_simp
          rw [this, Real.rpow_natCast]
        rw [mul_pow, this]; field_simp


theorem lintegral_le_tail {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ]
    (f : α → ℝ) (hf : Measurable f) (hf0 : ∀ a, 0 ≤ f a)
    (g : ℝ → ℝ) (hg : Measurable g) (hg0 : ∀ t, 0 < t → 0 ≤ g t)
    (hgi : ∀ t > 0, IntervalIntegrable g volume 0 t)
    (m : ℝ → ℝ≥0∞) (hm : ∀ t, 0 < t → μ {a | t ≤ f a} ≤ m t)
    (Φ : ℝ → ℝ) (hΦ : ∀ h, 0 ≤ h → Φ h ≤ ∫ t in (0 : ℝ)..h, g t) :
    ∫⁻ a, ENNReal.ofReal (Φ (f a)) ∂μ ≤ ∫⁻ t in Set.Ioi (0 : ℝ), m t * ENNReal.ofReal (g t) := by
  calc ∫⁻ a, ENNReal.ofReal (Φ (f a)) ∂μ
      ≤ ∫⁻ a, ENNReal.ofReal (∫ t in (0 : ℝ)..f a, g t) ∂μ :=
        lintegral_mono fun a => ENNReal.ofReal_le_ofReal (hΦ _ (hf0 a))
    _ = ∫⁻ t in Set.Ioi (0 : ℝ), μ {a | t ≤ f a} * ENNReal.ofReal (g t) :=
        lintegral_comp_eq_lintegral_meas_le_mul_of_measurable μ (fun a => hf0 a) hf hgi hg
          (fun t ht => hg0 t ht)
    _ ≤ ∫⁻ t in Set.Ioi (0 : ℝ), m t * ENNReal.ofReal (g t) :=
        setLIntegral_mono' measurableSet_Ioi fun t ht => by gcongr; exact hm t ht

theorem intervalIntegrable_bdd (g : ℝ → ℝ) (hg : Measurable g) (B : ℝ)
    (hB : ∀ t, 0 < t → |g t| ≤ B) (t : ℝ) (ht : 0 < t) : IntervalIntegrable g volume 0 t := by
  have hc : IntervalIntegrable (fun _ : ℝ => B) volume 0 t := intervalIntegrable_const
  refine hc.mono_fun' hg.aestronglyMeasurable ?_
  rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
  refine Filter.Eventually.of_forall fun x hx => ?_
  rw [Set.uIoc_of_le ht.le] at hx
  simpa using hB x hx.1


theorem lintegral_Ioi_indicator_Ioc (a b : ℝ) (ha : 0 ≤ a) (G : ℝ → ℝ≥0∞) :
    ∫⁻ t in Set.Ioi (0 : ℝ), (Set.Ioc a b).indicator G t = ∫⁻ t in Set.Ioc a b, G t := by
  rw [lintegral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc]
  congr 2
  ext t
  simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioi]
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, lt_of_le_of_lt ha h.1⟩

theorem lintegral_Ioc_ofReal (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume a b) (hf0 : ∀ t ∈ Set.Ioc a b, 0 ≤ f t) :
    ∫⁻ t in Set.Ioc a b, ENNReal.ofReal (f t) = ENNReal.ofReal (∫ t in a..b, f t) := by
  rw [intervalIntegral.integral_of_le hab]
  rw [ofReal_integral_eq_lintegral_ofReal]
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hf
  · exact (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall hf0)

theorem int1_bound (K H : ℝ) (hK : 0 < K) (hH : 1 ≤ H) :
    ∫⁻ t in Set.Ioi (0 : ℝ), min 1 (ENNReal.ofReal (K / t ^ 2)) *
        ENNReal.ofReal (if t ≤ H then 2 * t else 0) ≤
      ENNReal.ofReal (1 + 2 * K * Real.log H) := by
  have hpt : ∀ t ∈ Set.Ioi (0 : ℝ), min 1 (ENNReal.ofReal (K / t ^ 2)) *
        ENNReal.ofReal (if t ≤ H then 2 * t else 0) ≤
      (Set.Ioc (0 : ℝ) 1).indicator (fun t => ENNReal.ofReal (2 * t)) t +
        (Set.Ioc (1 : ℝ) H).indicator (fun t => ENNReal.ofReal (2 * K / t)) t := by
    intro t ht
    have ht0 : 0 < t := ht
    by_cases h1 : t ≤ 1
    · have hH' : t ≤ H := h1.trans hH
      simp only [hH', ↓reduceIte]
      rw [Set.indicator_of_mem (show t ∈ Set.Ioc (0 : ℝ) 1 from ⟨ht0, h1⟩)]
      calc _ ≤ 1 * ENNReal.ofReal (2 * t) := by gcongr; exact min_le_left _ _
        _ = _ := one_mul _
        _ ≤ _ := le_self_add
    · push Not at h1
      by_cases h2 : t ≤ H
      · simp only [h2, ↓reduceIte]
        rw [Set.indicator_of_mem (show t ∈ Set.Ioc (1 : ℝ) H from ⟨h1, h2⟩)]
        calc _ ≤ ENNReal.ofReal (K / t ^ 2) * ENNReal.ofReal (2 * t) := by
              gcongr; exact min_le_right _ _
          _ = ENNReal.ofReal (K / t ^ 2 * (2 * t)) := (ENNReal.ofReal_mul (by positivity)).symm
          _ = ENNReal.ofReal (2 * K / t) := by congr 1; field_simp
          _ ≤ _ := le_add_self
      · simp only [h2, ↓reduceIte]; simp
  calc _ ≤ ∫⁻ t in Set.Ioi (0 : ℝ), ((Set.Ioc (0 : ℝ) 1).indicator (fun t => ENNReal.ofReal (2 * t)) t +
        (Set.Ioc (1 : ℝ) H).indicator (fun t => ENNReal.ofReal (2 * K / t)) t) :=
        setLIntegral_mono' measurableSet_Ioi hpt
    _ = (∫⁻ t in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (2 * t)) +
          ∫⁻ t in Set.Ioc (1 : ℝ) H, ENNReal.ofReal (2 * K / t) := by
        rw [lintegral_add_left, lintegral_Ioi_indicator_Ioc _ _ le_rfl,
          lintegral_Ioi_indicator_Ioc _ _ zero_le_one]
        exact (ENNReal.measurable_ofReal.comp (measurable_const.mul measurable_id)).indicator
          measurableSet_Ioc
    _ = ENNReal.ofReal (1 + 2 * K * Real.log H) := by
        have hlog : 0 ≤ Real.log H := Real.log_nonneg hH
        have e1 : ∫⁻ t in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (2 * t) = ENNReal.ofReal 1 := by
          rw [lintegral_Ioc_ofReal 0 1 zero_le_one (fun t => 2 * t)
            ((continuous_const.mul continuous_id).intervalIntegrable _ _)
            (fun t ht => by have := ht.1; linarith)]
          congr 1
          rw [intervalIntegral.integral_const_mul, integral_id]; norm_num
        have e2 : ∫⁻ t in Set.Ioc (1 : ℝ) H, ENNReal.ofReal (2 * K / t) =
            ENNReal.ofReal (2 * K * Real.log H) := by
          have hcont : ContinuousOn (fun t : ℝ => 2 * K / t) (Set.uIcc 1 H) :=
            continuousOn_const.div continuousOn_id (fun x hx => by
              rw [Set.uIcc_of_le hH] at hx; exact (lt_of_lt_of_le one_pos hx.1).ne')
          rw [lintegral_Ioc_ofReal 1 H hH (fun t => 2 * K / t) hcont.intervalIntegrable
            (fun t ht => by have := ht.1; have : (0:ℝ) < t := by linarith
                            positivity)]
          congr 1
          have : (fun t : ℝ => 2 * K / t) = fun t => (2 * K) * t⁻¹ := by
            funext t; rw [div_eq_mul_inv]
          rw [this, intervalIntegral.integral_const_mul, integral_inv_of_pos one_pos (by linarith)]
          simp
        rw [e1, e2, ← ENNReal.ofReal_add one_pos.le (by positivity)]


theorem int2_bound (K H : ℝ) (hK : 0 < K) (hH : 0 < H) :
    ∫⁻ t in Set.Ioi (0 : ℝ), min 1 (ENNReal.ofReal (K / t ^ 2)) *
        ENNReal.ofReal (if H ≤ t then 1 else 0) ≤ ENNReal.ofReal (K / H) := by
  have hpt : ∀ t ∈ Set.Ioi (0 : ℝ), min 1 (ENNReal.ofReal (K / t ^ 2)) *
        ENNReal.ofReal (if H ≤ t then 1 else 0) ≤
      (Set.Ici H).indicator (fun t => ENNReal.ofReal (K * t ^ (-2 : ℝ))) t := by
    intro t ht
    have ht0 : 0 < t := ht
    by_cases h : H ≤ t
    · simp only [h, ↓reduceIte]
      rw [Set.indicator_of_mem (show t ∈ Set.Ici H from h)]
      calc _ ≤ ENNReal.ofReal (K / t ^ 2) * ENNReal.ofReal 1 := by gcongr; exact min_le_right _ _
        _ = ENNReal.ofReal (K * t ^ (-2 : ℝ)) := by
          rw [ENNReal.ofReal_one, mul_one, Real.rpow_neg ht0.le, div_eq_mul_inv]
          norm_cast
    · simp only [h, ↓reduceIte]; simp
  calc _ ≤ ∫⁻ t in Set.Ioi (0 : ℝ), (Set.Ici H).indicator
          (fun t => ENNReal.ofReal (K * t ^ (-2 : ℝ))) t := setLIntegral_mono' measurableSet_Ioi hpt
    _ = ∫⁻ t in Set.Ici H, ENNReal.ofReal (K * t ^ (-2 : ℝ)) := by
        rw [lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
        congr 2
        ext t
        simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioi]
        exact ⟨fun h => h.1, fun h => ⟨h, lt_of_lt_of_le hH h⟩⟩
    _ = ∫⁻ t in Set.Ioi H, ENNReal.ofReal (K * t ^ (-2 : ℝ)) :=
        setLIntegral_congr Ioi_ae_eq_Ici.symm
    _ = ENNReal.ofReal (∫ t in Set.Ioi H, K * t ^ (-2 : ℝ)) := by
        rw [ofReal_integral_eq_lintegral_ofReal]
        · exact (integrableOn_Ioi_rpow_of_lt (by norm_num) hH).const_mul K
        · exact (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht =>
            mul_nonneg hK.le (Real.rpow_nonneg (lt_trans hH ht).le _))
    _ = ENNReal.ofReal (K / H) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hH]
        congr 1
        norm_num
        rw [Real.rpow_neg_one]
        field_simp


theorem int3_bound (K H v : ℝ) (hK : 0 < K) (hH : 0 < H) (hv : 2 < v) :
    ∫⁻ t in Set.Ioi (0 : ℝ), min 1 (ENNReal.ofReal (K / t ^ 2)) *
        ENNReal.ofReal (if t ≤ H then v * t ^ (v - 1) else 0) ≤
      ENNReal.ofReal (v * K / (v - 2) * H ^ (v - 2)) := by
  have hpt : ∀ t ∈ Set.Ioi (0 : ℝ), min 1 (ENNReal.ofReal (K / t ^ 2)) *
        ENNReal.ofReal (if t ≤ H then v * t ^ (v - 1) else 0) ≤
      (Set.Ioc (0 : ℝ) H).indicator (fun t => ENNReal.ofReal (v * K * t ^ (v - 3))) t := by
    intro t ht
    have ht0 : 0 < t := ht
    by_cases h : t ≤ H
    · simp only [h, ↓reduceIte]
      rw [Set.indicator_of_mem (show t ∈ Set.Ioc (0 : ℝ) H from ⟨ht0, h⟩)]
      calc _ ≤ ENNReal.ofReal (K / t ^ 2) * ENNReal.ofReal (v * t ^ (v - 1)) := by
            gcongr; exact min_le_right _ _
        _ = ENNReal.ofReal (K / t ^ 2 * (v * t ^ (v - 1))) :=
            (ENNReal.ofReal_mul (by positivity)).symm
        _ = _ := by
            congr 1
            have : t ^ (v - 1) = t ^ (v - 3) * t ^ (2 : ℕ) := by
              rw [← Real.rpow_natCast, ← Real.rpow_add ht0]; congr 1; push_cast; ring
            rw [this]; field_simp
    · simp only [h, ↓reduceIte]; simp
  have hint : IntervalIntegrable (fun t : ℝ => v * K * t ^ (v - 3)) volume 0 H :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul _
  calc _ ≤ ∫⁻ t in Set.Ioi (0 : ℝ), (Set.Ioc (0 : ℝ) H).indicator
          (fun t => ENNReal.ofReal (v * K * t ^ (v - 3))) t := setLIntegral_mono' measurableSet_Ioi hpt
    _ = ∫⁻ t in Set.Ioc (0 : ℝ) H, ENNReal.ofReal (v * K * t ^ (v - 3)) :=
        lintegral_Ioi_indicator_Ioc _ _ le_rfl _
    _ = ENNReal.ofReal (∫ t in (0 : ℝ)..H, v * K * t ^ (v - 3)) :=
        lintegral_Ioc_ofReal 0 H hH.le _ hint (fun t ht => by
          have := ht.1; positivity)
    _ = _ := by
        congr 1
        rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith))]
        have h1 : v - 3 + 1 = v - 2 := by ring
        rw [h1, Real.zero_rpow (by linarith)]
        field_simp
        ring


theorem measurable_g1 (H : ℝ) : Measurable (fun t : ℝ => if t ≤ H then 2 * t else 0) :=
  Measurable.ite (measurableSet_le measurable_id measurable_const)
    (measurable_const.mul measurable_id) measurable_const

theorem integrable_g1 (H : ℝ) (hH : 0 < H) (b : ℝ) (hb : 0 < b) :
    IntervalIntegrable (fun t : ℝ => if t ≤ H then 2 * t else 0) volume 0 b := by
  refine intervalIntegrable_bdd _ (measurable_g1 H) (2 * H) (fun t ht => ?_) b hb
  by_cases h : t ≤ H
  · simp only [h, ↓reduceIte]; rw [abs_of_pos (by linarith)]; linarith
  · simp only [h, ↓reduceIte, abs_zero]; linarith

theorem hPhi1 (H : ℝ) (hH : 0 < H) (h : ℝ) (hh : 0 ≤ h) :
    min h H ^ 2 ≤ ∫ t in (0 : ℝ)..h, (if t ≤ H then 2 * t else 0) := by
  have key : ∀ b, 0 ≤ b → b ≤ H → ∫ t in (0 : ℝ)..b, (if t ≤ H then 2 * t else 0) = b ^ 2 := by
    intro b hb0 hbH
    rw [intervalIntegral.integral_congr (g := fun t : ℝ => 2 * t) (fun t ht => by
      rw [Set.uIcc_of_le hb0] at ht
      simp only [ht.2.trans hbH, ↓reduceIte])]
    rw [intervalIntegral.integral_const_mul, integral_id]; ring
  rcases le_or_gt h H with hle | hlt
  · rw [min_eq_left hle, key h hh hle]
  · rw [min_eq_right hlt.le, ← key H hH.le le_rfl]
    refine intervalIntegral.integral_mono_interval le_rfl hH.le hlt.le ?_ (integrable_g1 H hH h (hH.trans hlt))
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun t ht => ?_)
    simp only [Pi.zero_apply]
    split_ifs
    · linarith [ht.1]
    · exact le_rfl


theorem measurable_g2 (H : ℝ) : Measurable (fun t : ℝ => if H ≤ t then (1 : ℝ) else 0) :=
  Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const measurable_const

theorem integrable_g2 (H : ℝ) (b : ℝ) (hb : 0 < b) :
    IntervalIntegrable (fun t : ℝ => if H ≤ t then (1 : ℝ) else 0) volume 0 b := by
  refine intervalIntegrable_bdd _ (measurable_g2 H) 1 (fun t ht => ?_) b hb
  by_cases h : H ≤ t
  · simp [h]
  · simp [h]

theorem hPhi2 (H : ℝ) (hH : 0 < H) (h : ℝ) (hh : 0 ≤ h) :
    h - min h H ≤ ∫ t in (0 : ℝ)..h, (if H ≤ t then (1 : ℝ) else 0) := by
  rcases le_or_gt h H with hle | hlt
  · rw [min_eq_left hle, sub_self]
    exact intervalIntegral.integral_nonneg hh (fun u _ => by split_ifs <;> norm_num)
  · rw [min_eq_right hlt.le]
    have h1 : ∫ t in H..h, (if H ≤ t then (1 : ℝ) else 0) = h - H := by
      rw [intervalIntegral.integral_congr (g := fun _ : ℝ => (1 : ℝ)) (fun t ht => by
        rw [Set.uIcc_of_le hlt.le] at ht
        simp only [ht.1, ↓reduceIte])]
      simp
    rw [← h1]
    refine intervalIntegral.integral_mono_interval hH.le hlt.le le_rfl ?_ (integrable_g2 H h (hH.trans hlt))
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun t ht => ?_)
    simp only [Pi.zero_apply]
    split_ifs <;> norm_num

theorem measurable_g3 (H v : ℝ) :
    Measurable (fun t : ℝ => if t ≤ H then v * t ^ (v - 1) else 0) :=
  Measurable.ite (measurableSet_le measurable_id measurable_const)
    (measurable_const.mul (measurable_id.pow_const _)) measurable_const

theorem integrable_g3 (H v : ℝ) (hH : 0 < H) (hv : 2 < v) (b : ℝ) (hb : 0 < b) :
    IntervalIntegrable (fun t : ℝ => if t ≤ H then v * t ^ (v - 1) else 0) volume 0 b := by
  refine intervalIntegrable_bdd _ (measurable_g3 H v) (v * H ^ (v - 1)) (fun t ht => ?_) b hb
  by_cases h : t ≤ H
  · simp only [h, ↓reduceIte]
    rw [abs_of_nonneg (by positivity)]
    have : t ^ (v - 1) ≤ H ^ (v - 1) := Real.rpow_le_rpow ht.le h (by linarith)
    nlinarith
  · simp only [h, ↓reduceIte, abs_zero]; positivity

theorem hPhi3 (H v : ℝ) (hH : 0 < H) (hv : 2 < v) (h : ℝ) (hh : 0 ≤ h) :
    min h H ^ v ≤ ∫ t in (0 : ℝ)..h, (if t ≤ H then v * t ^ (v - 1) else 0) := by
  have key : ∀ b, 0 ≤ b → b ≤ H →
      ∫ t in (0 : ℝ)..b, (if t ≤ H then v * t ^ (v - 1) else 0) = b ^ v := by
    intro b hb0 hbH
    rw [intervalIntegral.integral_congr (g := fun t : ℝ => v * t ^ (v - 1)) (fun t ht => by
      rw [Set.uIcc_of_le hb0] at ht
      simp only [ht.2.trans hbH, ↓reduceIte])]
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith))]
    have h1 : v - 1 + 1 = v := by ring
    rw [h1, Real.zero_rpow (by linarith)]
    field_simp
    ring
  rcases le_or_gt h H with hle | hlt
  · rw [min_eq_left hle, key h hh hle]
  · rw [min_eq_right hlt.le, ← key H hH.le le_rfl]
    refine intervalIntegral.integral_mono_interval le_rfl hH.le hlt.le ?_
      (integrable_g3 H v hH hv h (hH.trans hlt))
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun t ht => ?_)
    simp only [Pi.zero_apply]
    have := ht.1
    split_ifs
    · positivity
    · exact le_rfl


theorem hs_aux (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) : 0 ≤ s ∧ s < d := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  constructor <;> rw [hcrit] <;> linarith

section Volume

variable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)
include hd hcrit hc

theorem vol_sq_trunc :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 2 ≤ H →
      ∫⁻ z, ENNReal.ofReal (gTrunc d s c H z ^ 2) ≤ ENNReal.ofReal (C * Real.log H) := by
  obtain ⟨K, hK, hKt⟩ := volume_tail hd hcrit c
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  refine ⟨2 + 2 * K, by positivity, fun H hH => ?_⟩
  have hH0 : 0 < H := by linarith
  have hlog : (1 : ℝ) / 2 ≤ Real.log H := by
    have := Real.log_two_gt_d9
    have h2 : Real.log 2 ≤ Real.log H := Real.log_le_log (by norm_num) hH
    linarith
  have h1 := lintegral_le_tail (volume : Measure (Torus d)) (gPlus d s c)
    (measurable_gPlus hd hs0 hsd c) (fun z => hc z) _ (measurable_g1 H) (fun t ht => by
      split_ifs
      · linarith
      · exact le_rfl)
    (fun t ht => integrable_g1 H hH0 t ht)
    (fun t => min 1 (ENNReal.ofReal (K / t ^ 2))) (fun t ht => le_min prob_le_one (hKt t ht))
    (fun h => min h H ^ 2) (fun h hh => hPhi1 H hH0 h hh)
  refine h1.trans ((int1_bound K H hK (by linarith)).trans ?_)
  refine ENNReal.ofReal_le_ofReal ?_
  nlinarith

theorem vol_excess :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 0 < H →
      ∫⁻ z, ENNReal.ofReal (gPlus d s c z - gTrunc d s c H z) ≤ ENNReal.ofReal (C / H) := by
  obtain ⟨K, hK, hKt⟩ := volume_tail hd hcrit c
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  refine ⟨K, hK, fun H hH0 => ?_⟩
  have h1 := lintegral_le_tail (volume : Measure (Torus d)) (gPlus d s c)
    (measurable_gPlus hd hs0 hsd c) (fun z => hc z) _ (measurable_g2 H) (fun t ht => by
      split_ifs <;> norm_num)
    (fun t ht => integrable_g2 H t ht)
    (fun t => min 1 (ENNReal.ofReal (K / t ^ 2))) (fun t ht => le_min prob_le_one (hKt t ht))
    (fun h => h - min h H) (fun h hh => hPhi2 H hH0 h hh)
  exact h1.trans (int2_bound K H hK hH0)

theorem vol_pow_trunc (v : ℝ) (hv : 2 < v) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 0 < H →
      ∫⁻ z, ENNReal.ofReal (gTrunc d s c H z ^ v) ≤ ENNReal.ofReal (C * H ^ (v - 2)) := by
  obtain ⟨K, hK, hKt⟩ := volume_tail hd hcrit c
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  refine ⟨v * K / (v - 2), by have : 0 < v - 2 := by linarith
                              positivity, fun H hH0 => ?_⟩
  have h1 := lintegral_le_tail (volume : Measure (Torus d)) (gPlus d s c)
    (measurable_gPlus hd hs0 hsd c) (fun z => hc z) _ (measurable_g3 H v) (fun t ht => by
      split_ifs
      · positivity
      · exact le_rfl)
    (fun t ht => integrable_g3 H v hH0 hv t ht)
    (fun t => min 1 (ENNReal.ofReal (K / t ^ 2))) (fun t ht => le_min prob_le_one (hKt t ht))
    (fun h => min h H ^ v) (fun h hh => hPhi3 H v hH0 hv h hh)
  exact h1.trans (int3_bound K H v hK hH0 hv)

end Volume


theorem conj_trunc (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 2 ≤ H → ∀ x : Torus d,
      ∫⁻ y, ENNReal.ofReal (gTrunc d s c H (x - y) ^ 2) ∂(withDensityReal ρ) ≤
          ENNReal.ofReal (C * Real.log H) ∧
        ∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y) - gTrunc d s c H (x - y))
            ∂(withDensityReal ρ) ≤ ENNReal.ofReal (C / H) := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_density_bound hρ
  obtain ⟨C1, hC1, h1⟩ := vol_sq_trunc hd hcrit c hc
  obtain ⟨C2, hC2, h2⟩ := vol_excess hd hcrit c hc
  refine ⟨Λ * max C1 C2, by positivity, fun H hH x => ⟨?_, ?_⟩⟩
  · calc _ ≤ ENNReal.ofReal Λ * ∫⁻ z, ENNReal.ofReal (gTrunc d s c H z ^ 2) :=
          lintegral_conv_le ρ Λ hΛ (fun z => ENNReal.ofReal (gTrunc d s c H z ^ 2)) x
      _ ≤ ENNReal.ofReal Λ * ENNReal.ofReal (C1 * Real.log H) := by gcongr; exact h1 H hH
      _ = ENNReal.ofReal (Λ * (C1 * Real.log H)) := (ENNReal.ofReal_mul hΛ0.le).symm
      _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hlog : 0 ≤ Real.log H := Real.log_nonneg (by linarith)
        have := le_max_left C1 C2
        nlinarith [mul_nonneg hΛ0.le hlog]
  · have hH0 : 0 < H := by linarith
    calc _ ≤ ENNReal.ofReal Λ * ∫⁻ z, ENNReal.ofReal (gPlus d s c z - gTrunc d s c H z) :=
          lintegral_conv_le ρ Λ hΛ (fun z => ENNReal.ofReal (gPlus d s c z - gTrunc d s c H z)) x
      _ ≤ ENNReal.ofReal Λ * ENNReal.ofReal (C2 / H) := by gcongr; exact h2 H hH0
      _ = ENNReal.ofReal (Λ * (C2 / H)) := (ENNReal.ofReal_mul hΛ0.le).symm
      _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have := le_max_right C1 C2
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right this hH0.le) hΛ0.le


theorem conj_pow (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ)
    (v : ℝ) (hv : 2 < v) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 2 ≤ H → ∀ x : Torus d,
      ∫⁻ y, ENNReal.ofReal (gTrunc d s c H (x - y) ^ v) ∂(withDensityReal ρ) ≤
          ENNReal.ofReal (C * H ^ (v - 2)) := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_density_bound hρ
  obtain ⟨C1, hC1, h1⟩ := vol_pow_trunc hd hcrit c hc v hv
  refine ⟨Λ * C1, by positivity, fun H hH x => ?_⟩
  calc _ ≤ ENNReal.ofReal Λ * ∫⁻ z, ENNReal.ofReal (gTrunc d s c H z ^ v) :=
        lintegral_conv_le ρ Λ hΛ (fun z => ENNReal.ofReal (gTrunc d s c H z ^ v)) x
    _ ≤ ENNReal.ofReal Λ * ENNReal.ofReal (C1 * H ^ (v - 2)) := by
        gcongr; exact h1 H (by linarith)
    _ = ENNReal.ofReal (Λ * (C1 * H ^ (v - 2))) := (ENNReal.ofReal_mul hΛ0.le).symm
    _ = _ := by congr 1; ring

theorem sq_exp_le (a u : ℝ) (ha : 0 ≤ a) (hu : 0 < u) :
    a ^ 2 * Real.exp (-u * a) ≤ 4 * min a (1 / u) ^ 2 := by
  rcases le_or_gt a (1 / u) with h | h
  · rw [min_eq_left h]
    have : Real.exp (-u * a) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    nlinarith [sq_nonneg a]
  · rw [min_eq_right h.le]
    have h1 : (u * a / 2 + 1) ^ 2 ≤ Real.exp (u * a) := by
      have := Real.add_one_le_exp (u * a / 2)
      have h2 : Real.exp (u * a) = Real.exp (u * a / 2) ^ 2 := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      rw [h2]
      exact pow_le_pow_left₀ (by positivity) this 2
    have h3 : (u * a) ^ 2 ≤ 4 * Real.exp (u * a) := by nlinarith [sq_nonneg (u * a / 2)]
    have h4 : a ^ 2 * Real.exp (-u * a) * Real.exp (u * a) = a ^ 2 := by
      rw [mul_assoc, ← Real.exp_add]; simp
    have hpos := Real.exp_pos (u * a)
    have h5 : a ^ 2 * Real.exp (-u * a) ≤ 4 * (1 / u) ^ 2 := by
      have hu2 : 0 < u ^ 2 := by positivity
      rw [show 4 * (1 / u) ^ 2 = 4 / u ^ 2 by field_simp]
      rw [le_div_iff₀ hu2]
      have hE : 0 < Real.exp (-u * a) := Real.exp_pos _
      have : a ^ 2 * Real.exp (-u * a) * u ^ 2 * Real.exp (u * a) = (u * a) ^ 2 := by
        rw [show a ^ 2 * Real.exp (-u * a) * u ^ 2 * Real.exp (u * a) =
          (a ^ 2 * Real.exp (-u * a) * Real.exp (u * a)) * u ^ 2 by ring, h4]; ring
      nlinarith [mul_pos hE hpos]
    exact h5


theorem conj_expo (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 0 < u → u ≤ 1 → ∀ x : Torus d,
      ∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y) ^ 2 * Real.exp (-u * gPlus d s c (x - y)))
          ∂(withDensityReal ρ) ≤ ENNReal.ofReal (C * (1 + |Real.log u|)) := by
  have := isProbabilityMeasure_mu hρ
  obtain ⟨C1, hC1, h1⟩ := conj_trunc hd hcrit c hc ρ hρ
  refine ⟨max (4 * C1) 16, by positivity, fun u hu hu1 x => ?_⟩
  set H : ℝ := 1 / u with hH
  have hH1 : 1 ≤ H := by rw [hH, le_div_iff₀ hu]; linarith
  have hpt : ∀ y, ENNReal.ofReal (gPlus d s c (x - y) ^ 2 * Real.exp (-u * gPlus d s c (x - y))) ≤
      ENNReal.ofReal 4 * ENNReal.ofReal (gTrunc d s c H (x - y) ^ 2) := by
    intro y
    rw [← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := sq_exp_le (gPlus d s c (x - y)) u (hc _) hu
    exact this
  have hlog : |Real.log u| = Real.log H := by
    rw [hH, one_div, Real.log_inv, abs_of_nonpos (Real.log_nonpos hu.le hu1)]
  calc _ ≤ ∫⁻ y, ENNReal.ofReal 4 * ENNReal.ofReal (gTrunc d s c H (x - y) ^ 2) ∂(withDensityReal ρ) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal 4 * ∫⁻ y, ENNReal.ofReal (gTrunc d s c H (x - y) ^ 2) ∂(withDensityReal ρ) := by
        rw [lintegral_const_mul']
        exact ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (max (4 * C1) 16 * (1 + |Real.log u|)) := by
        rcases le_or_gt 2 H with h2 | h2
        · have := (h1 H h2 x).1
          calc _ ≤ ENNReal.ofReal 4 * ENNReal.ofReal (C1 * Real.log H) := by gcongr
            _ = ENNReal.ofReal (4 * (C1 * Real.log H)) := (ENNReal.ofReal_mul (by norm_num)).symm
            _ ≤ _ := by
              refine ENNReal.ofReal_le_ofReal ?_
              have hl : 0 ≤ Real.log H := Real.log_nonneg hH1
              rw [hlog]
              have := le_max_left (4 * C1) 16
              have := le_max_right (4 * C1) 16
              nlinarith [abs_nonneg (Real.log u)]
        · have hb : ∀ y, ENNReal.ofReal (gTrunc d s c H (x - y) ^ 2) ≤ ENNReal.ofReal 4 := by
            intro y
            refine ENNReal.ofReal_le_ofReal ?_
            have h0 : 0 ≤ gTrunc d s c H (x - y) := le_min (hc _) (by linarith)
            have : gTrunc d s c H (x - y) ≤ 2 := (min_le_right _ _).trans h2.le
            nlinarith
          calc _ ≤ ENNReal.ofReal 4 * ∫⁻ y, ENNReal.ofReal 4 ∂(withDensityReal ρ) :=
                mul_le_mul' le_rfl (lintegral_mono hb)
            _ = ENNReal.ofReal 4 * ENNReal.ofReal 4 := by simp
            _ = ENNReal.ofReal 16 := by rw [← ENNReal.ofReal_mul (by norm_num)]; norm_num
            _ ≤ _ := by
              refine ENNReal.ofReal_le_ofReal ?_
              have := le_max_right (4 * C1) 16
              nlinarith [abs_nonneg (Real.log u)]


theorem lintegral_sq_le' {α : Type*} [MeasurableSpace α] (ν : Measure α) (F : α → ℝ≥0∞)
    (hF : AEMeasurable F ν) :
    (∫⁻ x, F x ∂ν) ^ 2 ≤ ν Set.univ * ∫⁻ x, F x ^ 2 ∂ν := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν (Real.HolderConjugate.two_two)
    (f := fun _ => (1 : ℝ≥0∞)) (g := F) aemeasurable_const hF
  simp only [Pi.mul_apply, one_mul, ENNReal.one_rpow, lintegral_const, one_mul] at h
  have h2 : (∫⁻ x, F x ∂ν) ^ 2 ≤ ((ν Set.univ) ^ (1 / (2:ℝ)) * (∫⁻ x, F x ^ (2:ℝ) ∂ν) ^ (1 / (2:ℝ))) ^ 2 :=
    pow_le_pow_left' h 2
  have e1 : ∀ X : ℝ≥0∞, (X ^ (1 / (2:ℝ))) ^ 2 = X := by
    intro X
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  rw [mul_pow, e1, e1] at h2
  simpa [ENNReal.rpow_two] using h2

theorem weighted_cs {α : Type*} [MeasurableSpace α] (μ : Measure α) (φ F : α → ℝ≥0∞)
    (hφ : Measurable φ) (hF : Measurable F) :
    (∫⁻ x, φ x * F x ∂μ) ^ 2 ≤ (∫⁻ x, φ x ∂μ) * ∫⁻ x, φ x * F x ^ 2 ∂μ := by
  have h := lintegral_sq_le' (μ.withDensity φ) F hF.aemeasurable
  rw [lintegral_withDensity_eq_lintegral_mul _ hφ hF,
    lintegral_withDensity_eq_lintegral_mul _ hφ (hF.pow_const 2),
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
  simpa using h

theorem lintegral_gPlus_lt_top (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ) :
    ∫⁻ z, ENNReal.ofReal (gPlus d s c z) < ∞ := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  exact ((integrable_periodicRiesz hd hs0 hsd).add (integrable_const c)).lintegral_lt_top

theorem gPlus_neg (c : ℝ) (z : Torus d) : gPlus d s c (-z) = gPlus d s c z := by
  unfold gPlus; rw [periodicRiesz_neg]

theorem conj_schur (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (_hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Torus d → ℝ, Measurable f →
      ∫⁻ x, (∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y)) * ‖f y‖ₑ ∂(withDensityReal ρ)) ^ 2
          ∂(withDensityReal ρ) ≤
        ENNReal.ofReal C * ∫⁻ y, ‖f y‖ₑ ^ 2 ∂(withDensityReal ρ) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_density_bound hρ
  have hgm := measurable_gPlus hd hs0 hsd c
  set a : Torus d → ℝ≥0∞ := fun z => ENNReal.ofReal (gPlus d s c z) with ha
  have ham : Measurable a := ENNReal.measurable_ofReal.comp hgm
  set S : ℝ≥0∞ := ENNReal.ofReal Λ * ∫⁻ z, a z with hS
  have hSfin : S ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (lintegral_gPlus_lt_top hd hcrit c).ne
  have hprob := isProbabilityMeasure_mu hρ
  set μ := withDensityReal ρ with hμ
  have h1 : ∀ x, ∫⁻ y, a (x - y) ∂μ ≤ S := fun x =>
    lintegral_conv_le ρ Λ hΛ a x
  have h2 : ∀ y, ∫⁻ x, a (x - y) ∂μ ≤ S := by
    intro y
    have : ∀ x, a (x - y) = a (y - x) := fun x => by
      simp only [ha]; rw [← gPlus_neg (s := s) c (y - x), neg_sub]
    simp_rw [this]
    exact h1 y
  refine ⟨(S ^ 2).toReal + 1, by positivity, fun f hf => ?_⟩
  have hFm : Measurable fun y => ‖f y‖ₑ := hf.enorm
  have hSq : S ^ 2 ≤ ENNReal.ofReal ((S ^ 2).toReal + 1) := by
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg zero_le_one, ENNReal.ofReal_toReal
      (ENNReal.pow_ne_top hSfin)]
    exact le_self_add
  calc ∫⁻ x, (∫⁻ y, a (x - y) * ‖f y‖ₑ ∂μ) ^ 2 ∂μ
      ≤ ∫⁻ x, S * ∫⁻ y, a (x - y) * ‖f y‖ₑ ^ 2 ∂μ ∂μ := by
        refine lintegral_mono fun x => ?_
        refine (weighted_cs μ (fun y => a (x - y)) (fun y => ‖f y‖ₑ)
          (ham.comp (measurable_const.sub measurable_id)) hFm).trans ?_
        exact mul_le_mul' (h1 x) le_rfl
    _ = S * ∫⁻ x, ∫⁻ y, a (x - y) * ‖f y‖ₑ ^ 2 ∂μ ∂μ := lintegral_const_mul' _ _ hSfin
    _ = S * ∫⁻ y, ∫⁻ x, a (x - y) * ‖f y‖ₑ ^ 2 ∂μ ∂μ := by
        congr 1
        refine lintegral_lintegral_swap (f := fun x y => a (x - y) * ‖f y‖ₑ ^ 2) ?_
        exact ((ham.comp (measurable_fst.sub measurable_snd)).mul
          ((hFm.comp measurable_snd).pow_const 2)).aemeasurable
    _ = S * ∫⁻ y, (∫⁻ x, a (x - y) ∂μ) * ‖f y‖ₑ ^ 2 ∂μ := by
        congr 1
        refine lintegral_congr fun y => ?_
        exact lintegral_mul_const _ (ham.comp (measurable_id.sub measurable_const))
    _ ≤ S * ∫⁻ y, S * ‖f y‖ₑ ^ 2 ∂μ := by
        refine mul_le_mul' le_rfl (lintegral_mono fun y => ?_)
        exact mul_le_mul' (h2 y) le_rfl
    _ = S * (S * ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ) := by
        congr 1; exact lintegral_const_mul' _ _ hSfin
    _ = S ^ 2 * ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ := by ring
    _ ≤ _ := mul_le_mul' hSq le_rfl


theorem small_arith (Mb C2 e : ℝ) (hMb : 0 ≤ Mb) (hC2 : 0 < C2) (he : 0 < e) :
    Real.sqrt ((Mb + 1) / e) * e + Mb * (C2 / Real.sqrt ((Mb + 1) / e)) ≤
      (1 + C2) * Real.sqrt (Mb + 1) * Real.sqrt e := by
  have hsq : 0 < Real.sqrt (Mb + 1) := Real.sqrt_pos.2 (by linarith)
  have hse : 0 < Real.sqrt e := Real.sqrt_pos.2 he
  have e1 : Real.sqrt ((Mb + 1) / e) = Real.sqrt (Mb + 1) / Real.sqrt e := Real.sqrt_div' _ he.le
  have e2 : e = Real.sqrt e ^ 2 := (Real.sq_sqrt he.le).symm
  have e3 : Mb + 1 = Real.sqrt (Mb + 1) ^ 2 := (Real.sq_sqrt (by linarith)).symm
  rw [e1]
  set p := Real.sqrt (Mb + 1)
  set q := Real.sqrt e
  have h1 : p / q * e = p * q := by
    rw [e2]; field_simp
  have h2 : Mb * (C2 / (p / q)) = Mb * C2 * q / p := by field_simp
  rw [h1, h2]
  have h3 : Mb * C2 * q / p ≤ C2 * p * q := by
    rw [div_le_iff₀ hsq]
    have : Mb ≤ p ^ 2 := by rw [← e3]; linarith
    nlinarith [mul_pos hC2 hse]
  nlinarith

theorem conj_small (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (M : ℝ) :
    ∃ CM : ℝ, ∀ (w : Torus d → ℝ) (e : ℝ), Measurable w → (∀ y, |w y| ≤ M) →
      e ≤ 1 → ∫⁻ y, ‖w y‖ₑ ≤ ENNReal.ofReal e → ∀ x : Torus d,
        ∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y)) * ‖w y‖ₑ ≤
          ENNReal.ofReal (CM * Real.sqrt e) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  obtain ⟨C2, hC2, h2⟩ := vol_excess hd hcrit c hc
  have hgm := measurable_gPlus hd hs0 hsd c
  refine ⟨(1 + C2) * Real.sqrt (|M| + 1), fun w e hw hM he hint x => ?_⟩
  have hwm : Measurable fun y => ‖w y‖ₑ := hw.enorm
  have hMb : ∀ y, ‖w y‖ₑ ≤ ENNReal.ofReal |M| := by
    intro y
    rw [← ofReal_norm, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal ((hM y).trans (le_abs_self M))
  rcases le_or_gt e 0 with he0 | he0
  · have h0 : ∫⁻ y, ‖w y‖ₑ = 0 := by
      refine le_antisymm ?_ bot_le
      rw [ENNReal.ofReal_of_nonpos he0] at hint
      exact hint
    rw [lintegral_eq_zero_iff hwm] at h0
    have hm2 : Measurable fun y => ENNReal.ofReal (gPlus d s c (x - y)) * ‖w y‖ₑ :=
      (ENNReal.measurable_ofReal.comp (hgm.comp (measurable_const.sub measurable_id))).mul hwm
    have : ∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y)) * ‖w y‖ₑ = 0 := by
      rw [lintegral_eq_zero_iff hm2]
      filter_upwards [h0] with y hy
      simp [hy]
    rw [this]; exact bot_le
  · set H : ℝ := Real.sqrt ((|M| + 1) / e) with hH
    have hH0 : 0 < H := Real.sqrt_pos.2 (by positivity)
    have hpt : ∀ y, ENNReal.ofReal (gPlus d s c (x - y)) * ‖w y‖ₑ ≤
        ENNReal.ofReal H * ‖w y‖ₑ + ENNReal.ofReal |M| *
          ENNReal.ofReal (gPlus d s c (x - y) - gTrunc d s c H (x - y)) := by
      intro y
      set a := gPlus d s c (x - y) with ha
      have ha0 : 0 ≤ a := hc _
      have hmin : gTrunc d s c H (x - y) = min a H := rfl
      have hsplit : ENNReal.ofReal a = ENNReal.ofReal (min a H) + ENNReal.ofReal (a - min a H) := by
        rw [← ENNReal.ofReal_add (le_min ha0 hH0.le) (sub_nonneg.2 (min_le_left _ _))]
        congr 1; ring
      rw [hmin, hsplit, add_mul]
      refine add_le_add ?_ ?_
      · exact mul_le_mul' (ENNReal.ofReal_le_ofReal (min_le_right _ _)) le_rfl
      · calc ENNReal.ofReal (a - min a H) * ‖w y‖ₑ
            ≤ ENNReal.ofReal (a - min a H) * ENNReal.ofReal |M| := mul_le_mul' le_rfl (hMb y)
          _ = _ := mul_comm _ _
    calc ∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y)) * ‖w y‖ₑ
        ≤ ∫⁻ y, (ENNReal.ofReal H * ‖w y‖ₑ + ENNReal.ofReal |M| *
          ENNReal.ofReal (gPlus d s c (x - y) - gTrunc d s c H (x - y))) := lintegral_mono hpt
      _ = ENNReal.ofReal H * (∫⁻ y, ‖w y‖ₑ) + ENNReal.ofReal |M| *
          (∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y) - gTrunc d s c H (x - y))) := by
        rw [lintegral_add_left (hwm.const_mul _), lintegral_const_mul _ hwm,
          lintegral_const_mul]
        refine ENNReal.measurable_ofReal.comp ?_
        exact (hgm.comp (measurable_const.sub measurable_id)).sub
          (((hgm.comp (measurable_const.sub measurable_id))).min measurable_const)
      _ ≤ ENNReal.ofReal H * ENNReal.ofReal e + ENNReal.ofReal |M| * ENNReal.ofReal (C2 / H) := by
        refine add_le_add (mul_le_mul' le_rfl hint) (mul_le_mul' le_rfl ?_)
        rw [lintegral_sub_left_torus (fun z => ENNReal.ofReal (gPlus d s c z - gTrunc d s c H z)) x]
        exact h2 H hH0
      _ = ENNReal.ofReal (H * e + |M| * (C2 / H)) := by
        rw [← ENNReal.ofReal_mul hH0.le, ← ENNReal.ofReal_mul (abs_nonneg M),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
      _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [mul_assoc]
        exact small_arith |M| C2 e (abs_nonneg M) hC2 he0 |>.trans (by rw [mul_assoc])


theorem ennreal_le_of_sq_le (X A : ℝ≥0∞) (h : X ^ 2 ≤ A ^ 2) : X ≤ A := by
  by_contra hc
  push Not at hc
  exact absurd h (not_le.2 (ENNReal.pow_lt_pow_left (by norm_num) hc))

theorem lintegral_mul_sq_le {α : Type*} [MeasurableSpace α] (ν : Measure α) (P Q : α → ℝ≥0∞)
    (hP : AEMeasurable P ν) (hQ : AEMeasurable Q ν) :
    (∫⁻ x, P x * Q x ∂ν) ^ 2 ≤ (∫⁻ x, P x ^ 2 ∂ν) * ∫⁻ x, Q x ^ 2 ∂ν := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν (Real.HolderConjugate.two_two) hP hQ
  simp only [Pi.mul_apply] at h
  have h2 : (∫⁻ x, P x * Q x ∂ν) ^ 2 ≤
      ((∫⁻ x, P x ^ (2:ℝ) ∂ν) ^ (1 / (2:ℝ)) * (∫⁻ x, Q x ^ (2:ℝ) ∂ν) ^ (1 / (2:ℝ))) ^ 2 :=
    pow_le_pow_left' h 2
  have e1 : ∀ X : ℝ≥0∞, (X ^ (1 / (2:ℝ))) ^ 2 = X := by
    intro X
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  rw [mul_pow, e1, e1] at h2
  simpa [ENNReal.rpow_two] using h2

theorem rpow_two_thirds_split (X : ℝ≥0∞) : X ^ (2 / 3 : ℝ) * X ^ (1 / 3 : ℝ) = X := by
  rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]; norm_num

theorem rpow_third_sq (X : ℝ≥0∞) : (X ^ (1 / 3 : ℝ)) ^ 2 = X ^ (2 / 3 : ℝ) := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

theorem young_sq (a : Torus d → ℝ≥0∞) (ha : Measurable a)
    (hA : ∫⁻ z, (a z ^ (2 / 3 : ℝ)) ^ 2 ≠ ∞) :
    ∫⁻ u, (∫⁻ w, a w * a (u - w)) ^ 2 ≤ (∫⁻ z, (a z ^ (2 / 3 : ℝ)) ^ 2) ^ 3 := by
  set A := ∫⁻ z, (a z ^ (2 / 3 : ℝ)) ^ 2 with hAdef
  set c0 : Torus d → ℝ≥0∞ := fun z => a z ^ (2 / 3 : ℝ) with hc0
  set e0 : Torus d → ℝ≥0∞ := fun z => a z ^ (1 / 3 : ℝ) with he0
  have hc0m : Measurable c0 := ha.pow_const _
  have he0m : Measurable e0 := ha.pow_const _
  have hshift : ∀ u, ∫⁻ w, (c0 (u - w)) ^ 2 = A := fun u => lintegral_sub_left_torus (fun z => c0 z ^ 2) u
  have hpt : ∀ u, (∫⁻ w, a w * a (u - w)) ^ 2 ≤ A * ∫⁻ w, c0 w ^ 2 * c0 (u - w) ^ 2 := by
    intro u
    have hfac : ∀ w, a w * a (u - w) = (c0 w * c0 (u - w)) * (e0 w * e0 (u - w)) := by
      intro w
      have h1 : a w = c0 w * e0 w := (rpow_two_thirds_split (a w)).symm
      have h2 : a (u - w) = c0 (u - w) * e0 (u - w) := (rpow_two_thirds_split (a (u - w))).symm
      rw [h1, h2]; ring
    have hP : Measurable fun w => c0 w * c0 (u - w) :=
      hc0m.mul (hc0m.comp (measurable_const.sub measurable_id))
    have hQ : Measurable fun w => e0 w * e0 (u - w) :=
      he0m.mul (he0m.comp (measurable_const.sub measurable_id))
    have step1 := lintegral_mul_sq_le (volume : Measure (Torus d)) _ _ hP.aemeasurable hQ.aemeasurable
    have hQ2 : ∫⁻ w, (e0 w * e0 (u - w)) ^ 2 ≤ A := by
      have : ∀ w, (e0 w * e0 (u - w)) ^ 2 = c0 w * c0 (u - w) := by
        intro w
        rw [mul_pow, he0, hc0]; simp only; rw [rpow_third_sq, rpow_third_sq]
      simp_rw [this]
      have step2 := lintegral_mul_sq_le (volume : Measure (Torus d)) (fun w => c0 w)
        (fun w => c0 (u - w)) hc0m.aemeasurable
        (hc0m.comp (measurable_const.sub measurable_id)).aemeasurable
      rw [hshift u] at step2
      exact ennreal_le_of_sq_le _ _ (step2.trans (by rw [sq]))
    have hl : ∫⁻ w, a w * a (u - w) = ∫⁻ w, (c0 w * c0 (u - w)) * (e0 w * e0 (u - w)) :=
      lintegral_congr hfac
    have hP2 : ∫⁻ w, (c0 w * c0 (u - w)) ^ 2 = ∫⁻ w, c0 w ^ 2 * c0 (u - w) ^ 2 :=
      lintegral_congr fun w => mul_pow _ _ _
    rw [hl]
    calc _ ≤ (∫⁻ w, (c0 w * c0 (u - w)) ^ 2) * ∫⁻ w, (e0 w * e0 (u - w)) ^ 2 := step1
      _ ≤ (∫⁻ w, (c0 w * c0 (u - w)) ^ 2) * A := mul_le_mul' le_rfl hQ2
      _ = _ := by rw [hP2, mul_comm]
  calc ∫⁻ u, (∫⁻ w, a w * a (u - w)) ^ 2
      ≤ ∫⁻ u, A * ∫⁻ w, c0 w ^ 2 * c0 (u - w) ^ 2 := lintegral_mono hpt
    _ = A * ∫⁻ u, ∫⁻ w, c0 w ^ 2 * c0 (u - w) ^ 2 := lintegral_const_mul' _ _ hA
    _ = A * ∫⁻ w, ∫⁻ u, c0 w ^ 2 * c0 (u - w) ^ 2 := by
        congr 1
        refine lintegral_lintegral_swap (f := fun u w => c0 w ^ 2 * c0 (u - w) ^ 2) ?_
        exact ((hc0m.comp measurable_snd).pow_const 2 |>.mul
          ((hc0m.comp (measurable_fst.sub measurable_snd)).pow_const 2)).aemeasurable
    _ = A * ∫⁻ w, c0 w ^ 2 * A := by
        congr 1
        refine lintegral_congr fun w => ?_
        rw [lintegral_const_mul (f := fun u => c0 (u - w) ^ 2) _
          ((hc0m.comp (measurable_id.sub measurable_const)).pow_const 2)]
        congr 1
        exact lintegral_sub_right_eq_self (fun z => c0 z ^ 2) w
    _ = A * (A * A) := by
        congr 1
        rw [lintegral_mul_const _ (hc0m.pow_const 2)]
    _ = A ^ 3 := by ring


theorem A_finite (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∫⁻ z, ((ENNReal.ofReal (gPlus d s c z)) ^ (2 / 3 : ℝ)) ^ 2 ≠ ∞ := by
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hs0' : 0 < s := by rw [hcrit]; positivity
  obtain ⟨A0, hA01, hA0⟩ := gPlus_envelope hd hs0' hsd c
  have hα : 2 * (d : ℝ) / 3 < d := by linarith
  have hI : IntegrableOn (fun y : Fin d → ℝ => A0 ^ (4 / 3 : ℝ) * ‖y‖ ^ (-(2 * (d : ℝ) / 3))) (Box d) :=
    (integrableOn_Box_rpow hd0 hα).const_mul _
  rw [lintegral_torus_box (fun z => ((ENNReal.ofReal (gPlus d s c z)) ^ (2 / 3 : ℝ)) ^ 2)]
  have hne : ∀ᵐ y ∂(volume.restrict (Box d)), y ≠ 0 := ae_restrict_of_ae (ae_ne_pi hd0)
  refine ne_of_lt (lt_of_le_of_lt ?_ (hI.lintegral_lt_top (f := fun y : Fin d → ℝ => A0 ^ (4 / 3 : ℝ) * ‖y‖ ^ (-(2 * (d : ℝ) / 3)))))
  refine lintegral_mono_ae ?_
  filter_upwards [hne, ae_restrict_mem (measurableSet_Box d)] with y hy hyB
  have hypos : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hg0 : 0 ≤ gPlus d s c (boxPt y) := hc _
  have hgle := hA0 y hyB hy
  rw [ENNReal.ofReal_rpow_of_nonneg hg0 (by norm_num), ← ENNReal.ofReal_pow (Real.rpow_nonneg hg0 _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hA0pos : 0 < A0 := by linarith
  have h1 : gPlus d s c (boxPt y) ^ (2 / 3 : ℝ) ≤ (A0 * ‖y‖ ^ (-s)) ^ (2 / 3 : ℝ) :=
    Real.rpow_le_rpow hg0 hgle (by norm_num)
  calc (gPlus d s c (boxPt y) ^ (2 / 3 : ℝ)) ^ 2 ≤ ((A0 * ‖y‖ ^ (-s)) ^ (2 / 3 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (Real.rpow_nonneg hg0 _) h1 2
    _ = A0 ^ (4 / 3 : ℝ) * ‖y‖ ^ (-(2 * (d : ℝ) / 3)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Real.mul_rpow hA0pos.le
          (Real.rpow_nonneg hypos.le _), ← Real.rpow_mul hypos.le]
        congr 2
        · push_cast; norm_num
        · rw [hcrit]; push_cast; ring


theorem lintegral_mu_le_vol {ρ : Torus d → ℝ} {Λ : ℝ} (hΛ : ∀ x, ρ x ≤ Λ) (F : Torus d → ℝ≥0∞) :
    ∫⁻ y, F y ∂(withDensityReal ρ) ≤ ENNReal.ofReal Λ * ∫⁻ y, F y := by
  calc _ ≤ ∫⁻ y, F y ∂(ENNReal.ofReal Λ • (volume : Measure (Torus d))) :=
        lintegral_mono' (withDensityReal_le ρ Λ hΛ) le_rfl
    _ = _ := by rw [lintegral_smul_measure, smul_eq_mul]

theorem conj_last (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (β : ℝ) (hβ : 0 < β) (ρ : Torus d → ℝ)
    (hρ : SmoothPosDensity ρ) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∫⁻ z, (∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y) *
            Real.exp (-(t * (β / N)) * gPlus d s c (x - y)) * gPlus d s c (y - z))
            ∂(withDensityReal ρ)) ^ 2 ∂(withDensityReal ρ) ≤ ENNReal.ofReal C := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_density_bound hρ
  have hgm := measurable_gPlus hd hs0 hsd c
  set a : Torus d → ℝ≥0∞ := fun z => ENNReal.ofReal (gPlus d s c z) with ha
  have ham : Measurable a := ENNReal.measurable_ofReal.comp hgm
  set Ab := ∫⁻ z, (a z ^ (2 / 3 : ℝ)) ^ 2 with hAb
  have hAbfin : Ab ≠ ∞ := A_finite hd hcrit c hc
  set B : ℝ≥0∞ := ENNReal.ofReal Λ ^ 3 * Ab ^ 3 with hB
  have hBfin : B ≠ ∞ := ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    (ENNReal.pow_ne_top hAbfin)
  refine ⟨B.toReal, fun N hN x t ht => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  -- pointwise reduction
  have hpt : ∀ z y, ENNReal.ofReal (gPlus d s c (x - y) *
      Real.exp (-(t * (β / N)) * gPlus d s c (x - y)) * gPlus d s c (y - z)) ≤
        a (x - y) * a (y - z) := by
    intro z y
    have h0 := hc (x - y)
    have h0' := hc (y - z)
    have hg1 : 0 ≤ gPlus d s c (x - y) := h0
    have hg2 : 0 ≤ gPlus d s c (y - z) := h0'
    have hE : Real.exp (-(t * (β / N)) * gPlus d s c (x - y)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ t * (β / N) := by have := ht.1; positivity
      nlinarith
    simp only [ha]
    rw [← ENNReal.ofReal_mul hg1]
    refine ENNReal.ofReal_le_ofReal ?_
    have hE0 := (Real.exp_pos (-(t * (β / N)) * gPlus d s c (x - y))).le
    calc gPlus d s c (x - y) * Real.exp (-(t * (β / N)) * gPlus d s c (x - y)) *
          gPlus d s c (y - z) ≤ gPlus d s c (x - y) * 1 * gPlus d s c (y - z) := by gcongr
      _ = _ := by ring
  set K : Torus d → ℝ≥0∞ := fun u => ∫⁻ w, a w * a (u - w) with hK
  have hJ : ∀ z, ∫⁻ y, a (x - y) * a (y - z) = K (x - z) := by
    intro z
    have := lintegral_sub_left_torus (fun w => a w * a (x - z - w)) x
    simp only [hK]
    rw [← this]
    refine lintegral_congr fun y => ?_
    show a (x - y) * a (y - z) = a (x - y) * a (x - z - (x - y))
    congr 2
    abel
  have hKm : Measurable K := by
    refine Measurable.lintegral_prod_right' (f := fun p : Torus d × Torus d => a p.2 * a (p.1 - p.2)) ?_
    exact (ham.comp measurable_snd).mul (ham.comp (measurable_fst.sub measurable_snd))
  have hKint : ∫⁻ u, K u ^ 2 ≤ Ab ^ 3 := young_sq a ham hAbfin
  calc ∫⁻ z, (∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y) *
            Real.exp (-(t * (β / N)) * gPlus d s c (x - y)) * gPlus d s c (y - z))
            ∂(withDensityReal ρ)) ^ 2 ∂(withDensityReal ρ)
      ≤ ∫⁻ z, (ENNReal.ofReal Λ * K (x - z)) ^ 2 ∂(withDensityReal ρ) := by
        refine lintegral_mono fun z => ?_
        refine pow_le_pow_left' ?_ 2
        calc _ ≤ ∫⁻ y, a (x - y) * a (y - z) ∂(withDensityReal ρ) :=
              lintegral_mono fun y => hpt z y
          _ ≤ ENNReal.ofReal Λ * ∫⁻ y, a (x - y) * a (y - z) :=
              lintegral_mu_le_vol hΛ (fun y => a (x - y) * a (y - z))
          _ = _ := by rw [hJ z]
    _ ≤ ENNReal.ofReal Λ * ∫⁻ z, (ENNReal.ofReal Λ * K (x - z)) ^ 2 :=
        lintegral_mu_le_vol hΛ (fun z => (ENNReal.ofReal Λ * K (x - z)) ^ 2)
    _ = ENNReal.ofReal Λ * (ENNReal.ofReal Λ ^ 2 * ∫⁻ z, K (x - z) ^ 2) := by
        congr 1
        rw [← lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
        simp_rw [mul_pow]
    _ = ENNReal.ofReal Λ ^ 3 * ∫⁻ u, K u ^ 2 := by
        rw [lintegral_sub_left_torus (fun u => K u ^ 2) x]; ring
    _ ≤ B := by
        calc _ ≤ ENNReal.ofReal Λ ^ 3 * Ab ^ 3 := mul_le_mul' le_rfl hKint
          _ = B := rfl
    _ = ENNReal.ofReal B.toReal := (ENNReal.ofReal_toReal hBfin).symm


end PoleCavityAux

/-! ### The critical exponent `s = d/2` (Lemmas 4.4-4.7, Propositions 4.8-4.9) -/

section Critical

variable {s : ℝ}

/-- Lemma 4.4 `M:R:lem:product-transfer` (source lines 4194-4200), `R:eq:product-transfer`:
for every `ε > 0` there is an integer `q ≥ 2` with `‖Y‖_{L²(P)} ≤ C_ε N^ε ‖Y‖_{L^{2q}(μ^{⊗ℓ})}`
for `P` the full law `Q_{N,β}(μ)` or any pole law `P_n^{x,t}` (`t = 0` is the cavity),
uniformly in the pole (`ε` real; an earlier version let `ε` elaborate in `ℕ`). Coordinate projections are included: a function of a subset of the
coordinates has the same `L^{2q}` norm under `μ^{⊗ℓ}` and under the full product measure. -/
theorem product_moment_transfer (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∀ ε : ℝ, 0 < ε → ∃ q : ℕ, 2 ≤ q ∧ ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      (∀ Y : Config d N → ℝ, Measurable Y →
        eLpNorm Y 2 (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
          ENNReal.ofReal (C * (N : ℝ) ^ ε) *
            eLpNorm Y ((2 * q : ℕ) : ℝ≥0∞) (Measure.pi fun _ : Fin N => withDensityReal ρ)) ∧
      (∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ Y : Config d (N - 1) → ℝ, Measurable Y →
        eLpNorm Y 2 (critPole d s c β ρ N x t) ≤
          ENNReal.ofReal (C * (N : ℝ) ^ ε) *
            eLpNorm Y ((2 * q : ℕ) : ℝ≥0∞)
              (Measure.pi fun _ : Fin (N - 1) => withDensityReal ρ)) := by
  sorry

/-- Lemma 4.5 `M:R:lem:integrals` (source lines 4210-4228): the radial bounds
`R:eq:radial-bounds`, `R:eq:radial-higher`, the `L²(μ)` boundedness of the operator with kernel
`g_+` (stated in the stronger Schur form for `|f|`), `R:eq:convolution-small` (stated for
`|w|`, which is what the proof gives; `w` a density with respect to `dx`), `R:eq:square-log`
and `R:eq:double-convolution`. All integrands are nonnegative; integrals are `lintegral`s. -/
theorem critical_integrals (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∃ C : ℝ,
      (∀ H : ℝ, 2 ≤ H → ∀ x : Torus d,
        ∫⁻ y, ENNReal.ofReal (gTrunc d s c H (x - y) ^ 2) ∂(withDensityReal ρ) ≤
            ENNReal.ofReal (C * Real.log H) ∧
          ∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y) - gTrunc d s c H (x - y))
              ∂(withDensityReal ρ) ≤ ENNReal.ofReal (C / H)) ∧
      (∀ v : ℝ, 2 < v → ∃ Cv : ℝ, ∀ H : ℝ, 2 ≤ H → ∀ x : Torus d,
        ∫⁻ y, ENNReal.ofReal (gTrunc d s c H (x - y) ^ v) ∂(withDensityReal ρ) ≤
          ENNReal.ofReal (Cv * H ^ (v - 2))) ∧
      (∀ f : Torus d → ℝ, Measurable f →
        ∫⁻ x, (∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y)) * ‖f y‖ₑ ∂(withDensityReal ρ)) ^ 2
            ∂(withDensityReal ρ) ≤
          ENNReal.ofReal C * ∫⁻ y, ‖f y‖ₑ ^ 2 ∂(withDensityReal ρ)) ∧
      (∀ M : ℝ, ∃ CM : ℝ, ∀ (w : Torus d → ℝ) (e : ℝ), Measurable w → (∀ y, |w y| ≤ M) →
        e ≤ 1 → ∫⁻ y, ‖w y‖ₑ ≤ ENNReal.ofReal e → ∀ x : Torus d,
          ∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y)) * ‖w y‖ₑ ≤
            ENNReal.ofReal (CM * Real.sqrt e)) ∧
      (∀ u : ℝ, 0 < u → u ≤ 1 → ∀ x : Torus d,
        ∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y) ^ 2 * Real.exp (-u * gPlus d s c (x - y)))
            ∂(withDensityReal ρ) ≤ ENNReal.ofReal (C * (1 + |Real.log u|))) ∧
      (∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∫⁻ z, (∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y) *
              Real.exp (-(t * (β / N)) * gPlus d s c (x - y)) * gPlus d s c (y - z))
              ∂(withDensityReal ρ)) ^ 2 ∂(withDensityReal ρ) ≤ ENNReal.ofReal C) := by
  obtain ⟨C1, hC1, h1⟩ := PoleCavityAux.conj_trunc hd hcrit c hc ρ hρ
  obtain ⟨C3, hC3, h3⟩ := PoleCavityAux.conj_schur hd hcrit c hc ρ hρ
  obtain ⟨C5, hC5, h5⟩ := PoleCavityAux.conj_expo hd hcrit c hc ρ hρ
  obtain ⟨C6, h6⟩ := PoleCavityAux.conj_last hd hcrit c hc β hβ ρ hρ
  refine ⟨max (max C1 C3) (max C5 C6), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro H hH x
    have hlog : 0 ≤ Real.log H := Real.log_nonneg (by linarith)
    have hH0 : 0 < H := by linarith
    have hm : C1 ≤ max (max C1 C3) (max C5 C6) := (le_max_left _ _).trans (le_max_left _ _)
    refine ⟨(h1 H hH x).1.trans (ENNReal.ofReal_le_ofReal ?_),
      (h1 H hH x).2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    · exact mul_le_mul_of_nonneg_right hm hlog
    · exact div_le_div_of_nonneg_right hm hH0.le
  · intro v hv
    obtain ⟨Cv, hCv, hv'⟩ := PoleCavityAux.conj_pow hd hcrit c hc ρ hρ v hv
    exact ⟨Cv, hv'⟩
  · intro f hf
    refine (h3 f hf).trans ?_
    gcongr
    exact (le_max_right C1 C3).trans (le_max_left _ _)
  · intro M
    obtain ⟨CM, hCM⟩ := PoleCavityAux.conj_small hd hcrit c hc M
    exact ⟨CM, hCM⟩
  · intro u hu hu1 x
    refine (h5 u hu hu1 x).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right ((le_max_left C5 C6).trans (le_max_right _ _))
      (by positivity)
  · intro N hN x t ht
    exact (h6 N hN x t ht).trans (ENNReal.ofReal_le_ofReal
      ((le_max_right C5 C6).trans (le_max_right _ _)))

/-- Lemma 4.6 `M:R:lem:cavity` (source lines 4246-4264): with `m_N = Q_{N,β}(μ)^{(1)}`,
`ν_n = (P_n^0)^{(1)}`, `z_N = dm_N/dμ - 1`,
* `R:eq:D-integral`: `F_{N,x}` has right derivative `-λ E_{P_n^0}[∑_i g_+(x-y_i)]` at `0`,
  `0 ≤ D_N(x) = ∫_0^1 (1-t) λ² Var_{P_n^{x,t}}[∑_i g_+(x - y_i)] dt ≤ C δ_N`;
* `R:eq:cavity-L2`: `‖(m_N - ν_n)/μ‖_{L²(μ)} ≤ C √(log N)/N`;
* `R:eq:response`: `‖(I + βK_μ) z_N - P_μ D_N‖_{L²(μ)} ≤ C √(log N)/N`;
* `R:eq:prefactor`: `d(P_n^{x,t})^{(1)}/dμ (y) = e^{-tλ g_+(x-y)}(1 + O(√δ_N))` essentially
  uniformly, and `‖z_N‖_∞ ≤ C √δ_N`. -/
theorem cavity_response (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      (∀ x : Torus d,
        Integrable (fun Y : Config d (N - 1) => ∑ i, gPlus d s c (x - Y i))
            (critCavity d s c β ρ N) ∧
          HasDerivWithinAt (insertionPressure d s c β ρ N x)
            (-((β / N) * ∫ Y, ∑ i, gPlus d s c (x - Y i) ∂(critCavity d s c β ρ N)))
            (Set.Ici 0) 0 ∧
          0 ≤ insertionDefect d s c β ρ N x ∧
          ENNReal.ofReal (insertionDefect d s c β ρ N x) =
            ∫⁻ t in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal ((1 - t) * (β / N) ^ 2) *
              evariance (fun Y : Config d (N - 1) => ∑ i, gPlus d s c (x - Y i))
                (critPole d s c β ρ N x t) ∧
          insertionDefect d s c β ρ N x ≤ C * deltaN d s N) ∧
      (firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≪
          withDensityReal ρ ∧
        firstMarginal (critCavity d s c β ρ N) ≪ withDensityReal ρ ∧
        eLpNorm (fun y =>
            ((firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))).rnDeriv
                (withDensityReal ρ) y).toReal -
              ((firstMarginal (critCavity d s c β ρ N)).rnDeriv (withDensityReal ρ) y).toReal)
            2 (withDensityReal ρ) ≤
          ENNReal.ofReal (C * Real.sqrt (Real.log N) / N)) ∧
      eLpNorm (fun y =>
          (((firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))).rnDeriv
              (withDensityReal ρ) y).toReal - 1) +
            β * Kop (periodicRiesz d s) (withDensityReal ρ)
              (fun y' => ((firstMarginal (modulatedGibbs (periodicRiesz d s) N β
                (withDensityReal ρ))).rnDeriv (withDensityReal ρ) y').toReal - 1) y -
            projMean (withDensityReal ρ) (insertionDefect d s c β ρ N) y)
          2 (withDensityReal ρ) ≤
        ENNReal.ofReal (C * Real.sqrt (Real.log N) / N) ∧
      (∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        firstMarginal (critPole d s c β ρ N x t) ≪ withDensityReal ρ ∧
          ∀ᵐ y ∂(withDensityReal ρ),
            |((firstMarginal (critPole d s c β ρ N x t)).rnDeriv (withDensityReal ρ) y).toReal -
                Real.exp (-(t * (β / N)) * gPlus d s c (x - y))| ≤
              C * Real.sqrt (deltaN d s N) * Real.exp (-(t * (β / N)) * gPlus d s c (x - y))) ∧
      (∀ᵐ y ∂(withDensityReal ρ),
        |((firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))).rnDeriv
            (withDensityReal ρ) y).toReal - 1| ≤ C * Real.sqrt (deltaN d s N)) := by
  sorry

/-- Lemma 4.7 `M:R:lem:Taylor` (source lines 4299-4306), `R:eq:Taylor-remainder`: for
`f = 1`, `f = e^{-tλ g_+(x-·)}` (the test `1` multiplied by the pole factor) and
`f = g_+(x-·) e^{-tλ g_+(x-·)}`, and `Y` distributed by any pole law `P_n^{x,t'}` (`t' = 0` is
the cavity) through the coordinates other than `i`,
`‖∫ f(y) H(v_Y(y)) dμ(y)‖_{L²(P)} ≤ C N^{-9/16}` (stated squared; `f H(v_Y) ≥ 0`). -/
theorem integrated_taylor_remainder (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ)
    (hβ : 0 < β) (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ t' ∈ Set.Icc (0 : ℝ) 1, ∀ i : Fin (N - 1),
      ∀ f ∈ ({fun _ => 1,
          fun y => Real.exp (-(t * (β / N)) * gPlus d s c (x - y)),
          fun y => gPlus d s c (x - y) * Real.exp (-(t * (β / N)) * gPlus d s c (x - y))} :
            Set (Torus d → ℝ)),
        ∫⁻ Y, (∫⁻ y, ENNReal.ofReal (f y * taylorH (cavityField d s c β ρ N i Y y))
              ∂(withDensityReal ρ)) ^ 2 ∂(critPole d s c β ρ N x t') ≤
          ENNReal.ofReal (C * (N : ℝ) ^ (-(9 / 8 : ℝ))) := by
  sorry

/-- Proposition 4.8 `M:R:prop:conditional-expectation` (source lines 4354-4366),
`R:eq:conditional-variance`: for `0 < t ≤ 1`, under `P_n^{x,t}`, with
`T_1 = E[g_+(x - y_i) | (y_j)_{j≠i}]`, `B_t = ∫ e^{-tλ g_+(x-y)} dμ`,
`F_t = ∫ g_+(x-y) e^{-tλ g_+(x-y)} dμ`:
`‖T_1 - F_t/B_t‖_{L²} ≤ C N^{-1/2}`, `Var(T_1) ≤ C/N`, `E[T_1²] ≤ C`, uniformly in `x, t, N`.
The integrability conjunct rules out the junk value of `condExp`. -/
theorem conditional_singular_observation (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ)
    (hβ : 0 < β) (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ i : Fin (N - 1),
      Integrable (fun Y : Config d (N - 1) => gPlus d s c (x - Y i)) (critPole d s c β ρ N x t) ∧
      eLpNorm (fun Y =>
          (critPole d s c β ρ N x t)[fun Y' => gPlus d s c (x - Y' i) | othersSigma i] Y -
            (∫ y, gPlus d s c (x - y) * Real.exp (-(t * (β / N)) * gPlus d s c (x - y))
                ∂(withDensityReal ρ)) /
              (∫ y, Real.exp (-(t * (β / N)) * gPlus d s c (x - y)) ∂(withDensityReal ρ)))
          2 (critPole d s c β ρ N x t) ≤ ENNReal.ofReal (C * (N : ℝ) ^ (-(1 / 2 : ℝ))) ∧
      evariance ((critPole d s c β ρ N x t)[fun Y' => gPlus d s c (x - Y' i) | othersSigma i])
          (critPole d s c β ρ N x t) ≤ ENNReal.ofReal (C / N) ∧
      ∫⁻ Y, ‖(critPole d s c β ρ N x t)[fun Y' => gPlus d s c (x - Y' i) | othersSigma i] Y‖ₑ ^ 2
          ∂(critPole d s c β ρ N x t) ≤ ENNReal.ofReal C := by
  sorry

/-- Proposition 4.9 `M:R:prop:insertion-coefficient` (source lines 4389-4394),
`R:eq:D-coefficient`: uniformly in `x`,
`|D_N(x) - (β²|𝕊^{d-1}|/d) ρ(x) δ_N| ≤ C √(log N)/N`, `δ_N = log(eN)/N`. -/
theorem insertion_coefficient (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d,
      |insertionDefect d s c β ρ N x - β ^ 2 * sphereArea d / d * ρ x * deltaN d s N| ≤
        C * Real.sqrt (Real.log N) / N := by
  sorry

end Critical

end HRS

end
