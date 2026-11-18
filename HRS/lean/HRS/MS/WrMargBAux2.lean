import HRS.MS.WrMargBAux1

/-!
# HRS.MS.WrMargBAux2 -- full-law marginal `dπ_N/dμ`: `L²` rate and the packaged bound (WR-13d, part 2)

Packet WR-13d (T10 of `docs/WR_B_PLAN.md`: `euc-convolution-L2`, `euc-cavity-equation`, `euc-absorption`),
namespace `HRS.MS.Wr`, helper prefix `wr13d_`.  Euclidean port of `HRS/Equilibrium/MarginalDensity.lean`
(`L2_all`, `firstMarginal_density_L2`) with the uniform-in-`ρ ≤ M` quantifier structure of the Euclidean packets.

Main theorems:
* `wr13d_core_L2`: for `N = n+1 ≥ N₁`, `β ∈ [βm, βp]`, `ρ ≤ M`: `‖θ_N - 1‖_{L²(μ)} ≤ C δ_N`, `θ_N = dπ_N/dμ`.
  Proof: exact cavity equation `log θ + β g*(θ-1) = D_N + β g*(π_N - ν_n) + λ g*ν_n - log Z`
  (`wr13d_log_theta`), `0 ≤ D_N ≤ C δ_N` (`wr13c2_insDefect_le`), `‖g*(π_N-ν_n)‖_{L²(μ)} ≤ C δ_N` from the cavity total
  variation `C√(δ_N/N)` and `wr13c_conv_L2_delta`, `0 ≤ g*ν_n ≤ C M_g`, `K_μ ≥ 0` (`wr13c_Kmu_nonneg`) and the
  absorption `wr13e_absorption` (positivity `(θ-1) log θ ≥ (θ-1)²/C` for `0 < θ ≤ C`: no smallness of `‖z_N‖_∞`
  is needed in the `L²` estimate).
* `wr13d_marginal_density_bounds` (`HasMarginalDensityBounds`, conjunct 3 of `euc_static`): for all `N ≥ 2`,
  `HasMarginalDensityBounds π_N μ C (C δ_N)` with `C` quantified before `ρ, β ∈ [βm, βp], N`; small `N` by the
  pointwise bound `θ ≤ e^{2βp|M_g|}` and `δ_N ≥ 1/N`.

* `wr13d_theta_uniform`: `‖θ_N - 1‖_∞ → 0` uniformly in `ρ ≤ M`, `β ∈ [βm, βp]` (unsimplified cavity equation,
  `‖π_N - μ‖_TV ≤ √(β C N^{s/d-1}/2)` of `euc_tv_Q_le` (WR-12a), cavity TV `K √(δ_N/N)`, and the sup bound
  `wr13d_cv_sup`; the normalisation `∫ θ = 1` controls `log Z`).

Adjustments with respect to the sketch of `docs/WR_B_PLAN.md` (all harmless): the intermediate statement
`‖π_N - μ‖_TV ≤ C N^{(s/d-1)/2}` is `euc_tv_Q_le` (already merged, not restated); the `L²` estimate does not use
`‖z_N‖_∞ → 0` (the positivity form of absorption suffices), so `wr13d_theta_uniform` is an independent output; the
sup bound `dπ_N/dμ ≤ C` is pointwise (`wr13d_theta_le`), not only almost everywhere.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wr

open HRS.Whole (rieszKernel EucConfig potentialBound)
open HRS.External

variable {d : ℕ} {s : ℝ}

/-! ### 1. Elementary `L²` facts -/

theorem wr13d_sqrt_eq {μ : Measure (Euc d)} {F : Euc d → ℝ} (hF : MemLp F 2 μ) :
    Real.sqrt (∫ x, F x ^ 2 ∂μ) = (eLpNorm F 2 μ).toReal := by
  have hsq := RefMarg.integral_mul_self_eq hF
  rw [← Real.sqrt_sq ENNReal.toReal_nonneg, ← hsq]
  congr 2; funext x; ring

theorem wr13d_eLpNorm_le_of_sqrt {μ : Measure (Euc d)} {F : Euc d → ℝ} (hF : MemLp F 2 μ) {r : ℝ}
    (h : Real.sqrt (∫ x, F x ^ 2 ∂μ) ≤ r) : eLpNorm F 2 μ ≤ ENNReal.ofReal r := by
  have hfin : eLpNorm F 2 μ ≠ ⊤ := hF.eLpNorm_ne_top
  rw [← ENNReal.ofReal_toReal hfin]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← wr13d_sqrt_eq hF]
  exact h

theorem wr13d_sqrt_le_of_eLpNorm {μ : Measure (Euc d)} {F : Euc d → ℝ} (hF : MemLp F 2 μ) {r : ℝ}
    (hr : 0 ≤ r) (h : eLpNorm F 2 μ ≤ ENNReal.ofReal r) : Real.sqrt (∫ x, F x ^ 2 ∂μ) ≤ r := by
  rw [wr13d_sqrt_eq hF]
  exact ENNReal.toReal_le_of_le_ofReal hr h

/-! ### 2. The convolution term `g*θ - g*ν` -/

section CvBound

/-- **Density decomposition of `g*θ - g*ν`**: for `0 < θ ≤ Cν` and a probability measure `ν ≤ Cν μ` at event
distance `≤ ε` from `θ μ`, there is a bounded integrable Lebesgue density `w = ρ (θ - θ')` with
`∫|w| ≤ 2ε` and `g*θ(x) - g*ν(x) = ∫ g(x-y) w(y) dy` for every `x` (integrals of the first two terms against
`μ`, `ν`; all integrals converge since `g*μ ≤ M_g`). -/
theorem wr13d_cv_prep (hd : 1 ≤ d) (hs : 0 < s) (hsd : s < d) (M : ℝ) {Cν : ℝ} (hCν1 : 1 ≤ Cν)
    {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) (hM : ∀ x, ρ x ≤ M)
    {θ : Euc d → ℝ} (hθm : Measurable θ) (hθ0 : ∀ x, 0 < θ x) (hθC : ∀ x, θ x ≤ Cν)
    {ν : Measure (Euc d)} (hνp : IsProbabilityMeasure ν)
    (hνle : ν ≤ ENNReal.ofReal Cν • HRS.Whole.withDensityReal ρ) {ε : ℝ}
    (hTV : ∀ A : Set (Euc d), MeasurableSet A →
      |((HRS.Whole.withDensityReal ρ).withDensity (fun y => ENNReal.ofReal (θ y))).real A - ν.real A| ≤ ε) :
    ∃ w : Euc d → ℝ, Measurable w ∧ (∀ y, |w y| ≤ max M 0 * Cν) ∧ Integrable w ∧
      ∫ y, |w y| ≤ 2 * ε ∧
      ∀ x, (∫ y, rieszKernel d s (x - y) * θ y ∂(HRS.Whole.withDensityReal ρ)) -
        ∫ y, rieszKernel d s (x - y) ∂ν = ∫ y, rieszKernel d s (x - y) * w y := by
  have hCν0 : 0 ≤ Cν := by linarith
  haveI hμp := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  have hM'ρ : ∀ x, ρ x ≤ max M 0 := fun x => (hM x).trans (le_max_left _ _)
  have hM'0 : (0 : ℝ) ≤ max M 0 := le_max_right _ _
  have hint : ∀ x : Euc d, Integrable (fun y => rieszKernel d s (x - y)) (HRS.Whole.withDensityReal ρ) :=
    fun x => (wr13a_potential_bound hd hs hsd hρ hM x).1
  -- the density of `ν`
  haveI hνfin : IsFiniteMeasure ν := inferInstance
  haveI hlebd : ν.HaveLebesgueDecomposition (HRS.Whole.withDensityReal ρ) :=
    Measure.haveLebesgueDecomposition_of_sigmaFinite _ _
  have hνac : ν ≪ HRS.Whole.withDensityReal ρ := Measure.absolutelyContinuous_of_le_smul hνle
  have hν_rn := HRS.PoleCavityAux.rnDeriv_le_of_le_withDensity (HRS.Whole.withDensityReal ρ) ν
    (fun _ => ENNReal.ofReal Cν) (by rw [withDensity_const]; exact hνle)
  set θ' : Euc d → ℝ := fun y => (ν.rnDeriv (HRS.Whole.withDensityReal ρ) y).toReal with hθ'
  set θ'c : Euc d → ℝ := fun y => min (θ' y) Cν with hθ'c
  have hθ'm : Measurable θ' := (Measure.measurable_rnDeriv ν (HRS.Whole.withDensityReal ρ)).ennreal_toReal
  have hθ'cm : Measurable θ'c := hθ'm.min measurable_const
  have hθ'c0 : ∀ y, 0 ≤ θ'c y := fun y => le_min ENNReal.toReal_nonneg hCν0
  have hθ'cb : ∀ y, θ'c y ≤ Cν := fun y => min_le_right _ _
  have hνeq : ν = (HRS.Whole.withDensityReal ρ).withDensity (fun y => ENNReal.ofReal (θ'c y)) := by
    calc ν = (HRS.Whole.withDensityReal ρ).withDensity (ν.rnDeriv (HRS.Whole.withDensityReal ρ)) :=
          (Measure.withDensity_rnDeriv_eq ν (HRS.Whole.withDensityReal ρ) hνac).symm
      _ = _ := by
        refine withDensity_congr_ae ?_
        filter_upwards [Measure.rnDeriv_lt_top ν (HRS.Whole.withDensityReal ρ), hν_rn.2] with y h1 h2
        have h3 : (ν.rnDeriv (HRS.Whole.withDensityReal ρ) y).toReal ≤ Cν :=
          ENNReal.toReal_le_of_le_ofReal hCν0 h2
        simp only [hθ'c, hθ', min_eq_left h3, ENNReal.ofReal_toReal h1.ne]
  have hθi : Integrable θ (HRS.Whole.withDensityReal ρ) :=
    Integrable.of_bound hθm.aestronglyMeasurable Cν
      (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs, abs_of_pos (hθ0 y)]; exact hθC y)
  have hθ'ci : Integrable θ'c (HRS.Whole.withDensityReal ρ) :=
    Integrable.of_bound hθ'cm.aestronglyMeasurable Cν
      (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (hθ'c0 y)]; exact hθ'cb y)
  have hTVL1 : ∫ y, |θ y - θ'c y| ∂(HRS.Whole.withDensityReal ρ) ≤ 2 * ε := by
    refine RefMarg.integral_abs_sub_le hθm hθ'cm (fun y => (hθ0 y).le) hθ'c0 hθi hθ'ci (fun A hA => ?_)
    rw [← hνeq]
    exact hTV A hA
  -- the Lebesgue density `w = ρ (θ - θ')`
  set w : Euc d → ℝ := fun y => ρ y * (θ y - θ'c y) with hw
  have hwm : Measurable w := hρ.measurable.mul (hθm.sub hθ'cm)
  have hρi : Integrable ρ := HRS.Whole.Q34.integrable_of_isProbDensity hρ
  have hdiff : ∀ y, |θ y - θ'c y| ≤ Cν := fun y => by
    rw [abs_le]; constructor <;> linarith [hθ0 y, hθ'c0 y, hθC y, hθ'cb y]
  have hwb : ∀ y, |w y| ≤ max M 0 * Cν := fun y => by
    simp only [hw]
    rw [abs_mul, abs_of_nonneg (hρ.nonneg y)]
    exact mul_le_mul (hM'ρ y) (hdiff y) (abs_nonneg _) hM'0
  have hwi : Integrable w := by
    refine Integrable.mono' (hρi.mul_const Cν) hwm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ.nonneg y)]
    exact mul_le_mul_of_nonneg_left (hdiff y) (hρ.nonneg y)
  refine ⟨w, hwm, hwb, hwi, ?_, ?_⟩
  · have e : ∫ y, |w y| = ∫ y, |θ y - θ'c y| ∂(HRS.Whole.withDensityReal ρ) := by
      rw [wr13e_integral_nu hρ]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [hw]
      rw [abs_mul, abs_of_nonneg (hρ.nonneg y)]
    rw [e]
    exact hTVL1
  · intro x
    have i1 : Integrable (fun y => rieszKernel d s (x - y) * θ y) (HRS.Whole.withDensityReal ρ) :=
      (hint x).mul_bdd hθm.aestronglyMeasurable (c := Cν)
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_of_pos (hθ0 y)]; exact hθC y)
    have i2 : Integrable (fun y => rieszKernel d s (x - y) * θ'c y) (HRS.Whole.withDensityReal ρ) :=
      (hint x).mul_bdd hθ'cm.aestronglyMeasurable (c := Cν)
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hθ'c0 y)]; exact hθ'cb y)
    have e2 : ∫ y, rieszKernel d s (x - y) ∂ν =
        ∫ y, rieszKernel d s (x - y) * θ'c y ∂(HRS.Whole.withDensityReal ρ) := by
      rw [hνeq, integral_withDensity_eq_integral_toReal_smul (f := fun y => ENNReal.ofReal (θ'c y))
        (ENNReal.measurable_ofReal.comp hθ'cm)
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [ENNReal.toReal_ofReal (hθ'c0 y), smul_eq_mul]
      ring
    rw [e2, ← integral_sub i1 i2, wr13e_integral_nu hρ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hw]
    ring

/-- **The convolution term of the cavity equation**: if `ν ≤ Cν μ` is a probability measure whose event distance
to `θ μ` is at most `K0 √(δ_N/N)` (`N = n+1 ≥ N₀`), then `x ↦ g*θ(x) - g*ν(x)` (integrals against `μ`, `ν`) is the
measurable function `g * (ρ (θ - θ'))` with `L²(μ)` norm `≤ C δ_N`, uniformly in the densities `ρ ≤ M`. -/
theorem wr13d_cv_bound (hd : 1 ≤ d) (hs : 0 < s) (hsd : s < d) (M : ℝ)
    {Cν : ℝ} (hCν1 : 1 ≤ Cν) {K0 : ℝ} (hK0 : 0 ≤ K0) :
    ∃ (C : ℝ) (N0 : ℕ), 0 ≤ C ∧ ∀ n : ℕ, N0 ≤ n + 1 → ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ →
      (∀ x, ρ x ≤ M) → ∀ θ : Euc d → ℝ, Measurable θ → (∀ x, 0 < θ x) → (∀ x, θ x ≤ Cν) →
      ∀ ν : Measure (Euc d), IsProbabilityMeasure ν →
      ν ≤ ENNReal.ofReal Cν • HRS.Whole.withDensityReal ρ →
      (∀ A : Set (Euc d), MeasurableSet A →
        |((HRS.Whole.withDensityReal ρ).withDensity (fun y => ENNReal.ofReal (θ y))).real A - ν.real A| ≤
          K0 * Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ))) →
      ∃ F : Euc d → ℝ, Measurable F ∧
        (∀ x, (∫ y, rieszKernel d s (x - y) * θ y ∂(HRS.Whole.withDensityReal ρ)) -
          ∫ y, rieszKernel d s (x - y) ∂ν = F x) ∧
        eLpNorm F 2 (HRS.Whole.withDensityReal ρ) ≤ ENNReal.ofReal (C * deltaN d s (n + 1)) := by
  obtain ⟨Ccv, Ncv, hCcv0, hcv⟩ := wr13c_conv_L2_delta hd hs hsd (max M 0 * Cν) M (2 * K0)
  refine ⟨Ccv, Ncv, hCcv0, ?_⟩
  intro n hn ρ hρ hM θ hθm hθ0 hθC ν hνp hνle hTV
  obtain ⟨w, hwm, hwb, hwi, hwL1, hid⟩ := wr13d_cv_prep hd hs hsd M hCν1 hρ hM hθm hθ0 hθC hνp hνle hTV
  have hwL1' : ∫ y, |w y| ≤ 2 * K0 * Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ)) :=
    hwL1.trans (le_of_eq (by ring))
  obtain ⟨hcvmem, hcvnorm⟩ := hcv (n + 1) hn w hwm hwb hwi hwL1' ρ hρ hM
  have hFm : Measurable fun x : Euc d => ∫ y, rieszKernel d s (x - y) * w y :=
    RefMarg.measurable_integral_kernel (F := fun p : Euc d × Euc d => rieszKernel d s (p.1 - p.2) * w p.2)
      (((HRS.Whole.Q34.measurable_rieszKernel hs.ne').comp (measurable_fst.sub measurable_snd)).mul
        (hwm.comp measurable_snd))
  have hFeq : (fun x : Euc d => ∫ y, rieszKernel d s (x - y) * w y) =
      fun x : Euc d => ∫ y, ‖x - y‖ ^ (-s) * w y := by
    funext x
    simp_rw [HRS.Whole.Q34.rieszKernel_eq hs.ne']
  have hcvmem' : MemLp (fun x : Euc d => ∫ y, rieszKernel d s (x - y) * w y) 2
      (HRS.Whole.withDensityReal ρ) := by rw [hFeq]; exact hcvmem
  have hcvnorm' : Real.sqrt (∫ x, (∫ y, rieszKernel d s (x - y) * w y) ^ 2 ∂(HRS.Whole.withDensityReal ρ)) ≤
      Ccv * deltaN d s (n + 1) := by
    simpa only [HRS.Whole.Q34.rieszKernel_eq hs.ne'] using hcvnorm
  exact ⟨fun x => ∫ y, rieszKernel d s (x - y) * w y, hFm, hid, wr13d_eLpNorm_le_of_sqrt hcvmem' hcvnorm'⟩

/-- **Sup norm of the convolution term**: with the notation of `wr13d_cv_prep` and `2ε ≤ 1`,
`|g*θ(x) - g*ν(x)| ≤ C (2ε)^{1-s/d}` for every `x`. -/
theorem wr13d_cv_sup (hd : 1 ≤ d) (hs : 0 < s) (hsd : s < d) (M : ℝ) {Cν : ℝ} (hCν1 : 1 ≤ Cν) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ θ : Euc d → ℝ, Measurable θ → (∀ x, 0 < θ x) → (∀ x, θ x ≤ Cν) →
      ∀ ν : Measure (Euc d), IsProbabilityMeasure ν →
      ν ≤ ENNReal.ofReal Cν • HRS.Whole.withDensityReal ρ → ∀ ε : ℝ, 2 * ε ≤ 1 →
      (∀ A : Set (Euc d), MeasurableSet A →
        |((HRS.Whole.withDensityReal ρ).withDensity (fun y => ENNReal.ofReal (θ y))).real A - ν.real A| ≤ ε) →
      ∀ x, |(∫ y, rieszKernel d s (x - y) * θ y ∂(HRS.Whole.withDensityReal ρ)) -
          ∫ y, rieszKernel d s (x - y) ∂ν| ≤ C * (2 * ε) ^ (1 - s / d) := by
  obtain ⟨C, hC0, hC⟩ := wr13c_sup_conv_small hd hs hsd (max M 0 * Cν)
  refine ⟨C, hC0, fun ρ hρ hM θ hθm hθ0 hθC ν hνp hνle ε hε hTV x => ?_⟩
  obtain ⟨w, hwm, hwb, hwi, hwL1, hid⟩ := wr13d_cv_prep hd hs hsd M hCν1 hρ hM hθm hθ0 hθC hνp hνle hTV
  obtain ⟨-, hb⟩ := hC w hwm hwb hwi (2 * ε) hε hwL1
  rw [hid x]
  exact hb x

end CvBound

/-! ### 3. The `L²` core -/

section Core

variable {ρ : Euc d → ℝ} {M β : ℝ} {n : ℕ}

/-- `0 ≤ g*ν ≤ Cν M_g` for a probability measure `ν ≤ Cν μ`. -/
theorem wr13d_conv_nu_le (hd : 1 ≤ d) (hs0 : 0 < s) (hsd : s < d)
    (hρ : HRS.Whole.IsProbDensity ρ) (hM : ∀ x, ρ x ≤ M) {Cν : ℝ} (hCν0 : 0 ≤ Cν)
    {ν : Measure (Euc d)} (hνle : ν ≤ ENNReal.ofReal Cν • HRS.Whole.withDensityReal ρ) (x : Euc d) :
    0 ≤ ∫ y, rieszKernel d s (x - y) ∂ν ∧ ∫ y, rieszKernel d s (x - y) ∂ν ≤ Cν * potentialBound d s M := by
  refine ⟨integral_nonneg fun y => wr13a_g_nonneg hs0 _, ?_⟩
  have h1 := wr13e_integral_le_of_le_smul hνle hCν0 (f := fun y => rieszKernel d s (x - y))
    (fun y => wr13a_g_nonneg hs0 _) (wr13a_potential_bound hd hs0 hsd hρ hM x).1
  refine h1.trans ?_
  exact mul_le_mul_of_nonneg_left (wr13a_conv_le_density hd hs0 hsd hρ hM x) hCν0

set_option maxHeartbeats 1600000 in
/-- **`L²` core** (torus `L2_all`): for `N = n + 1 ≥ N₁` (`n ≥ 1`), `‖θ_N - 1‖_{L²(μ)} ≤ C δ_N`, with `C, N₁` depending
only on `(d, s, βm, βp, M)`. -/
theorem wr13d_core_L2 (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) {βm : ℝ} (hβm : 0 < βm) {βp : ℝ}
    (hβ : βm ≤ βp) (M : ℝ) :
    ∃ (C : ℝ) (N₁ : ℕ), ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ β : ℝ, βm ≤ β → β ≤ βp → ∀ n : ℕ, 1 ≤ n → N₁ ≤ n + 1 →
        MemLp (fun x => wr13d_theta d s n β (HRS.Whole.withDensityReal ρ) x - 1) 2
          (HRS.Whole.withDensityReal ρ) ∧
        eLpNorm (fun x => wr13d_theta d s n β (HRS.Whole.withDensityReal ρ) x - 1) 2
          (HRS.Whole.withDensityReal ρ) ≤ ENNReal.ofReal (C * deltaN d s (n + 1)) := by
  have hd1 : 1 ≤ d := by omega
  have hβp0 : 0 ≤ βp := (hβm.le.trans hβ)
  set Mg : ℝ := max (potentialBound d s M) 0 with hMg
  have hMg0 : 0 ≤ Mg := le_max_right _ _
  obtain ⟨C', hC'1, hνC'⟩ := wr13d_cavMarg_le hd hs0 hsd βp M hβp0
  set Cθ : ℝ := Real.exp (2 * βp * |potentialBound d s M|) with hCθ
  have hCθ1 : 1 ≤ Cθ := Real.one_le_exp (by positivity)
  set Cν : ℝ := max Cθ C' with hCν
  have hCν1 : 1 ≤ Cν := hCθ1.trans (le_max_left _ _)
  have hCν0 : 0 ≤ Cν := by linarith
  obtain ⟨K, hK0, hK⟩ := wr13d_event_bound hd hs0 hsd hβm βp M
  obtain ⟨Ccv, Ncv, hCcv0, hcvb⟩ := wr13d_cv_bound hd1 hs0 hsd M hCν1 hK0
  obtain ⟨CD, hCD0, hD⟩ := wr13c2_insDefect_le hd hs0 hsd hβm βp M
  refine ⟨Cν * (CD + βp * Ccv + βp * (Cν * Mg)), Ncv, ?_⟩
  intro ρ hρ hM β hβ1 hββp n hn hN1
  have hμp := wr13a_isProb_density hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  have hβ0 : 0 ≤ β := (hβm.trans_le hβ1).le
  set θ : Euc d → ℝ := wr13d_theta d s n β μ with hθdef
  have hθm : Measurable θ := wr13d_theta_meas hd hs0 hsd hρ hM hβ0 n
  have hθ0 : ∀ x, 0 < θ x := wr13d_theta_pos hd hs0 hsd hρ hM hβ0 hn
  have hMgle : potentialBound d s M ≤ |potentialBound d s M| := le_abs_self _
  have hθCθ : ∀ x, θ x ≤ Cθ := by
    intro x
    refine (wr13d_theta_le hd hs0 hsd hρ hM hβ0 n x).trans (Real.exp_le_exp.2 ?_)
    have h1 : 2 * β * potentialBound d s M ≤ 2 * β * |potentialBound d s M| :=
      mul_le_mul_of_nonneg_left hMgle (by positivity)
    have h2 : 2 * β * |potentialBound d s M| ≤ 2 * βp * |potentialBound d s M| :=
      mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    linarith
  have hθC : ∀ x, θ x ≤ Cν := fun x => (hθCθ x).trans (le_max_left _ _)
  have hθ1 : ∫ x, θ x ∂μ = 1 := wr13d_theta_integral hd hs0 hsd hρ hM hβ0 hn
  have hint : ∀ x : Euc d, Integrable (fun y => rieszKernel d s (x - y)) μ :=
    fun x => (wr13a_potential_bound hd1 hs0 hsd hρ hM x).1
  -- the cavity marginal
  set ν := HRS.Whole.cavityMarginal d s (n + 1) β μ with hνdef
  haveI hνp : IsProbabilityMeasure ν := wr13d_cavMarg_isProb hd hs0 hsd hρ hM hβ0 hn
  have hνle : ν ≤ ENNReal.ofReal Cν • μ := by
    refine (hνC' ρ hρ hM β hβ0 hββp (n + 1) (by omega)).trans ?_
    intro A
    simp only [Measure.smul_apply, smul_eq_mul]
    gcongr
    exact le_max_right _ _
  have hTV : ∀ A : Set (Euc d), MeasurableSet A →
      |(μ.withDensity (fun y => ENNReal.ofReal (θ y))).real A - ν.real A| ≤
        K * Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ)) := by
    intro A hA
    have := hK ρ hρ hM β hβ1 hββp n hn A hA
    rwa [wr13d_firstMarginal_eq hd hs0 hsd hρ hM hβ0 n] at this
  obtain ⟨F, hFm, hFid, hFnorm⟩ := hcvb n hN1 ρ hρ hM θ hθm hθ0 hθC ν hνp hνle hTV
  -- numerics
  have hN2 : (2 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    have : 2 ≤ n + 1 := by omega
    exact_mod_cast this
  have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by linarith
  have hδ0 : 0 ≤ deltaN d s (n + 1) := HRS.deltaN_nonneg s (by omega)
  have hδ1 : (((n + 1 : ℕ) : ℝ))⁻¹ ≤ deltaN d s (n + 1) :=
    HRS.WeakRef.inv_le_deltaN hd1 hs0.le hsd (by omega)
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = β / ((n + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  have hlam0 : 0 ≤ lam := by rw [hlam]; exact div_nonneg hβ0 (Nat.cast_nonneg _)
  have hlam_le : lam ≤ β * deltaN d s (n + 1) := by
    have : lam = β * (((n + 1 : ℕ) : ℝ))⁻¹ := by rw [hlam]; ring
    rw [this]; exact mul_le_mul_of_nonneg_left hδ1 hβ0
  have hlamN : lam * ((n + 1 : ℕ) : ℝ) = β := by rw [hlam]; field_simp
  -- the cavity correction `D`
  set Dfun : Euc d → ℝ := fun x => HRS.Whole.insertionDefect d s (n + 1) β μ x with hDfun
  have hDb : ∀ x, 0 ≤ Dfun x ∧ Dfun x ≤ CD * deltaN d s (n + 1) := fun x => by
    obtain ⟨-, h1, h2, -⟩ := hD ρ hρ hM β hβ1 hββp (n + 1) (by omega) x
    exact ⟨h1, h2⟩
  have hQνm : Measurable fun x => ∫ y, rieszKernel d s (x - y) ∂ν :=
    RefMarg.measurable_integral_kernel (F := fun p : Euc d × Euc d => rieszKernel d s (p.1 - p.2))
      ((HRS.Whole.Q34.measurable_rieszKernel hs0.ne').comp (measurable_fst.sub measurable_snd))
  have hlogθ := wr13d_log_theta hd hs0 hsd hρ hM hβ0 hn
  have hDm : Measurable Dfun := by
    have e : Dfun = fun x => Real.log (θ x) - β * HRS.Whole.convMeasure (rieszKernel d s) μ x +
        (β / ((n + 1 : ℕ) : ℝ)) * n * (∫ y, rieszKernel d s (x - y) ∂ν) +
          Real.log (wr13d_Z d s n β μ) := by
      funext x
      have := hlogθ x
      simp only [hDfun]
      rw [hθdef]
      linarith
    rw [e]
    exact (((Real.measurable_log.comp hθm).sub ((wr13a_conv_meas hs0 μ).const_mul β)).add
      (hQνm.const_mul ((β / ((n + 1 : ℕ) : ℝ)) * n))).add measurable_const
  have hDL2 : eLpNorm Dfun 2 μ ≤ ENNReal.ofReal (CD * deltaN d s (n + 1)) :=
    RefMarg.eLpNorm_two_le_const hDm.aestronglyMeasurable fun x => by
      rw [abs_of_nonneg (hDb x).1]; exact (hDb x).2
  -- the term `lam * g*ν`
  have hQb : ∀ x, 0 ≤ ∫ y, rieszKernel d s (x - y) ∂ν ∧
      ∫ y, rieszKernel d s (x - y) ∂ν ≤ Cν * Mg := fun x => by
    obtain ⟨h1, h2⟩ := wr13d_conv_nu_le hd1 hs0 hsd hρ hM hCν0 hνle x
    exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hCν0)⟩
  have hQL2 : eLpNorm (fun x => lam * ∫ y, rieszKernel d s (x - y) ∂ν) 2 μ ≤
      ENNReal.ofReal (βp * (Cν * Mg) * deltaN d s (n + 1)) :=
    RefMarg.eLpNorm_two_le_const (hQνm.const_mul lam).aestronglyMeasurable fun x => by
      rw [abs_of_nonneg (mul_nonneg hlam0 (hQb x).1)]
      calc lam * ∫ y, rieszKernel d s (x - y) ∂ν
          ≤ (β * deltaN d s (n + 1)) * (Cν * Mg) :=
            mul_le_mul hlam_le (hQb x).2 (hQb x).1 (by positivity)
        _ ≤ βp * (Cν * Mg) * deltaN d s (n + 1) := by
            have : β * deltaN d s (n + 1) * (Cν * Mg) = β * (Cν * Mg) * deltaN d s (n + 1) := by ring
            rw [this]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hββp (by positivity)) hδ0
  -- the kernel `K_g`
  have hzm : Measurable fun y => θ y - 1 := hθm.sub_const 1
  have hz2 : MemLp (fun y => θ y - 1) 2 μ :=
    MemLp.of_bound hzm.aestronglyMeasurable Cν (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hθ0 y, hθC y])
  have hM'ρ : ∀ x, ρ x ≤ max M 0 := fun x => (hM x).trans (le_max_left _ _)
  obtain ⟨CS, hCS0, hCS⟩ := wr13c_schur_W_real hd1 hs0.le hsd (max M 0)
  have hKz2 : MemLp (fun x => ∫ y, rieszKernel d s (x - y) * (θ y - 1) ∂μ) 2 μ :=
    (hCS ρ hρ hM'ρ 1 zero_le_one (fun x y => rieszKernel d s (x - y))
      ((HRS.Whole.Q34.measurable_rieszKernel hs0.ne').comp (measurable_fst.sub measurable_snd))
      (fun x y hxy => by
        have h1 := wr13e_g_eq_weight (d := d) hs0 (x - y)
        have h2 := wr3_rieszWeight_nonneg (d := d) s (x - y)
        show |rieszKernel d s (x - y)| ≤ 1 * (1 + HRS.Whole.rieszWeight s (x - y))
        rw [h1, abs_of_nonneg h2]; linarith)
      (fun y => θ y - 1) hzm hz2).1
  have hnn : 0 ≤ ∫ x, (∫ y, rieszKernel d s (x - y) * (θ y - 1) ∂μ) * (θ x - 1) ∂μ :=
    (wr13c_Kmu_nonneg hd1 hs0 hsd hρ hM'ρ hzm hz2).2
  -- the equation
  have heq : ∀ x, Real.log (θ x) + β * (∫ y, rieszKernel d s (x - y) * (θ y - 1) ∂μ) =
      Dfun x + β * F x + lam * (∫ y, rieszKernel d s (x - y) ∂ν) + -Real.log (wr13d_Z d s n β μ) := by
    intro x
    have i1 : Integrable (fun y => rieszKernel d s (x - y) * θ y) μ :=
      (hint x).mul_bdd hθm.aestronglyMeasurable (c := Cν)
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_of_pos (hθ0 y)]; exact hθC y)
    have hKz : ∫ y, rieszKernel d s (x - y) * (θ y - 1) ∂μ =
        F x + (∫ y, rieszKernel d s (x - y) ∂ν) - HRS.Whole.convMeasure (rieszKernel d s) μ x := by
      have e1 : ∫ y, rieszKernel d s (x - y) * (θ y - 1) ∂μ =
          (∫ y, rieszKernel d s (x - y) * θ y ∂μ) - ∫ y, rieszKernel d s (x - y) ∂μ := by
        rw [← integral_sub i1 (hint x)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only
        ring
      rw [e1]
      have := hFid x
      unfold HRS.Whole.convMeasure
      linarith
    have hlog := hlogθ x
    rw [← hlam] at hlog
    have hlamN' : lam * ((n : ℝ) + 1) = β := by
      have := hlamN
      push_cast at this
      exact this
    simp only [hDfun]
    rw [hKz]
    rw [hθdef]
    linear_combination hlog - (∫ y, rieszKernel d s (x - y) ∂ν) * hlamN'
  have hass := wr13e_L2_assemble (μ := μ) (lam := lam) (e1 := CD * deltaN d s (n + 1))
    (e2 := Ccv * deltaN d s (n + 1)) (e3 := βp * (Cν * Mg) * deltaN d s (n + 1)) hβ0 hCν1 hθm hθ0
    (Filter.Eventually.of_forall hθC) hθ1 hDm hFm hQνm hDL2 hFnorm hQL2 (by positivity) (by positivity)
    (by positivity) hKz2 hnn heq
  refine ⟨hz2, hass.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have h1 : β * (Ccv * deltaN d s (n + 1)) ≤ βp * (Ccv * deltaN d s (n + 1)) :=
    mul_le_mul_of_nonneg_right hββp (by positivity)
  calc Cν * (CD * deltaN d s (n + 1) + β * (Ccv * deltaN d s (n + 1)) +
        βp * (Cν * Mg) * deltaN d s (n + 1))
      ≤ Cν * (CD * deltaN d s (n + 1) + βp * (Ccv * deltaN d s (n + 1)) +
        βp * (Cν * Mg) * deltaN d s (n + 1)) := by gcongr
    _ = Cν * (CD + βp * Ccv + βp * (Cν * Mg)) * deltaN d s (n + 1) := by ring

end Core

/-! ### 3b. Uniform smallness `‖θ_N - 1‖_∞ → 0` -/

section Uniform

variable {ρ : Euc d → ℝ} {M β : ℝ} {n : ℕ}

/-- **`‖dπ_N/dμ - 1‖_∞ → 0`, uniformly** (`euc-unsimplified` plus the sup bound): for every `ε > 0` there is `N₁`
(depending only on `ε, d, s, βm, βp, M`) with `|θ_N(x) - 1| ≤ ε` for all `x`, `ρ ≤ M`, `β ∈ [βm, βp]`,
`n ≥ 1`, `n + 1 ≥ N₁`.  Inputs: the unsimplified equation `log θ + log Z = β g*(μ - ν_n) + λ g*ν_n + D_N`,
`‖π_N - μ‖_TV ≤ √(β C N^{s/d-1}/2)` (`euc_tv_Q_le`), `‖π_N - ν_n‖_TV ≤ K √(δ_N/N)` and the sup bound
`‖g * f‖_∞ ≤ C ‖f‖₁^{1-s/d}`. -/
theorem wr13d_theta_uniform (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) {βm βp : ℝ} (hβm : 0 < βm)
    (hβ : βm ≤ βp) (M : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ N₁ : ℕ, ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ β : ℝ, βm ≤ β → β ≤ βp → ∀ n : ℕ, 1 ≤ n → N₁ ≤ n + 1 → ∀ x : Euc d,
        |wr13d_theta d s n β (HRS.Whole.withDensityReal ρ) x - 1| ≤ ε := by
  intro ε hε
  have hd1 : 1 ≤ d := by omega
  have hβp0 : 0 ≤ βp := hβm.le.trans hβ
  set Mg : ℝ := max (potentialBound d s M) 0 with hMg
  have hMg0 : 0 ≤ Mg := le_max_right _ _
  obtain ⟨C', hC'1, hνC'⟩ := wr13d_cavMarg_le hd hs0 hsd βp M hβp0
  set Cθ : ℝ := Real.exp (2 * βp * |potentialBound d s M|) with hCθ
  have hCθ1 : 1 ≤ Cθ := Real.one_le_exp (by positivity)
  set Cν : ℝ := max Cθ C' with hCν
  have hCν1 : 1 ≤ Cν := hCθ1.trans (le_max_left _ _)
  have hCν0 : 0 ≤ Cν := by linarith
  obtain ⟨K, hK0, hK⟩ := wr13d_event_bound hd hs0 hsd hβm βp M
  obtain ⟨CS, hCS0, hCS⟩ := wr13d_cv_sup hd1 hs0 hsd M hCν1
  obtain ⟨CD, hCD0, hD⟩ := wr13c2_insDefect_le hd hs0 hsd hβm βp M
  obtain ⟨CT, hCT0, hCT⟩ := euc_tv_Q_le hd1 hs0 hsd M
  set a : ℝ := 1 - s / (d : ℝ) with ha_def
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  have ha : 0 < a := by
    have : s / (d : ℝ) < 1 := by rw [div_lt_one hdpos]; exact hsd
    rw [ha_def]; linarith
  set r0 : ℝ := min (ε / 4) (1 / 2) with hr0def
  have hr0 : 0 < r0 := lt_min (by positivity) (by norm_num)
  have hr0ε : 4 * r0 ≤ ε := by
    have : r0 ≤ ε / 4 := min_le_left _ _
    linarith
  have hr01 : 2 * r0 ≤ 1 := by
    have : r0 ≤ 1 / 2 := min_le_right _ _
    linarith
  -- the sequences
  set epsN : ℕ → ℝ := fun N => Real.sqrt (βp * (CT * (N : ℝ) ^ (s / (d : ℝ) - 1)) / 2) +
    K * Real.sqrt (deltaN d s N / (N : ℝ)) with hepsN
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ (s / (d : ℝ) - 1)) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop ha).comp hcast
    have e : -a = s / (d : ℝ) - 1 := by rw [ha_def]; ring
    rw [e] at this
    exact this
  have hsq0 : Tendsto Real.sqrt (𝓝 (0 : ℝ)) (𝓝 0) := by
    have := Real.continuous_sqrt.tendsto (0 : ℝ)
    simpa using this
  have hT1 : Tendsto (fun N : ℕ => Real.sqrt (βp * (CT * (N : ℝ) ^ (s / (d : ℝ) - 1)) / 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => βp * (CT * (N : ℝ) ^ (s / (d : ℝ) - 1)) / 2) atTop (𝓝 0) := by
      have := ((hpow.const_mul CT).const_mul βp).div_const 2
      simpa using this
    exact hsq0.comp h1
  have hdelta : Tendsto (fun N : ℕ => deltaN d s N) atTop (𝓝 0) := RefMarg.tendsto_deltaN hd hs0.le hsd
  have hT2 : Tendsto (fun N : ℕ => K * Real.sqrt (deltaN d s N / (N : ℝ))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => deltaN d s N / (N : ℝ)) atTop (𝓝 0) := by
      have := hdelta.mul (tendsto_inv_atTop_zero.comp hcast)
      simpa [div_eq_mul_inv] using this
    have := (hsq0.comp h1).const_mul K
    simpa using this
  have hepsT : Tendsto epsN atTop (𝓝 0) := by
    have := hT1.add hT2
    rw [add_zero] at this
    exact this
  have hRT : Tendsto (fun N : ℕ => βp * (CS * (2 * epsN N) ^ a) + βp * (Cν * Mg) / (N : ℝ) +
      CD * deltaN d s N) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => (2 * epsN N) ^ a) atTop (𝓝 0) := by
      have := (hepsT.const_mul 2).rpow_const (p := a) (Or.inr ha.le)
      simpa [Real.zero_rpow ha.ne'] using this
    have h2 : Tendsto (fun N : ℕ => βp * (Cν * Mg) / (N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    have h3 := hdelta.const_mul CD
    have := ((h1.const_mul CS).const_mul βp).add h2 |>.add h3
    simpa using this
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1
    ((hepsT.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))).and
      (hRT.eventually (ge_mem_nhds hr0)))
  refine ⟨N₁, fun ρ hρ hM β hβ1 hββp n hn hNn x => ?_⟩
  obtain ⟨hε1, hR⟩ := hN₁ (n + 1) hNn
  have hβ0 : 0 ≤ β := (hβm.trans_le hβ1).le
  have hμp := wr13a_isProb_density hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set θ : Euc d → ℝ := wr13d_theta d s n β μ with hθdef
  have hθ0 : ∀ x, 0 < θ x := wr13d_theta_pos hd hs0 hsd hρ hM hβ0 hn
  have hθm : Measurable θ := wr13d_theta_meas hd hs0 hsd hρ hM hβ0 n
  have hMgle : potentialBound d s M ≤ |potentialBound d s M| := le_abs_self _
  have hθCθ : ∀ x, θ x ≤ Cθ := by
    intro x
    refine (wr13d_theta_le hd hs0 hsd hρ hM hβ0 n x).trans (Real.exp_le_exp.2 ?_)
    have h1 : 2 * β * potentialBound d s M ≤ 2 * β * |potentialBound d s M| :=
      mul_le_mul_of_nonneg_left hMgle (by positivity)
    have h2 : 2 * β * |potentialBound d s M| ≤ 2 * βp * |potentialBound d s M| :=
      mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    linarith
  have hθ1 : ∫ x, θ x ∂μ = 1 := wr13d_theta_integral hd hs0 hsd hρ hM hβ0 hn
  have hθint : Integrable θ μ :=
    Integrable.of_bound hθm.aestronglyMeasurable Cθ (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (hθ0 x)]; exact hθCθ x)
  -- the cavity marginal and the event bound against `μ`
  set ν := HRS.Whole.cavityMarginal d s (n + 1) β μ with hνdef
  have hνp : IsProbabilityMeasure ν := wr13d_cavMarg_isProb hd hs0 hsd hρ hM hβ0 hn
  have hνle : ν ≤ ENNReal.ofReal Cν • μ := by
    refine (hνC' ρ hρ hM β hβ0 hββp (n + 1) (by omega)).trans ?_
    intro A
    simp only [Measure.smul_apply, smul_eq_mul]
    gcongr
    exact le_max_right _ _
  have hπp := wr13d_firstMarginal_isProb hd hs0 hsd hρ hM hβ0 hn
  have hTVμ : ∀ A : Set (Euc d), MeasurableSet A →
      |(μ.withDensity (fun y => ENNReal.ofReal ((fun _ : Euc d => (1 : ℝ)) y))).real A - ν.real A| ≤
        epsN (n + 1) := by
    intro A hA
    have e1 : (μ.withDensity (fun y => ENNReal.ofReal ((fun _ : Euc d => (1 : ℝ)) y))) = μ := by
      simp
    rw [e1]
    set π := HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs (rieszKernel d s) (n + 1) β μ) with hπ
    have h1 : |π.real A - μ.real A| ≤ Real.sqrt (βp * (CT * ((n + 1 : ℕ) : ℝ) ^ (s / (d : ℝ) - 1)) / 2) := by
      refine (HRS.External.Entropy.abs_le_tvDist π μ hA).trans ((hCT ρ hρ hM β hβ0 (n + 1) (by omega)).trans ?_)
      refine Real.sqrt_le_sqrt ?_
      have : 0 ≤ CT * ((n + 1 : ℕ) : ℝ) ^ (s / (d : ℝ) - 1) :=
        mul_nonneg hCT0 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      have h2 := mul_le_mul_of_nonneg_right hββp this
      linarith
    have h2 : |π.real A - ν.real A| ≤ K * Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ)) :=
      hK ρ hρ hM β hβ1 hββp n hn A hA
    have h3 : |μ.real A - ν.real A| ≤ |π.real A - μ.real A| + |π.real A - ν.real A| := by
      have h3 := abs_sub_le (μ.real A) (π.real A) (ν.real A)
      rwa [abs_sub_comm (μ.real A) (π.real A)] at h3
    exact h3.trans (by simpa only [hepsN] using add_le_add h1 h2)
  have hsup := hCS ρ hρ hM (fun _ => 1) measurable_const (fun _ => one_pos) (fun _ => hCν1) ν hνp hνle
    (epsN (n + 1)) (by linarith) hTVμ x
  simp only [mul_one] at hsup
  -- the pointwise bound on `log θ + log Z`
  set c : ℝ := Real.log (wr13d_Z d s n β μ) with hc
  have hu : ∀ y, |Real.log (θ y) + c| ≤ βp * (CS * (2 * epsN (n + 1)) ^ a) +
      βp * (Cν * Mg) / ((n + 1 : ℕ) : ℝ) + CD * deltaN d s (n + 1) := by
    intro y
    have hsup' := hCS ρ hρ hM (fun _ => 1) measurable_const (fun _ => one_pos) (fun _ => hCν1) ν hνp hνle
      (epsN (n + 1)) (by linarith) hTVμ y
    simp only [mul_one] at hsup'
    have hlog := wr13d_log_theta hd hs0 hsd hρ hM hβ0 hn y
    obtain ⟨-, hD0, hD1, -⟩ := hD ρ hρ hM β hβ1 hββp (n + 1) (by omega) y
    obtain ⟨hg0, hg1⟩ := wr13d_conv_nu_le hd1 hs0 hsd hρ hM hCν0 hνle y
    have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    set gν := ∫ z, rieszKernel d s (y - z) ∂ν with hgν
    set gμ := HRS.Whole.convMeasure (rieszKernel d s) μ y with hgμ
    have hgμ' : gμ = ∫ z, rieszKernel d s (y - z) ∂μ := rfl
    have hlamN : β / ((n + 1 : ℕ) : ℝ) * ((n : ℝ) + 1) = β := by
      push_cast; field_simp
    have key : Real.log (θ y) + c = β * (gμ - gν) + β / ((n + 1 : ℕ) : ℝ) * gν +
        HRS.Whole.insertionDefect d s (n + 1) β μ y := by
      rw [hθdef]
      linear_combination hlog - gν * hlamN
    rw [key]
    have t1 : |β * (gμ - gν)| ≤ βp * (CS * (2 * epsN (n + 1)) ^ a) := by
      rw [abs_mul, abs_of_nonneg hβ0]
      calc β * |gμ - gν| ≤ βp * |gμ - gν| := mul_le_mul_of_nonneg_right hββp (abs_nonneg _)
        _ ≤ βp * (CS * (2 * epsN (n + 1)) ^ a) := by
            rw [hgμ']
            exact mul_le_mul_of_nonneg_left hsup' hβp0
    have t2 : |β / ((n + 1 : ℕ) : ℝ) * gν| ≤ βp * (Cν * Mg) / ((n + 1 : ℕ) : ℝ) := by
      rw [abs_of_nonneg (mul_nonneg (div_nonneg hβ0 hNpos.le) hg0)]
      calc β / ((n + 1 : ℕ) : ℝ) * gν ≤ β / ((n + 1 : ℕ) : ℝ) * (Cν * Mg) :=
            mul_le_mul_of_nonneg_left (hg1.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hCν0))
              (div_nonneg hβ0 hNpos.le)
        _ ≤ βp / ((n + 1 : ℕ) : ℝ) * (Cν * Mg) :=
            mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hββp hNpos.le) (by positivity)
        _ = βp * (Cν * Mg) / ((n + 1 : ℕ) : ℝ) := by ring
    have t3 : |HRS.Whole.insertionDefect d s (n + 1) β μ y| ≤ CD * deltaN d s (n + 1) := by
      rw [abs_of_nonneg hD0]; exact hD1
    calc |β * (gμ - gν) + β / ((n + 1 : ℕ) : ℝ) * gν + HRS.Whole.insertionDefect d s (n + 1) β μ y|
        ≤ |β * (gμ - gν) + β / ((n + 1 : ℕ) : ℝ) * gν| + |HRS.Whole.insertionDefect d s (n + 1) β μ y| :=
          abs_add_le _ _
      _ ≤ (|β * (gμ - gν)| + |β / ((n + 1 : ℕ) : ℝ) * gν|) + |HRS.Whole.insertionDefect d s (n + 1) β μ y| := by
          gcongr; exact abs_add_le _ _
      _ ≤ _ := by linarith
  -- normalisation: `|c| ≤ R`
  set R : ℝ := βp * (CS * (2 * epsN (n + 1)) ^ a) + βp * (Cν * Mg) / ((n + 1 : ℕ) : ℝ) +
    CD * deltaN d s (n + 1) with hRdef
  have hθexp : ∀ y, θ y = Real.exp (Real.log (θ y)) := fun y => (Real.exp_log (hθ0 y)).symm
  have hup : c ≤ R := by
    have h1 : ∀ y, θ y ≤ Real.exp (R - c) := fun y => by
      rw [hθexp y]
      refine Real.exp_le_exp.2 ?_
      have := (abs_le.1 (hu y)).2
      linarith
    have h2 : ∫ y, θ y ∂μ ≤ ∫ _y, Real.exp (R - c) ∂μ :=
      integral_mono hθint (integrable_const _) h1
    rw [hθ1] at h2
    simp at h2
    linarith
  have hlow : -R ≤ c := by
    have h1 : ∀ y, Real.exp (-R - c) ≤ θ y := fun y => by
      rw [hθexp y]
      refine Real.exp_le_exp.2 ?_
      have := (abs_le.1 (hu y)).1
      linarith
    have h2 : ∫ _y, Real.exp (-R - c) ∂μ ≤ ∫ y, θ y ∂μ :=
      integral_mono (integrable_const _) hθint h1
    rw [hθ1] at h2
    simp at h2
    linarith
  have hlogθ : |Real.log (θ x)| ≤ 2 * R := by
    have h1 := hu x
    rw [abs_le] at h1 ⊢
    constructor <;> linarith [h1.1, h1.2, hup, hlow]
  have hRle : R ≤ r0 := hR
  have h1 : |Real.log (θ x)| ≤ 1 := hlogθ.trans (by linarith)
  have := Real.abs_exp_sub_one_le h1
  rw [Real.exp_log (hθ0 x)] at this
  calc |θ x - 1| ≤ 2 * |Real.log (θ x)| := this
    _ ≤ 2 * (2 * R) := by gcongr
    _ ≤ ε := by linarith

end Uniform

/-! ### 4. The packaged bound (conjunct 3 of `euc_static`) -/

section Final

/-- **Full-law marginal bounds** (`HasMarginalDensityBounds`, conjunct 3 of `euc_static`): for `d ≥ 2`,
`0 < s < d`, `0 < βm ≤ βp`, there is `C` (quantified before `ρ`, `β ∈ [βm, βp]`, `N`) such that for every
probability density `ρ ≤ M`, `β ∈ [βm, βp]`, `N ≥ 2`, the first marginal of `Q_N` has a density `φ` with respect
to `μ = ρ dx`, `0 ≤ φ ≤ C` everywhere, `φ - 1 ∈ L²(μ)` and `‖φ - 1‖_{L²(μ)} ≤ C δ_N`. -/
theorem wr13d_marginal_density_bounds (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) {βm βp : ℝ}
    (hβm : 0 < βm) (hβ : βm ≤ βp) (M : ℝ) :
    ∃ C : ℝ, ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ β ∈ Set.Icc βm βp, ∀ N : ℕ, 2 ≤ N →
        HRS.Whole.HasMarginalDensityBounds
          (HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs (rieszKernel d s) N β
            (HRS.Whole.withDensityReal ρ)))
          (HRS.Whole.withDensityReal ρ) C (C * deltaN d s N) := by
  have hd1 : 1 ≤ d := by omega
  have hβp0 : 0 ≤ βp := hβm.le.trans hβ
  obtain ⟨CL, N1, hL⟩ := wr13d_core_L2 hd hs0 hsd hβm hβ M
  set Cθ : ℝ := Real.exp (2 * βp * |potentialBound d s M|) with hCθ
  have hCθ1 : 1 ≤ Cθ := Real.one_le_exp (by positivity)
  refine ⟨max (max Cθ CL) (Cθ * N1), fun ρ hρ hM β hβmem N hN => ?_⟩
  obtain ⟨hβ1, hββp⟩ := hβmem
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  have hμp := wr13a_isProb_density hρ
  have hβ0 : 0 ≤ β := (hβm.trans_le hβ1).le
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set C : ℝ := max (max Cθ CL) (Cθ * N1) with hC
  have hδ0 : 0 ≤ deltaN d s (n + 1) := HRS.deltaN_nonneg s (by omega)
  set θ : Euc d → ℝ := wr13d_theta d s n β μ with hθdef
  have hθm : Measurable θ := wr13d_theta_meas hd hs0 hsd hρ hM hβ0 n
  have hθ0 : ∀ x, 0 < θ x := wr13d_theta_pos hd hs0 hsd hρ hM hβ0 hn
  have hMgle : potentialBound d s M ≤ |potentialBound d s M| := le_abs_self _
  have hθCθ : ∀ x, θ x ≤ Cθ := by
    intro x
    refine (wr13d_theta_le hd hs0 hsd hρ hM hβ0 n x).trans (Real.exp_le_exp.2 ?_)
    have h1 : 2 * β * potentialBound d s M ≤ 2 * β * |potentialBound d s M| :=
      mul_le_mul_of_nonneg_left hMgle (by positivity)
    have h2 : 2 * β * |potentialBound d s M| ≤ 2 * βp * |potentialBound d s M| :=
      mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    linarith
  have hCθC : Cθ ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hz2 : MemLp (fun x => θ x - 1) 2 μ :=
    MemLp.of_bound (hθm.sub_const 1).aestronglyMeasurable Cθ (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hθ0 y, hθCθ y])
  have hnorm : eLpNorm (fun x => θ x - 1) 2 μ ≤ ENNReal.ofReal (C * deltaN d s (n + 1)) := by
    by_cases hN1 : N1 ≤ n + 1
    · refine (hL ρ hρ hM β hβ1 hββp n hn hN1).2.trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_left _ _)) hδ0
    · have hlt : n + 1 ≤ N1 := (not_le.1 hN1).le
      have hδ1 : (((n + 1 : ℕ) : ℝ))⁻¹ ≤ deltaN d s (n + 1) :=
        HRS.WeakRef.inv_le_deltaN hd1 hs0.le hsd (by omega)
      have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      have hone : 1 ≤ (N1 : ℝ) * deltaN d s (n + 1) := by
        have h1 : 1 ≤ ((n + 1 : ℕ) : ℝ) * deltaN d s (n + 1) := by
          rw [inv_le_iff_one_le_mul₀ hNpos, mul_comm] at hδ1
          exact hδ1
        have h2 : ((n + 1 : ℕ) : ℝ) ≤ N1 := by exact_mod_cast hlt
        exact h1.trans (mul_le_mul_of_nonneg_right h2 hδ0)
      refine (RefMarg.eLpNorm_two_le_const (hz2.aestronglyMeasurable) (C := Cθ) fun x => ?_).trans
        (ENNReal.ofReal_le_ofReal ?_)
      · rw [abs_le]; constructor <;> linarith [hθ0 x, hθCθ x]
      · calc Cθ ≤ Cθ * ((N1 : ℝ) * deltaN d s (n + 1)) := by nlinarith
          _ = (Cθ * N1) * deltaN d s (n + 1) := by ring
          _ ≤ C * deltaN d s (n + 1) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hδ0
  refine ⟨θ, hθm, wr13d_firstMarginal_eq hd hs0 hsd hρ hM hβ0 n, fun x => ⟨(hθ0 x).le, (hθCθ x).trans hCθC⟩,
    hz2, ?_⟩
  unfold HRS.Whole.l2Norm
  exact wr13d_sqrt_le_of_eLpNorm hz2 (mul_nonneg (le_trans (by linarith) hCθC) hδ0) hnorm

end Final

end HRS.MS.Wr
