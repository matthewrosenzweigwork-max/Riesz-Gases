import HRS.MS.Fp81S21MovingInputs
import HRS.MS.R2InterpAux73
import HRS.MS.S104eReg2
import HRS.MS.R2WinOrbNLAux1
import HRS.MS.R2S11Aux14
import HRS.MS.GenPathAux47
import HRS.MS.S21A_Mono
import HRS.MS.R2InterpAux105

/-!
# HRS S2.1(iii): trajectory-only producers for moving interpolation inputs

Every radius is selected before the trajectory parameter and trajectory. All constants below may
depend on the model parameters and the horizon, but are uniform in time on that horizon.
The proof of joint measurability copies the small-class continuity argument used privately in
`Fp81S21CovCoreBound.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.Whole.AppendixA
open HRS.MS.R26T3 HRS.MS.CovMeas HRS.MS.R2Interp

private theorem fp81s21_gaussian_weighted_moment
    {d : ℕ} {C₀ c₀ a : ℝ} (hc₀ : 0 < c₀) (ha : 0 ≤ a) :
    ∃ Mρ : ℝ, ∀ {ρ : Euc d → ℝ},
      (hρ : HRS.Whole.IsProbDensity ρ) →
      (hG : HRS.Whole.HasR2GaussianUpper C₀ c₀ ρ) →
      Integrable (fun x : Euc d => ρ x * jbracket x ^ a) ∧
        (∫ x : Euc d, ρ x * jbracket x ^ a) ≤ Mρ := by
  obtain ⟨C, hC0, hC⟩ := HRS.MS.R2Poly.s95_moment d C₀ c₀ hc₀
    (Pw := a / 2) (by linarith)
  refine ⟨C, ?_⟩
  intro ρ hρ hG
  have hpow : ∀ x : Euc d, (jbracket x ^ (a / 2)) ^ 2 = jbracket x ^ a := by
    intro x
    have hj : 0 < jbracket x := lt_of_lt_of_le zero_lt_one (HRS.MS.R2Poly.s95_one_le_jb x)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hj)]
    congr 1
    ring
  have hpowBound :
      (∫⁻ x, ENNReal.ofReal (jbracket x ^ a) ∂(HRS.Whole.withDensityReal ρ)) ≤ ENNReal.ofReal C := by
    calc
      _ = ∫⁻ x, ENNReal.ofReal ((jbracket x ^ (a / 2)) ^ 2) ∂(HRS.Whole.withDensityReal ρ) := by
        refine lintegral_congr fun x => ?_
        rw [hpow]
      _ ≤ ENNReal.ofReal C := hC ρ hρ hG.2
  have hgm : Measurable (fun x : Euc d => jbracket x ^ a) := by
    unfold jbracket
    fun_prop
  have h1 :
      (∫⁻ y, ENNReal.ofReal (jbracket y ^ a) ∂(HRS.Whole.withDensityReal ρ)) =
        ∫⁻ x, ENNReal.ofReal (ρ x * jbracket x ^ a) := by
    unfold HRS.Whole.withDensityReal
    have hf : Measurable (fun x => ENNReal.ofReal (ρ x)) :=
      ENNReal.measurable_ofReal.comp hρ.measurable
    have hg : Measurable (fun y => ENNReal.ofReal (jbracket y ^ a)) :=
      ENNReal.measurable_ofReal.comp hgm
    rw [lintegral_withDensity_eq_lintegral_mul (f := fun x => ENNReal.ofReal (ρ x))
      (g := fun y => ENNReal.ofReal (jbracket y ^ a)) volume hf hg]
    refine lintegral_congr fun x => ?_
    simp only [Pi.mul_apply]
    rw [ENNReal.ofReal_mul (hρ.nonneg x)]
  rw [h1] at hpowBound
  have hga : ∀ x : Euc d, 0 ≤ jbracket x ^ a := fun x =>
    Real.rpow_nonneg (Real.sqrt_nonneg _) a
  have hint : Integrable (fun x : Euc d => ρ x * jbracket x ^ a) := by
    refine ⟨(hρ.measurable.mul hgm).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    calc
      ∫⁻ x, ‖ρ x * jbracket x ^ a‖ₑ =
          ∫⁻ x, ENNReal.ofReal (ρ x * jbracket x ^ a) := by
        refine lintegral_congr fun x => ?_
        rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg (hρ.nonneg x) (hga x))]
      _ ≤ ENNReal.ofReal C := hpowBound
      _ < ⊤ := ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun x => mul_nonneg (hρ.nonneg x) (hga x))
    (hρ.measurable.mul hgm).aestronglyMeasurable]
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hpowBound
  rwa [ENNReal.toReal_ofReal hC0] at hreal

private theorem fp81s21_pair_withDensityReal
    {d : ℕ} {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) (f : Euc d → ℝ) :
    HRS.Whole.pair (HRS.Whole.withDensityReal ρ) f = ∫ x, ρ x * f x := by
  unfold HRS.Whole.pair HRS.Whole.withDensityReal
  rw [integral_withDensity_eq_integral_toReal_smul₀]
  · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [ENNReal.toReal_ofReal (hρ.nonneg x)]
  · exact (hρ.measurable.ennreal_ofReal).aemeasurable
  · exact Eventually.of_forall fun _ => ENNReal.ofReal_lt_top

private theorem fp81s21_moving_rho_joint_continuous
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) :
    Continuous fun z : ℝ≥0 × Euc p.d => R.ρ z.1 z.2 := by
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  have hρeq : R.ρβ = HRS.Whole.thermalDensity p.d p.s p.a p.β :=
    HRS.MS.Mov0.mv0_rho_eq p.hd p.hs0 hsd p.ha p.hβ R.thermal
  have hρβc : Continuous R.ρβ := by
    obtain ⟨-, ψ', hψ'⟩ := HRS.MS.S21.s21_schwartz_thermal
      p.hd p.hs0 hsd p.ha p.hβ
    rw [hρeq, ← hψ']
    exact ψ'.continuous
  have hρβpos : ∀ x, 0 < R.ρβ x := fun x => HRS.Whole.u4_thermal_pos R.thermal x
  have hm : (p.d : ℝ) / 2 < ((102 * p.d + 1020 : ℕ) : ℝ) := by
    rw [HRS.MS.R2WinOrbNL.s103n_cast_m]
    nlinarith
  have hclass := HRS.MS.R2WinOrbNL.s103n_small_class R.resulting
    (r := p.C₁ * δ) le_rfl
  exact HRS.MS.R2S11.s11_class_continuous hρβc hρβpos hm hclass

private theorem fp81s21_log_integrable_withDensityReal
    {d : ℕ} {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ)
    (hmom : Integrable (fun x : Euc d => ‖x‖ ^ 2 * ρ x)) :
    Integrable (fun x : Euc d => Real.log (2 + ‖x‖)) (HRS.Whole.withDensityReal ρ) := by
  have hρi : Integrable ρ volume := HRS.Whole.Q34.integrable_of_isProbDensity hρ
  unfold HRS.Whole.withDensityReal
  rw [integrable_withDensity_iff_integrable_smul' hρ.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hcont : Continuous fun x : Euc d => Real.log (2 + ‖x‖) :=
    (continuous_const.add continuous_norm).log (fun x => by
      show (2 + ‖x‖) ≠ 0
      positivity)
  have hdom : Integrable
      (fun x : Euc d => (3 / 2 : ℝ) * ρ x + (1 / 2 : ℝ) * (‖x‖ ^ 2 * ρ x)) :=
    (hρi.const_mul _).add (hmom.const_mul _)
  refine hdom.mono'
    ((hρ.measurable.ennreal_ofReal.ennreal_toReal.smul hcont.measurable).aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  have hx := hρ.nonneg x
  have hr := norm_nonneg x
  have hlog0 : 0 ≤ Real.log (2 + ‖x‖) := Real.log_nonneg (by linarith)
  rw [ENNReal.toReal_ofReal hx, smul_eq_mul,
    Real.norm_of_nonneg (mul_nonneg hx hlog0)]
  have h1 := Real.log_le_sub_one_of_pos (show 0 < 2 + ‖x‖ by positivity)
  nlinarith [mul_nonneg hx (sq_nonneg (‖x‖ - 1))]

/-- Produce all requested `Fp81MovingStd` fields except the later orbit-summability datum `hD`
and active-interval Gram continuity `hGram`, together with the trajectory-only physical fields.
The radius is the common radius from `fp81s21_common_radius`, chosen before `δ` and `R`.
Constants may depend on `p` and `H`, and all time bounds are uniform for `u ∈ [0,H]`. -/
theorem fp81s21_moving_trajectory_fields (p : Parameters) :
    ∃ δ0 Co co : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧ 0 < co ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ (R : Trajectory p δ) (H : ℝ), 0 < H →
        let C := r26t3_coeff R
        (0 ≤ C.ν) ∧
        (∀ u ∈ Set.Icc (0 : ℝ) H, Integrable (C.ρ u)) ∧
        (∀ u ∈ Set.Icc (0 : ℝ) H, ∀ x, 0 ≤ C.ρ u x) ∧
        (∀ (α : MultiIndex p.d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) H →
          ∃ f, IsClassicalAdjointW C t (oscTestFun (wholeSpaceIndex p.d : ℝ) α) f) ∧
        (∃ Λ : ℝ, IsRegularMFRd p.s 3 Λ H R.ρ) ∧
        Measurable (fun q : Set.Icc (0 : ℝ) H × Euc p.d => R.ρ q.1 q.2) ∧
        (∃ M L : ℝ, ∀ u ∈ Set.Icc (0 : ℝ) H,
          HRS.Whole.IsRound2Density p.d p.s M L (R.ρ u)) ∧
        (∃ C₀ c₀ : ℝ, 0 < c₀ ∧ ∀ u ∈ Set.Icc (0 : ℝ) H, ∀ x,
          R.ρ u x ≤ C₀ * Real.exp (-c₀ * ‖x‖ ^ 2)) ∧
        (∃ Mρ : ℝ, ∀ u ∈ Set.Icc (0 : ℝ) H,
          Integrable (fun x : Euc p.d => R.ρ u x * jbracket x ^ (2 * ((p.d : ℝ) + 2))) ∧
          (∫ x : Euc p.d, R.ρ u x * jbracket x ^ (2 * ((p.d : ℝ) + 2))) ≤ Mρ) := by
  obtain ⟨δ0, Co, co, hδ0, hδhalf, hco, hcommon⟩ := fp81s21_common_radius p
  refine ⟨δ0, Co, co, hδ0, hδhalf, hco, fun δ hδ hδle R H hH => ?_⟩
  have hδh : δ ≤ 1 / 2 := hδle.trans hδhalf
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  let C : WholeCoeff p.d := r26t3_coeff R
  have hsol := R.resulting.global H
  letI : IsProbabilityMeasure (r26t3_mu R 0) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu
      (hsol.density 0 ⟨le_rfl, hH.le⟩)
  have hν : 0 ≤ C.ν := by
    change 0 ≤ p.β⁻¹
    exact inv_nonneg.mpr p.hβ.le
  have hint : ∀ u ∈ Set.Icc (0 : ℝ) H, Integrable (C.ρ u) := by
    intro u hu
    have hρ := hsol.density u hu
    change Integrable (R.ρ u)
    exact HRS.Whole.Q34.integrable_of_isProbDensity hρ
  have hnn : ∀ u ∈ Set.Icc (0 : ℝ) H, ∀ x, 0 ≤ C.ρ u x := by
    intro u hu x
    exact (hsol.density u hu).nonneg x
  have hcls : ∀ (α : MultiIndex p.d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) H →
      ∃ f, IsClassicalAdjointW C t (oscTestFun (wholeSpaceIndex p.d : ℝ) α) f := by
    intro α t ht
    have ht0 : 0 ≤ t := ht.1
    exact HRS.Fp81.S21.fp81s21_adjoint_of_osc_test p R
      (HRS.MS.GenPath.s56_isOscTest (wholeSpaceIndex p.d : ℝ) α) ht0
  obtain ⟨Λ, hregular⟩ := HRS.MS.S104e.s104e_regMF p.hd p.hs0 hsd p.ha p.hβ
    δ p.c₁ p.C₁ 3 (by omega) (ρβ := R.ρβ) R.thermal R.admissible R.resulting H hH.le
  obtain ⟨c₀, C₀, hc₀, hC₀, hgauss⟩ := HRS.MS.S104e.s104e_gauss_rho
    p.hd p.hs0 hsd p.ha p.hβ δ p.c₁ p.C₁ 0 (by omega) R.thermal R.resulting
  have hgauss' : ∀ u ∈ Set.Icc (0 : ℝ) H, ∀ x,
      R.ρ u x ≤ C₀ * Real.exp (-c₀ * ‖x‖ ^ 2) := by
    intro u hu x
    have h := (hgauss u hu.1).2 0 (by omega) x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs,
      abs_of_nonneg ((hsol.density u hu).nonneg x)] at h
    exact h
  have hgaussian : ∀ u ∈ Set.Icc (0 : ℝ) H,
      HRS.Whole.HasR2GaussianUpper C₀ c₀ (R.ρ u) := fun u hu => ⟨hc₀, hgauss' u hu⟩
  obtain ⟨Mρ, hMρ⟩ := fp81s21_gaussian_weighted_moment
    (d := p.d) (C₀ := C₀) (c₀ := c₀)
    (a := 2 * ((p.d : ℝ) + 2)) hc₀
    (by positivity : 0 ≤ 2 * ((p.d : ℝ) + 2))
  have hρjointNN := fp81s21_moving_rho_joint_continuous p R hδ hδh
  have hmap : Continuous
      (fun q : Set.Icc (0 : ℝ) H × Euc p.d =>
        ((⟨q.1.1, q.1.2.1⟩ : ℝ≥0), q.2)) := by
    fun_prop
  have hdensityJoint : Measurable
      (fun q : Set.Icc (0 : ℝ) H × Euc p.d => R.ρ q.1 q.2) := by
    have hcomp : Measurable (fun q : Set.Icc (0 : ℝ) H × Euc p.d =>
        R.ρ (⟨q.1.1, q.1.2.1⟩ : ℝ≥0) q.2) := hρjointNN.measurable.comp hmap.measurable
    convert hcomp using 1 <;> simp
  obtain ⟨M2, hM2⟩ := fp81s21_gaussian_weighted_moment
    (d := p.d) (C₀ := C₀) (c₀ := c₀) (a := (2 : ℝ)) hc₀
    (by norm_num : 0 ≤ (2 : ℝ))
  have hround2 : ∃ M L : ℝ, ∀ u ∈ Set.Icc (0 : ℝ) H,
      HRS.Whole.IsRound2Density p.d p.s M L (R.ρ u) := by
    refine ⟨C₀, 3 / 2 + M2 / 2, fun u hu => ?_⟩
    have hρ := hsol.density u hu
    haveI : IsProbabilityMeasure (r26t3_mu R u) :=
      HRS.Whole.Q34.isProbabilityMeasure_nu hρ
    have hbd : ∀ x, R.ρ u x ≤ C₀ := by
      intro x
      have h := hgauss' u hu x
      have hexp : Real.exp (-c₀ * ‖x‖ ^ 2) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        nlinarith [sq_nonneg ‖x‖, hc₀]
      calc R.ρ u x ≤ C₀ * Real.exp (-c₀ * ‖x‖ ^ 2) := h
        _ ≤ C₀ := by nlinarith [hC₀, Real.exp_pos (-c₀ * ‖x‖ ^ 2)]
    refine ⟨hρ, hbd, fun hs0 => ?_⟩
    have hsecond := hsol.second_moment u hu
    have hsecondBound :
        (∫ x : Euc p.d, ‖x‖ ^ 2 * R.ρ u x) ≤ M2 := by
      have hupper : ∀ x : Euc p.d,
          ‖x‖ ^ 2 * R.ρ u x ≤ R.ρ u x * jbracket x ^ (2 : ℝ) := by
        intro x
        have hjb : jbracket x ^ (2 : ℝ) = 1 + ‖x‖ ^ 2 := by
          calc
            jbracket x ^ (2 : ℝ) = jbracket x ^ (2 : ℕ) := Real.rpow_natCast _ _
            _ = 1 + ‖x‖ ^ 2 := HRS.MS.R2Poly.s95_jb_sq x
        rw [hjb]
        have hrho := hρ.nonneg x
        nlinarith [sq_nonneg ‖x‖]
      have hmu := hM2 (hsol.density u hu) (hgaussian u hu)
      exact (integral_mono hsecond hmu.1 hupper).trans hmu.2
    let μ : Measure (Euc p.d) := r26t3_mu R u
    haveI : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
    have hlog := fp81s21_log_integrable_withDensityReal hρ hsecond
    have hnorm2 : Integrable (fun x : Euc p.d => ‖x‖ ^ 2) μ := by
      change Integrable (fun x : Euc p.d => ‖x‖ ^ 2)
        (HRS.Whole.withDensityReal (R.ρ u))
      unfold HRS.Whole.withDensityReal
      rw [integrable_withDensity_iff_integrable_smul' hρ.measurable.ennreal_ofReal
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      refine hsecond.congr (Eventually.of_forall fun x => ?_)
      simp [ENNReal.toReal_ofReal (hρ.nonneg x), mul_comm]
    have hdom : Integrable (fun x : Euc p.d => (3 / 2 : ℝ) + (1 / 2 : ℝ) * ‖x‖ ^ 2) μ :=
      (integrable_const _).add (hnorm2.const_mul _)
    have hpt : ∀ x : Euc p.d,
        Real.log (2 + ‖x‖) ≤ (3 / 2 : ℝ) + (1 / 2 : ℝ) * ‖x‖ ^ 2 := by
      intro x
      have hx := Real.log_le_sub_one_of_pos (show 0 < 2 + ‖x‖ by positivity)
      nlinarith [sq_nonneg (‖x‖ - 1)]
    have hpair : (∫ x : Euc p.d, ‖x‖ ^ 2 ∂μ) =
        ∫ x : Euc p.d, R.ρ u x * ‖x‖ ^ 2 := by
      calc
        _ = HRS.Whole.pair μ (fun x : Euc p.d => ‖x‖ ^ 2) := rfl
        _ = _ := by
          simpa [HRS.Whole.pair, μ, r26t3_mu] using fp81s21_pair_withDensityReal hρ
            (fun x : Euc p.d => ‖x‖ ^ 2)
    have hlogBound :
        (∫ x : Euc p.d, Real.log (2 + ‖x‖) ∂μ) ≤ 3 / 2 + M2 / 2 := by
      calc
        _ ≤ ∫ x : Euc p.d, (3 / 2 : ℝ) + (1 / 2 : ℝ) * ‖x‖ ^ 2 ∂μ :=
          integral_mono hlog hdom hpt
        _ = 3 / 2 + (1 / 2 : ℝ) * (∫ x : Euc p.d, ‖x‖ ^ 2 ∂μ) := by
          rw [integral_add (integrable_const _) (hnorm2.const_mul _), integral_const,
            integral_const_mul]
          simp
        _ = 3 / 2 + (1 / 2 : ℝ) *
            (∫ x : Euc p.d, R.ρ u x * ‖x‖ ^ 2) := by rw [hpair]
        _ ≤ 3 / 2 + M2 / 2 := by
          have hsecondBound' :
              (∫ x : Euc p.d, R.ρ u x * ‖x‖ ^ 2) ≤ M2 := by
            simpa only [mul_comm] using hsecondBound
          nlinarith [hsecondBound']
    exact ⟨hlog, hlogBound⟩
  exact ⟨hν, hint, hnn, hcls, ⟨Λ, hregular⟩, hdensityJoint, hround2,
    ⟨C₀, c₀, hc₀, hgauss'⟩,
    ⟨Mρ, fun u hu => hMρ (hsol.density u hu) (hgaussian u hu)⟩⟩

/-- Produce the two particle-dependent fields in `Fp81MovingPhysicalInputs`. The interpolation
consumer supplies `hN : 2 ≤ N`; the radius is the minimum of the common trajectory radius and
the actual-density radius, and is fixed before `δ` and `R`. -/
theorem fp81s21_moving_particle_fields (p : Parameters) :
    ∃ δ0 Co co pinf K : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧ 0 < co ∧ 1 < pinf ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ (R : Trajectory p δ) (N : ℕ),
        2 ≤ N → ∀ (A : Particle R N) (H : ℝ), 0 < H →
          (∀ u ∈ Set.Icc (0 : ℝ) H,
            HasR2ActualDensity p.s p.β pinf K
              (r26t3_mu R u) (A.P.map (A.X u.toNNReal))) ∧
          (∃ Cm : ℝ, ∀ u ∈ Set.Icc (0 : ℝ) H,
            Integrable
              (fun x : Euc p.d => jbracket x ^ ((p.d : ℝ) + 2))
              (HRS.Whole.meanEmpirical (A.P.map (A.X u.toNNReal))) ∧
            (∫ x : Euc p.d, jbracket x ^ ((p.d : ℝ) + 2)
              ∂(HRS.Whole.meanEmpirical (A.P.map (A.X u.toNNReal)))) ≤ Cm) := by
  obtain ⟨δtraj, Co, co, hδtraj, hδtrajHalf, hco, htrajectory⟩ :=
    fp81s21_moving_trajectory_fields p
  obtain ⟨δdens, pinf, K, η, gapConst, hδdens, hδdensHalf, hpinf, hη, hη1,
    hgapConst, -, -, hactual, -⟩ := fp81s21_uniform_thermal_package p
  let δ0 : ℝ := min δtraj δdens
  have hδ0 : 0 < δ0 := lt_min hδtraj hδdens
  have hδ0Half : δ0 ≤ 1 / 2 := (min_le_left _ _).trans hδtrajHalf
  refine ⟨δ0, Co, co, pinf, K, hδ0, hδ0Half, hco, hpinf,
    fun δ hδ hδle R N hN A H hH => ?_⟩
  have hδtraj' : δ ≤ δtraj := hδle.trans (min_le_left _ _)
  have hδdens' : δ ≤ δdens := hδle.trans (min_le_right _ _)
  obtain ⟨-, -, -, -, -, -, hround2, hgaussian, -⟩ :=
    htrajectory δ hδ hδtraj' R H hH
  obtain ⟨M, L, hround2⟩ := hround2
  obtain ⟨C₀, c₀, hc₀, hgaussian⟩ := hgaussian
  have hactual' : ∀ u ∈ Set.Icc (0 : ℝ) H,
      HasR2ActualDensity p.s p.β pinf K
        (r26t3_mu R u) (A.P.map (A.X u.toNNReal)) := by
    intro u hu
    have hu0 : 0 ≤ u := hu.1
    have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
    have hmono := HRS.MS.S21A.s21a_cls_mono p.hd p.hs0 hsd p.ha p.hβ R.thermal
      (hle := hδdens') R.admissible R.resulting
    let Rdens : Trajectory p δdens :=
      { ρβ := R.ρβ
        thermal := R.thermal
        ε := R.ε
        ψ := R.ψ
        admissible := hmono.1
        ρ := R.ρ
        resulting := hmono.2 }
    let Adens : Particle Rdens N :=
      { A with initial := by simpa [Rdens, r26t3_Q, r26t3_mu] using A.initial }
    simpa [Rdens, r26t3_mu] using hactual Rdens N hN Adens u hu0
  obtain ⟨Cm, hCm⟩ := HRS.MS.R2Interp.s102_marginal_moment_bound
    p.hd p.hs0 p.hs M L C₀ c₀ p.β pinf K hc₀ p.hβ hpinf
    (Pw := (p.d : ℝ) + 2) (by positivity)
  have hparticle : ∀ u ∈ Set.Icc (0 : ℝ) H,
      Integrable
        (fun x : Euc p.d => jbracket x ^ ((p.d : ℝ) + 2))
        (HRS.Whole.meanEmpirical (A.P.map (A.X u.toNNReal))) ∧
      (∫ x : Euc p.d, jbracket x ^ ((p.d : ℝ) + 2)
        ∂(HRS.Whole.meanEmpirical (A.P.map (A.X u.toNNReal)))) ≤ Cm := by
    intro u hu
    have hρ := hround2 u hu
    have hG := hgaussian u hu
    have hP := hactual' u hu
    have hInt := HRS.MS.R2Interp.s102_marginal_moment
      p.hd p.hs0 p.hs M L C₀ c₀ p.β pinf K hc₀ p.hβ hpinf
      (Pw := (p.d : ℝ) + 2) (by positivity) hρ hG hN hP
    exact ⟨hInt, hCm hρ hG hN hP⟩
  exact ⟨hactual', ⟨Cm, hparticle⟩⟩

#print axioms HRS.Fp81.S21.fp81s21_moving_trajectory_fields
#print axioms HRS.Fp81.S21.fp81s21_moving_particle_fields

end HRS.Fp81.S21
