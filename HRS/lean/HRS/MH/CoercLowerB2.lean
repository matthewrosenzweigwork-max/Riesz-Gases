import HRS.Whole.AppendixA
import HRS.MH.CoercLowerDefs
import HRS.MH.CoercLowerB1

/-!
# CoercLower B2: `Qform` algebra and domination packets (P03a-d, P04a-d)

Proofs of the statements in `HRS/MH/CoercLowerSpec.lean`, copied verbatim.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace HRS.MH.CoercLower


variable {d N : ℕ}

/-- Auxiliary: convolution with a constant kernel. -/
theorem clb2_convFun_const (c : ℝ) {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) (x : Euc d) :
    HRS.Whole.convFun (fun _ => c) ρ x = c := by
  show ∫ y, c * ρ y = c
  rw [integral_const_mul, hρ.integral_one, mul_one]

/-- Auxiliary: energy of a constant kernel. -/
theorem clb2_energyDens_const (c : ℝ) {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) :
    energyDens (fun _ => c) ρ = c := by
  unfold energyDens
  simp only [clb2_convFun_const c hρ]
  rw [integral_mul_const, hρ.integral_one, one_mul]

/-- Auxiliary: convolution commutes with scalar multiples of the kernel. -/
theorem clb2_convFun_smul (c : ℝ) (h ρ : Euc d → ℝ) (x : Euc d) :
    HRS.Whole.convFun (fun z => c * h z) ρ x = c * HRS.Whole.convFun h ρ x := by
  unfold HRS.Whole.convFun
  rw [← integral_const_mul]
  congr 1
  funext y
  ring

/-- Auxiliary: energy commutes with scalar multiples of the kernel. -/
theorem clb2_energyDens_smul (c : ℝ) (h ρ : Euc d → ℝ) :
    energyDens (fun z => c * h z) ρ = c * energyDens h ρ := by
  unfold energyDens
  simp only [clb2_convFun_smul c h ρ]
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

/-- Auxiliary: convolution is additive in the kernel (integrability of both pieces at `x`). -/
theorem clb2_convFun_add (h₁ h₂ ρ : Euc d → ℝ) (x : Euc d)
    (i₁ : Integrable (fun y => h₁ (x - y) * ρ y)) (i₂ : Integrable (fun y => h₂ (x - y) * ρ y)) :
    HRS.Whole.convFun (fun z => h₁ z + h₂ z) ρ x =
      HRS.Whole.convFun h₁ ρ x + HRS.Whole.convFun h₂ ρ x := by
  unfold HRS.Whole.convFun
  simp only [add_mul]
  exact integral_add i₁ i₂

/-- Auxiliary: energy is additive in the kernel. -/
theorem clb2_energyDens_add (h₁ h₂ ρ : Euc d → ℝ)
    (i₁ : ∀ x, Integrable (fun y => h₁ (x - y) * ρ y))
    (i₂ : ∀ x, Integrable (fun y => h₂ (x - y) * ρ y))
    (e₁ : Integrable (fun x => ρ x * HRS.Whole.convFun h₁ ρ x))
    (e₂ : Integrable (fun x => ρ x * HRS.Whole.convFun h₂ ρ x)) :
    energyDens (fun z => h₁ z + h₂ z) ρ = energyDens h₁ ρ + energyDens h₂ ρ := by
  have hc : ∀ x, HRS.Whole.convFun (fun z => h₁ z + h₂ z) ρ x =
      HRS.Whole.convFun h₁ ρ x + HRS.Whole.convFun h₂ ρ x :=
    fun x => clb2_convFun_add h₁ h₂ ρ x (i₁ x) (i₂ x)
  unfold energyDens
  simp only [hc, mul_add]
  exact integral_add e₁ e₂

/-- [P03a] -/
theorem Qform_smul (c : ℝ) (h : Euc d → ℝ) (X : HRS.Whole.EucConfig d N) (ρ : Euc d → ℝ) :
    Qform (fun z => c * h z) X ρ = c * Qform h X ρ := by
  unfold Qform
  simp only [clb2_convFun_smul, clb2_energyDens_smul, ← Finset.mul_sum]
  ring

/-- [P03b] Mass-zero cancellation. -/
theorem Qform_const (c : ℝ) {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) (hN : 1 ≤ N)
    (X : HRS.Whole.EucConfig d N) : Qform (fun _ => c) X ρ = 0 := by
  have hN0 : (N : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    positivity
  unfold Qform
  simp only [clb2_convFun_const c hρ, clb2_energyDens_const c hρ, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- [P03c] -/
theorem Qform_add (h₁ h₂ : Euc d → ℝ) (X : HRS.Whole.EucConfig d N) (ρ : Euc d → ℝ)
    (i₁ : ∀ x, Integrable (fun y => h₁ (x - y) * ρ y))
    (i₂ : ∀ x, Integrable (fun y => h₂ (x - y) * ρ y))
    (e₁ : Integrable (fun x => ρ x * HRS.Whole.convFun h₁ ρ x))
    (e₂ : Integrable (fun x => ρ x * HRS.Whole.convFun h₂ ρ x)) :
    Qform (fun z => h₁ z + h₂ z) X ρ = Qform h₁ X ρ + Qform h₂ X ρ := by
  have hc : ∀ x, HRS.Whole.convFun (fun z => h₁ z + h₂ z) ρ x =
      HRS.Whole.convFun h₁ ρ x + HRS.Whole.convFun h₂ ρ x :=
    fun x => clb2_convFun_add h₁ h₂ ρ x (i₁ x) (i₂ x)
  have he := clb2_energyDens_add h₁ h₂ ρ i₁ i₂ e₁ e₂
  unfold Qform
  rw [he]
  simp only [hc, Finset.sum_add_distrib]
  ring

/-- [P03d] -/
theorem Qform_sub_const (h : Euc d → ℝ) (c : ℝ) {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ)
    (hN : 1 ≤ N) (X : HRS.Whole.EucConfig d N)
    (i₁ : ∀ x, Integrable (fun y => h (x - y) * ρ y))
    (e₁ : Integrable (fun x => ρ x * HRS.Whole.convFun h ρ x)) :
    Qform (fun z => h z - c) X ρ = Qform h X ρ := by
  have hfun : (fun z => h z - c) = (fun z => h z + (fun _ : Euc d => -c) z) := by
    funext z
    ring
  have i₂ : ∀ x, Integrable (fun y => (fun _ : Euc d => -c) (x - y) * ρ y) := fun x =>
    (isProbDensity_integrable hρ).const_mul (-c)
  have e₂ : Integrable (fun x => ρ x * HRS.Whole.convFun (fun _ : Euc d => -c) ρ x) := by
    have : (fun x => ρ x * HRS.Whole.convFun (fun _ : Euc d => -c) ρ x) =
        fun x => ρ x * (-c) := by
      funext x
      rw [clb2_convFun_const (-c) hρ x]
    rw [this]
    exact (isProbDensity_integrable hρ).mul_const (-c)
  have key := Qform_add h (fun _ => -c) X ρ i₁ i₂ e₁ e₂
  have hc0 := Qform_const (-c) hρ hN X
  rw [hfun, key, hc0, add_zero]

/-- Auxiliary: `DomK` for a constant kernel is immediate. -/
theorem clb2_log_le (x y : Euc d) :
    0 ≤ Real.log (2 + ‖x - y‖) ∧
      Real.log (2 + ‖x - y‖) ≤ Real.log (2 + ‖x‖) + Real.log (2 + ‖y‖) := by
  have hx : 0 < 2 + ‖x‖ := by positivity
  have hy : 0 < 2 + ‖y‖ := by positivity
  have hxy : 0 < 2 + ‖x - y‖ := by positivity
  refine ⟨Real.log_nonneg (by linarith [norm_nonneg (x - y)]), ?_⟩
  rw [← Real.log_mul hx.ne' hy.ne']
  apply Real.log_le_log hxy
  have := norm_sub_le x y
  nlinarith [norm_nonneg x, norm_nonneg y, mul_nonneg (norm_nonneg x) (norm_nonneg y)]

/-- Auxiliary: measurability of the convolution of a measurable kernel with a measurable density. -/
theorem clb2_meas_convFun {h ρ : Euc d → ℝ} (hh : Measurable h) (hρ : Measurable ρ) :
    Measurable (HRS.Whole.convFun h ρ) := by
  have hF : Measurable (fun p : Euc d × Euc d => h (p.1 - p.2) * ρ p.2) :=
    (hh.comp (measurable_fst.sub measurable_snd)).mul (hρ.comp measurable_snd)
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

/-- Auxiliary: measurability of `z ↦ c + log(2+‖z‖)`. -/
theorem clb2_meas_K (c : ℝ) : Measurable (fun z : Euc d => c + Real.log (2 + ‖z‖)) := by
  fun_prop

/-- [P04a] -/
theorem domK_const (c : ℝ) {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) : DomK (fun _ => c) ρ := by
  refine ⟨fun x => ?_, ?_⟩
  · exact (isProbDensity_integrable hρ).const_mul c
  · have : (fun x => ρ x * HRS.Whole.convFun (fun _ => c) ρ x) = fun x => ρ x * c := by
      funext x
      rw [clb2_convFun_const c hρ x]
    rw [this]
    exact (isProbDensity_integrable hρ).mul_const c

/-- [P04b] Log-moment kernel: `K(z) = c + log(2+‖z‖)`. -/
theorem domK_log {c : ℝ} (hc : 0 ≤ c) {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ)
    (hlog : Integrable (fun y : Euc d => Real.log (2 + ‖y‖) * ρ y)) :
    DomK (fun z => c + Real.log (2 + ‖z‖)) ρ := by
  have hρi : Integrable ρ := isProbDensity_integrable hρ
  have hI : ∀ x, Integrable (fun y => (c + Real.log (2 + ‖x - y‖)) * ρ y) := by
    intro x
    have hg : Integrable (fun y => (c + Real.log (2 + ‖x‖)) * ρ y + Real.log (2 + ‖y‖) * ρ y) :=
      (hρi.const_mul _).add hlog
    refine hg.mono' ?_ ?_
    · have hm : Measurable (fun y : Euc d => (c + Real.log (2 + ‖x - y‖)) * ρ y) :=
        ((clb2_meas_K c).comp (measurable_const.sub measurable_id : Measurable fun y : Euc d => x - y)).mul
          hρ.measurable
      exact hm.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun y => ?_
      obtain ⟨h0, h1⟩ := clb2_log_le x y
      have hρy := hρ.nonneg y
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith) hρy)]
      nlinarith [mul_nonneg (sub_nonneg.mpr h1) hρy]
  -- pointwise upper bound on the convolution
  have hup : ∀ x, HRS.Whole.convFun (fun z => c + Real.log (2 + ‖z‖)) ρ x ≤
      (c + Real.log (2 + ‖x‖)) + ∫ y, Real.log (2 + ‖y‖) * ρ y := by
    intro x
    have hg : Integrable (fun y => (c + Real.log (2 + ‖x‖)) * ρ y + Real.log (2 + ‖y‖) * ρ y) :=
      (hρi.const_mul _).add hlog
    have hm : ∫ y, ((c + Real.log (2 + ‖x‖)) * ρ y + Real.log (2 + ‖y‖) * ρ y) =
        (c + Real.log (2 + ‖x‖)) + ∫ y, Real.log (2 + ‖y‖) * ρ y := by
      rw [integral_add (hρi.const_mul _) hlog, integral_const_mul, hρ.integral_one, mul_one]
    rw [← hm]
    unfold HRS.Whole.convFun
    refine integral_mono (hI x) hg (fun y => ?_)
    dsimp only
    obtain ⟨h0, h1⟩ := clb2_log_le x y
    have hρy := hρ.nonneg y
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) hρy]
  have hlo : ∀ x, 0 ≤ HRS.Whole.convFun (fun z => c + Real.log (2 + ‖z‖)) ρ x := by
    intro x
    refine integral_nonneg (fun y => ?_)
    dsimp only
    obtain ⟨h0, _⟩ := clb2_log_le x y
    exact mul_nonneg (by linarith) (hρ.nonneg y)
  refine ⟨fun x => hI x, ?_⟩
  have hmeas : AEStronglyMeasurable (fun x => ρ x * HRS.Whole.convFun
      (fun z => c + Real.log (2 + ‖z‖)) ρ x) volume :=
    (hρ.measurable.mul (clb2_meas_convFun (clb2_meas_K c) hρ.measurable)).aestronglyMeasurable
  refine Integrable.mono' ((hρi.const_mul (c + ∫ y, Real.log (2 + ‖y‖) * ρ y)).add hlog) hmeas ?_
  refine Filter.Eventually.of_forall fun x => ?_
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hρ.nonneg x) (hlo x))]
  nlinarith [mul_le_mul_of_nonneg_left (hup x) (hρ.nonneg x)]

/-- [P04c] Measure form versus density form of the log-moment hypothesis. -/
theorem integrable_log_moment_iff {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) :
    Integrable (fun x : Euc d => Real.log (2 + ‖x‖)) (HRS.Whole.withDensityReal ρ) ↔
      Integrable (fun y : Euc d => Real.log (2 + ‖y‖) * ρ y) := by
  unfold HRS.Whole.withDensityReal
  rw [integrable_withDensity_iff_integrable_smul' hρ.measurable.ennreal_ofReal
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  have hfun : (fun x : Euc d => (ENNReal.ofReal (ρ x)).toReal • Real.log (2 + ‖x‖)) =
      fun x => Real.log (2 + ‖x‖) * ρ x := by
    funext x
    rw [smul_eq_mul, ENNReal.toReal_ofReal (hρ.nonneg x), mul_comm]
  rw [hfun]

/-- [P04d] Integrability of the convolution pieces for a kernel dominated by `K`. -/
theorem integrable_of_domK {h K ρ : Euc d → ℝ} (hh : Measurable h) (hρ : HRS.Whole.IsProbDensity ρ)
    (hb : ∀ z, |h z| ≤ K z) (hK : DomK K ρ) :
    (∀ x, Integrable (fun y => h (x - y) * ρ y)) ∧
      Integrable (fun x => ρ x * HRS.Whole.convFun h ρ x) := by
  have hI : ∀ x, Integrable (fun y => h (x - y) * ρ y) := by
    intro x
    refine (hK.1 x).mono' ?_ ?_
    · exact ((hh.comp (measurable_const.sub measurable_id)).mul hρ.measurable).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun y => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ.nonneg y)]
      exact mul_le_mul_of_nonneg_right (hb (x - y)) (hρ.nonneg y)
  refine ⟨hI, ?_⟩
  refine hK.2.mono' ?_ ?_
  · exact (hρ.measurable.mul (clb2_meas_convFun hh hρ.measurable)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ.nonneg x)]
    apply mul_le_mul_of_nonneg_left _ (hρ.nonneg x)
    have h1 : |HRS.Whole.convFun h ρ x| ≤ ∫ y, |h (x - y) * ρ y| :=
      abs_integral_le_integral_abs
    have h2 : ∫ y, |h (x - y) * ρ y| ≤ ∫ y, K (x - y) * ρ y := by
      refine integral_mono (hI x).abs (hK.1 x) (fun y => ?_)
      rw [abs_mul, abs_of_nonneg (hρ.nonneg y)]
      exact mul_le_mul_of_nonneg_right (hb (x - y)) (hρ.nonneg y)
    exact h1.trans h2

end HRS.MH.CoercLower
