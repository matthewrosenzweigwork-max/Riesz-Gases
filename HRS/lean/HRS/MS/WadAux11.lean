import HRS.MS.WadAux1
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# S8.3, packet D2 (part 6): the Lebesgue density of `stdGaussian` and the Cameron-Martin identity

* `s83_std_density`: `stdGaussian (Euc d) = volume.withDensity (ψ)`, `ψ(z) = (2π)^{-d/2} e^{-‖z‖²/2}`.
* `s83_cm_map`: `(stdGaussian).map (· + k) = (stdGaussian).withDensity (E_k)`, `E_k(u) = exp(⟨u,k⟩ - ‖k‖²/2)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped ENNReal ComplexConjugate RealInnerProductSpace

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

/-- The Gaussian density. -/
def s83_psi (d : ℕ) (z : Euc d) : ℝ := (2 * Real.pi) ^ (-(d : ℝ) / 2) * Real.exp (-(‖z‖ ^ 2) / 2)

theorem s83_psi_pos (z : Euc d) : 0 < s83_psi d z := by
  unfold s83_psi; positivity

theorem s83_psi_meas : Measurable (s83_psi d) := by
  unfold s83_psi; fun_prop

theorem s83_charFun_psi (t : Euc d) :
    charFun (volume.withDensity fun z : Euc d => ENNReal.ofReal (s83_psi d z)) t =
      Complex.exp (-(‖t‖ ^ 2 : ℝ) / 2) := by
  rw [charFun_apply, integral_withDensity_eq_integral_toReal_smul (by
      have := s83_psi_meas (d := d); fun_prop) (Eventually.of_forall fun z => ENNReal.ofReal_lt_top)]
  have key := GaussianFourier.integral_cexp_neg_mul_sq_norm_add_of_euclideanSpace (ι := Fin d)
    (b := (1/2 : ℂ)) (by norm_num) Complex.I t
  have e1 : ∀ x : Euc d, (ENNReal.ofReal (s83_psi d x)).toReal • cexp (↑⟪x, t⟫ * I) =
      (((2 * Real.pi) ^ (-(d : ℝ) / 2) : ℝ) : ℂ) *
        cexp (-(1/2 : ℂ) * (‖x‖ : ℂ) ^ 2 + I * (⟪t, x⟫ : ℝ)) := by
    intro x
    rw [ENNReal.toReal_ofReal (s83_psi_pos x).le, Complex.real_smul, real_inner_comm]
    unfold s83_psi
    push_cast
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  simp only [e1]
  rw [integral_const_mul, key]
  have hp : (0 : ℝ) < 2 * Real.pi := by positivity
  have hc : ((Real.pi : ℂ) / (1/2 : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  have e2 : (((2 * Real.pi : ℝ) : ℂ)) ^ (((Fintype.card (Fin d) : ℕ) : ℂ) / 2) =
      (((2 * Real.pi) ^ ((d : ℝ) / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hp.le]; push_cast; simp
  rw [hc, e2, ← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add hp]
  have h0 : -(d : ℝ) / 2 + (d : ℝ) / 2 = 0 := by ring
  rw [h0, Real.rpow_zero, Complex.ofReal_one, one_mul]
  congr 1
  rw [Complex.I_sq]
  push_cast
  ring

/-- `stdGaussian` has the Lebesgue density `ψ`. -/
theorem s83_std_density :
    stdGaussian (Euc d) = volume.withDensity fun z : Euc d => ENNReal.ofReal (s83_psi d z) := by
  have hfin : IsFiniteMeasure (volume.withDensity fun z : Euc d => ENNReal.ofReal (s83_psi d z)) := by
    refine ⟨?_⟩
    have h0 := s83_charFun_psi (d := d) 0
    rw [charFun_zero] at h0
    have h00 : Complex.exp (-((‖(0 : Euc d)‖ ^ 2 : ℝ) : ℂ) / 2) = 1 := by simp
    rw [h00] at h0
    have h1 : (volume.withDensity fun z : Euc d => ENNReal.ofReal (s83_psi d z)).real Set.univ = 1 := by
      exact_mod_cast h0
    by_contra hcon
    have : (volume.withDensity fun z : Euc d => ENNReal.ofReal (s83_psi d z)) Set.univ = ⊤ := by
      simpa using hcon
    rw [Measure.real, this] at h1
    simp at h1
  refine Measure.ext_of_charFun ?_
  ext t
  rw [s83_charFun_psi, charFun_stdGaussian]
  push_cast
  rfl

/-- The Cameron-Martin density `E_k(u) = exp(⟨u,k⟩ - ‖k‖²/2)`. -/
def s83_E (k u : Euc d) : ℝ := Real.exp (⟪u, k⟫ - ‖k‖ ^ 2 / 2)

theorem s83_E_pos (k u : Euc d) : 0 < s83_E k u := Real.exp_pos _

theorem s83_E_meas (k : Euc d) : Measurable (s83_E k) := by
  unfold s83_E; fun_prop

theorem s83_psi_mul_E (k v : Euc d) : s83_psi d v * s83_E k v = s83_psi d (v - k) := by
  unfold s83_psi s83_E
  rw [mul_assoc, ← Real.exp_add, norm_sub_sq_real]
  congr 2
  ring

/-- **Cameron-Martin**: the translate of the standard Gaussian has density `E_k` w.r.t. it. -/
theorem s83_cm_map (k : Euc d) :
    (stdGaussian (Euc d)).map (fun u => u + k) =
      (stdGaussian (Euc d)).withDensity (fun u => ENNReal.ofReal (s83_E k u)) := by
  have hψ : Measurable fun z : Euc d => ENNReal.ofReal (s83_psi d z) :=
    ENNReal.measurable_ofReal.comp s83_psi_meas
  have hE : Measurable fun u : Euc d => ENNReal.ofReal (s83_E k u) :=
    ENNReal.measurable_ofReal.comp (s83_E_meas k)
  have hψk : Measurable fun z : Euc d => ENNReal.ofReal (s83_psi d (z - k)) :=
    ENNReal.measurable_ofReal.comp (s83_psi_meas.comp (measurable_sub_const k))
  have h1 : (volume.withDensity fun z : Euc d => ENNReal.ofReal (s83_psi d z)).map (fun u => u + k) =
      volume.withDensity fun z : Euc d => ENNReal.ofReal (s83_psi d (z - k)) := by
    ext s hs
    rw [Measure.map_apply (measurable_add_const k) hs, withDensity_apply _ (measurable_add_const k hs),
      withDensity_apply _ hs, ← lintegral_indicator (measurable_add_const k hs),
      ← lintegral_indicator hs]
    have : ∀ u : Euc d, ((fun u => u + k) ⁻¹' s).indicator
        (fun z : Euc d => ENNReal.ofReal (s83_psi d z)) u =
        s.indicator (fun z : Euc d => ENNReal.ofReal (s83_psi d (z - k))) (u + k) := by
      intro u
      by_cases hu : u + k ∈ s
      · rw [Set.indicator_of_mem (show u ∈ (fun u => u + k) ⁻¹' s from hu), Set.indicator_of_mem hu]
        simp
      · rw [Set.indicator_of_notMem (show u ∉ (fun u => u + k) ⁻¹' s from hu), Set.indicator_of_notMem hu]
    simp only [this]
    exact lintegral_add_right_eq_self (fun v => s.indicator (fun z : Euc d =>
      ENNReal.ofReal (s83_psi d (z - k))) v) k
  have h2 : (volume.withDensity fun z : Euc d => ENNReal.ofReal (s83_psi d z)).withDensity
      (fun u => ENNReal.ofReal (s83_E k u)) =
      volume.withDensity fun z : Euc d => ENNReal.ofReal (s83_psi d (z - k)) := by
    rw [← withDensity_mul _ hψ hE]
    congr 1
    funext v
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (s83_psi_pos v).le, s83_psi_mul_E]
  rw [s83_std_density, h1, h2]

/-- Cameron-Martin at the level of the Bochner integral (continuous test functions). -/
theorem s83_cm_integral {F : Euc d → ℝ} (hF : Continuous F) (k : Euc d) :
    ∫ u, F (u + k) ∂(stdGaussian (Euc d)) = ∫ u, s83_E k u * F u ∂(stdGaussian (Euc d)) := by
  have h := s83_cm_map (d := d) k
  have e1 : ∫ u, F u ∂((stdGaussian (Euc d)).map (fun u => u + k)) =
      ∫ u, F (u + k) ∂(stdGaussian (Euc d)) :=
    integral_map (measurable_add_const k).aemeasurable (hF.aestronglyMeasurable)
  have hE : Measurable fun u : Euc d => ENNReal.ofReal (s83_E k u) :=
    ENNReal.measurable_ofReal.comp (s83_E_meas k)
  have e2 : ∫ u, F u ∂((stdGaussian (Euc d)).withDensity (fun u => ENNReal.ofReal (s83_E k u))) =
      ∫ u, s83_E k u * F u ∂(stdGaussian (Euc d)) := by
    rw [integral_withDensity_eq_integral_toReal_smul hE (Eventually.of_forall fun u => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [ENNReal.toReal_ofReal (s83_E_pos k u).le, smul_eq_mul]
  rw [← e1, ← e2, h]

/-- Cameron-Martin for nonnegative functions (`lintegral` form). -/
theorem s83_cm_lintegral {F : Euc d → ℝ≥0∞} (hF : Measurable F) (k : Euc d) :
    ∫⁻ u, F (u + k) ∂(stdGaussian (Euc d)) =
      ∫⁻ u, ENNReal.ofReal (s83_E k u) * F u ∂(stdGaussian (Euc d)) := by
  have h := s83_cm_map (d := d) k
  have hE : Measurable fun u : Euc d => ENNReal.ofReal (s83_E k u) :=
    ENNReal.measurable_ofReal.comp (s83_E_meas k)
  have e1 : ∫⁻ u, F u ∂((stdGaussian (Euc d)).map (fun u => u + k)) =
      ∫⁻ u, F (u + k) ∂(stdGaussian (Euc d)) :=
    lintegral_map hF (measurable_add_const k)
  rw [← e1, h, lintegral_withDensity_eq_lintegral_mul _ hE hF]
  rfl

theorem s83_lintegral_E (k : Euc d) :
    ∫⁻ u, ENNReal.ofReal (s83_E k u) ∂(stdGaussian (Euc d)) = 1 := by
  have := s83_cm_lintegral (d := d) (F := fun _ => 1) measurable_const k
  simpa using this.symm

theorem s83_integrable_E (k : Euc d) : Integrable (s83_E k) (stdGaussian (Euc d)) := by
  rw [← lintegral_ofReal_ne_top_iff_integrable (s83_E_meas k).aestronglyMeasurable
    (Eventually.of_forall fun u => (s83_E_pos k u).le)]
  rw [s83_lintegral_E]; exact ENNReal.one_ne_top

theorem s83_integral_E (k : Euc d) : ∫ u, s83_E k u ∂(stdGaussian (Euc d)) = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun u => (s83_E_pos k u).le)
    (s83_E_meas k).aestronglyMeasurable, s83_lintegral_E]
  simp

theorem s83_E_shift (k u : Euc d) : s83_E k (u + k) = s83_E k u * Real.exp (‖k‖ ^ 2) := by
  unfold s83_E
  rw [← Real.exp_add, inner_add_left, real_inner_self_eq_norm_sq]
  congr 1
  ring

theorem s83_lintegral_E_sq (k : Euc d) :
    ∫⁻ u, ENNReal.ofReal (s83_E k u) * ENNReal.ofReal (s83_E k u) ∂(stdGaussian (Euc d)) =
      ENNReal.ofReal (Real.exp (‖k‖ ^ 2)) := by
  have := s83_cm_lintegral (d := d) (F := fun u => ENNReal.ofReal (s83_E k u))
    (ENNReal.measurable_ofReal.comp (s83_E_meas k)) k
  rw [← this]
  simp only [s83_E_shift]
  have : ∀ u : Euc d, ENNReal.ofReal (s83_E k u * Real.exp (‖k‖ ^ 2)) =
      ENNReal.ofReal (s83_E k u) * ENNReal.ofReal (Real.exp (‖k‖ ^ 2)) := fun u =>
    ENNReal.ofReal_mul (s83_E_pos k u).le
  simp only [this]
  rw [lintegral_mul_const (f := fun u : Euc d => ENNReal.ofReal (s83_E k u)) _
    (ENNReal.measurable_ofReal.comp (s83_E_meas k)), s83_lintegral_E, one_mul]

theorem s83_integrable_E_sq (k : Euc d) :
    Integrable (fun u => s83_E k u ^ 2) (stdGaussian (Euc d)) := by
  have hm : Measurable fun u : Euc d => s83_E k u ^ 2 := (s83_E_meas k).pow_const 2
  rw [← lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
    (Eventually.of_forall fun u => by positivity)]
  have : ∀ u : Euc d, ENNReal.ofReal (s83_E k u ^ 2) =
      ENNReal.ofReal (s83_E k u) * ENNReal.ofReal (s83_E k u) := fun u => by
    rw [pow_two, ENNReal.ofReal_mul (s83_E_pos k u).le]
  simp only [this]
  rw [s83_lintegral_E_sq]; exact ENNReal.ofReal_ne_top

theorem s83_integral_E_sq (k : Euc d) :
    ∫ u, s83_E k u ^ 2 ∂(stdGaussian (Euc d)) = Real.exp (‖k‖ ^ 2) := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun u => by positivity)
    ((s83_E_meas k).pow_const 2).aestronglyMeasurable]
  have : ∀ u : Euc d, ENNReal.ofReal (s83_E k u ^ 2) =
      ENNReal.ofReal (s83_E k u) * ENNReal.ofReal (s83_E k u) := fun u => by
    rw [pow_two, ENNReal.ofReal_mul (s83_E_pos k u).le]
  simp only [this]
  rw [s83_lintegral_E_sq, ENNReal.toReal_ofReal (Real.exp_pos _).le]

/-- `∫ (E_k - 1)² dγ = e^{‖k‖²} - 1`. -/
theorem s83_integral_E_sub_one_sq (k : Euc d) :
    ∫ u, (s83_E k u - 1) ^ 2 ∂(stdGaussian (Euc d)) = Real.exp (‖k‖ ^ 2) - 1 := by
  have h1 := s83_integrable_E k
  have h2 := s83_integrable_E_sq k
  have e : ∀ u : Euc d, (s83_E k u - 1) ^ 2 = s83_E k u ^ 2 - 2 * s83_E k u + 1 := fun u => by ring
  simp only [e]
  have hI : Integrable (fun u : Euc d => s83_E k u ^ 2 - 2 * s83_E k u) (stdGaussian (Euc d)) :=
    h2.sub (h1.const_mul 2)
  rw [integral_add hI (integrable_const _), integral_sub h2 (h1.const_mul 2),
    integral_const_mul, s83_integral_E_sq, s83_integral_E, integral_const]
  simp
  ring

end HRS.MS.Wad
