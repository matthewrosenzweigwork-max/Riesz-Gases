import HRS.PDE.MovCAux3

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem movc_conv_abs_le {k f : Torus d → ℝ} (hk : Integrable k) {C : ℝ}
    (hC : ∀ y, |f y| ≤ C) (x : Torus d) :
    |convFun k f x| ≤ C * ∫ z : Torus d, |k z| := by
  unfold convFun
  have h1 : |∫ y : Torus d, k (x - y) * f y| ≤ ∫ y : Torus d, |k (x - y) * f y| := by
    have := norm_integral_le_integral_norm (μ := (volume : Measure (Torus d)))
      (fun y : Torus d => k (x - y) * f y)
    simpa [Real.norm_eq_abs] using this
  refine h1.trans ?_
  have hshift : ∫ y : Torus d, |k (x - y)| = ∫ z : Torus d, |k z| :=
    integral_sub_left_eq_self (fun z : Torus d => |k z|) volume x
  rw [← hshift, ← integral_const_mul]
  by_cases hint : Integrable (fun y : Torus d => |k (x - y) * f y|)
  · refine integral_mono hint ((hk.abs.comp_sub_left x).const_mul C) fun y => ?_
    show |k (x - y) * f y| ≤ C * |k (x - y)|
    rw [abs_mul]
    calc _ ≤ |k (x - y)| * C := mul_le_mul_of_nonneg_left (hC y) (abs_nonneg _)
      _ = _ := mul_comm _ _
  · rw [integral_undef hint]
    exact integral_nonneg fun y => mul_nonneg ((abs_nonneg _).trans (hC y)) (abs_nonneg _)


theorem movc_conv_integral {k f : Torus d → ℝ} (hf : Measurable f) (hf0 : ∀ y, 0 ≤ f y) (x : Torus d) :
    ∫ y, k (x - y) ∂(withDensityReal f) = convFun k f x := by
  unfold withDensityReal convFun
  rw [integral_withDensity_eq_integral_toReal_smul₀ (f := fun y => ENNReal.ofReal (f y))
    (ENNReal.measurable_ofReal.comp hf).aemeasurable (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp [ENNReal.toReal_ofReal (hf0 y), mul_comm]

theorem movc_energy_eq (k : Torus d → ℝ) {f : Torus d → ℝ} (hf : Measurable f) (hf0 : ∀ y, 0 ≤ f y)
    (X : Config d N) :
    modulatedEnergyKernel k X (withDensityReal f) =
      (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, k (X i - X j)
        - (1 / (N : ℝ)) * ∑ i, convFun k f (X i)
        + (1 / 2) * ∫ x, convFun k f x ∂(withDensityReal f) := by
  unfold modulatedEnergyKernel modulatedEnergy
  simp_rw [movc_conv_integral hf hf0]

theorem movc_gReg_tendsto_pt {s : ℝ} {M : ℕ → ℝ} (hM : Tendsto M atTop atTop) {z : Torus d} (hz : z ≠ 0) :
    Tendsto (fun n => b15c_gReg d s (M n) z) atTop (𝓝 (periodicRiesz d s z)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hM.eventually (b15c_gReg_eventuallyEq (d := d) s hz)] with n hn
  exact hn.symm


theorem movc_conv_bound (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {f : Torus d → ℝ} {C : ℝ}
    (hC : ∀ y, |f y| ≤ C) :
    ∃ B Cb : ℝ, 0 ≤ B ∧ (∀ z : Torus d, -B ≤ periodicRiesz d s z) ∧ 0 ≤ Cb ∧
      ∀ x, |convFun (periodicRiesz d s) f x| ≤ Cb ∧
        ∀ M : ℝ, 0 ≤ M → |convFun (b15c_gReg d s M) f x| ≤ Cb := by
  obtain ⟨B, hB0, hB⟩ := movc_riesz_lower hd hs0 hsd
  have hgi : Integrable (periodicRiesz d s) := CoercAux.integrable_periodicRiesz_one hd hs0 hsd
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC (0 : Torus d) |> fun h => h)
  have hI0 : 0 ≤ ∫ z : Torus d, |periodicRiesz d s z| := integral_nonneg fun z => abs_nonneg _
  refine ⟨B, C * ((∫ z : Torus d, |periodicRiesz d s z|) + B), hB0, hB,
    mul_nonneg hC0 (by linarith), fun x => ⟨?_, fun M hM => ?_⟩⟩
  · refine (movc_conv_abs_le hgi hC x).trans ?_
    exact mul_le_mul_of_nonneg_left (by linarith) hC0
  · have hgc := movc_gReg_measurable hd hs0 hsd M
    have hgM : Integrable (b15c_gReg d s M) := hgc.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
    refine (movc_conv_abs_le hgM hC x).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hC0
    have hz : (volume : Measure (Torus d)) {0} = 0 := volume_singleton_torus hd 0
    have hae : ∀ᵐ z : Torus d ∂volume, z ≠ 0 := by
      rw [ae_iff]; simpa using hz
    have : ∫ z : Torus d, |b15c_gReg d s M z| ≤ ∫ z : Torus d, (|periodicRiesz d s z| + B) := by
      refine integral_mono_ae hgM.abs (hgi.abs.add (integrable_const B)) ?_
      filter_upwards [hae] with z hz
      have h1 := b15c_gReg_le s M hz
      have h2 := b15c_gReg_ge s hB0 hM hB z
      show |b15c_gReg d s M z| ≤ |periodicRiesz d s z| + B
      rw [abs_le]
      constructor
      · linarith [abs_nonneg (periodicRiesz d s z)]
      · linarith [le_abs_self (periodicRiesz d s z)]
    rw [integral_add hgi.abs (integrable_const B)] at this
    simpa using this

end HRS
