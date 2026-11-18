import HRS.MS.Fp81S21GaussG4U5Slice
import HRS.MS.Fp81S21GaussG4U5Tonelli
import HRS.MS.Fp81S21GaussG4U5Meas

/-! Restrict the generator energy budget to earlier times. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2WinErr HRS.MS.R2WinOrbNL

theorem fp81s21_g4_kernel_energy
    (p : Parameters) {δ H v q B : ℝ} (R : Trajectory p δ)
    (hterm : S104bTermRegGen p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁)
    {f : Euc p.d → ℝ} (hf : IsR2DualCombo (wholeSpaceIndex p.d : ℝ) f)
    (V : ℝ × ℝ → Euc p.d → Euc p.d)
    (hV : Measurable (Function.uncurry V))
    (hVe : ∀ r q, 0 ≤ r → r ≤ q → q ≤ H → ∀ x,
      V (r, q) x = gradient (r26t3_U R r q
        (generatorW (r26t3_coeff R) q f)) x)
    (hv : 0 ≤ v) (hvq : v ≤ q) (hqH : q ≤ H)
    (hE : IntegrableOn (fun r => ∫ x, ‖gradient (r26t3_U R r q
      (generatorW (r26t3_coeff R) q f)) x‖^2
      ∂HRS.Whole.withDensityReal R.ρβ) (Icc (0 : ℝ) q))
    (hB : (∫ r in Icc (0 : ℝ) q, ∫ x, ‖gradient (r26t3_U R r q
      (generatorW (r26t3_coeff R) q f)) x‖^2
      ∂HRS.Whole.withDensityReal R.ρβ) ≤ B) :
    (∫⁻ z, ENNReal.ofReal (‖V (z.1, q) z.2‖^2)
      ∂((volume.restrict (Icc (0 : ℝ) v)).prod (HRS.Whole.withDensityReal R.ρβ))) ≤
      ENNReal.ofReal B := by
  let μ := HRS.Whole.withDensityReal R.ρβ
  letI : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  let F : ℝ × Euc p.d → ℝ := fun z => ‖V (z.1, q) z.2‖^2
  have hFm : Measurable F := by
    exact (hV.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)).norm.pow_const 2
  have hEq : ∀ r ∈ Icc (0 : ℝ) q, ∀ x,
      F (r, x) = ‖gradient (r26t3_U R r q
        (generatorW (r26t3_coeff R) q f)) x‖^2 := by
    intro r hr x
    dsimp [F]
    rw [hVe r q hr.1 hr.2 hqH x]
  have hx : ∀ r ∈ Icc (0 : ℝ) q, Integrable (fun x => F (r, x)) μ := by
    intro r hr
    apply (fp81s21_g4_generator_gradient_slice p R hterm hf (hv.trans hvq) r hr).congr
    exact Filter.Eventually.of_forall fun x => (hEq r hr x).symm
  have hrow : ∀ r ∈ Icc (0 : ℝ) q,
      (∫ x, F (r, x) ∂μ) = ∫ x, ‖gradient (r26t3_U R r q
        (generatorW (r26t3_coeff R) q f)) x‖^2 ∂μ := by
    intro r hr
    exact integral_congr_ae (Filter.Eventually.of_forall (hEq r hr))
  have hae : ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) q)), r ∈ Icc (0 : ℝ) q :=
    ae_restrict_mem measurableSet_Icc
  have hr : IntegrableOn (fun r => ∫ x, F (r, x) ∂μ) (Icc (0 : ℝ) q) :=
    hE.congr (hae.mono fun r hr => (hrow r hr).symm)
  have hb : (∫ r in Icc (0 : ℝ) q, ∫ x, F (r, x) ∂μ) ≤ B := by
    rw [integral_congr_ae (hae.mono fun r hr => hrow r hr)]
    exact hB
  have ht := fp81s21_g4_energy_tonelli μ hFm (fun z => sq_nonneg _) hx hr hb
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal (F z) ∂((volume.restrict (Icc (0 : ℝ) q)).prod μ) := by
      exact lintegral_mono' (Measure.prod_mono
        (Measure.restrict_mono (Icc_subset_Icc_right hvq) le_rfl) le_rfl) le_rfl
    _ ≤ _ := ht

#print axioms fp81s21_g4_kernel_energy
end HRS.Fp81.S21
end
