import HRS.MS.Fp81S21GaussG4U5Kernel
import HRS.MS.Fp81S21GaussG4U5CS

/-! Integrated time Cauchy–Schwarz for the propagated generator. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2WinErr HRS.MS.R2WinOrbNL

theorem fp81s21_g4_kernel_cs
    (p : Parameters) {δ v w B : ℝ} (R : Trajectory p δ)
    (hterm : S104bTermRegGen p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁)
    {f : Euc p.d → ℝ} (hf : IsR2DualCombo (wholeSpaceIndex p.d : ℝ) f)
    (V : ℝ × ℝ → Euc p.d → Euc p.d)
    (hV : Measurable (Function.uncurry V))
    (hVe : ∀ r q, 0 ≤ r → r ≤ q → q ≤ w → ∀ x,
      V (r, q) x = gradient (r26t3_U R r q
        (generatorW (r26t3_coeff R) q f)) x)
    (hv : 0 ≤ v) (hvw : v ≤ w)
    (hE : ∀ q, 0 < q →
      IntegrableOn (fun r => ∫ x, ‖gradient (r26t3_U R r q
        (generatorW (r26t3_coeff R) q f)) x‖^2
        ∂HRS.Whole.withDensityReal R.ρβ) (Icc (0 : ℝ) q) ∧
      (∫ r in Icc (0 : ℝ) q, ∫ x, ‖gradient (r26t3_U R r q
        (generatorW (r26t3_coeff R) q f)) x‖^2
        ∂HRS.Whole.withDensityReal R.ρβ) ≤ B) :
    (∫⁻ z, (∫⁻ q in Icc v w, ‖V (z.1, q) z.2‖ₑ)^2
      ∂((volume.restrict (Icc (0 : ℝ) v)).prod (HRS.Whole.withDensityReal R.ρβ))) ≤
      ENNReal.ofReal (w-v) * (ENNReal.ofReal (w-v) * ENNReal.ofReal B) := by
  let μ := HRS.Whole.withDensityReal R.ρβ
  letI : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  let ν := (volume.restrict (Icc (0 : ℝ) v)).prod μ
  let h : (ℝ × Euc p.d) → ℝ → ℝ≥0∞ := fun z q => ‖V (z.1, q) z.2‖ₑ
  have hm : Measurable (fun z : (ℝ × Euc p.d) × ℝ => h z.1 z.2) := by
    exact (hV.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)).enorm
  have hqne : ∀ᵐ q ∂(volume.restrict (Icc v w)), q ≠ 0 :=
    ae_restrict_of_ae ((volume : Measure ℝ).ae_ne 0)
  have hqmem : ∀ᵐ q ∂(volume.restrict (Icc v w)), q ∈ Icc v w :=
    ae_restrict_mem measurableSet_Icc
  have hbound : ∀ᵐ q ∂(volume.restrict (Icc v w)), ∫⁻ z, h z q ^ 2 ∂ν ≤ ENNReal.ofReal B := by
    filter_upwards [hqne, hqmem] with q hqne hq
    have hqpos : 0 < q := lt_of_le_of_ne (hv.trans hq.1) (Ne.symm hqne)
    obtain ⟨hi, hb⟩ := hE q hqpos
    have hk := fp81s21_g4_kernel_energy p R hterm hf V hV hVe hv hq.1 hq.2 hi hb
    simpa only [h, ν, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)] using hk
  exact fp81s21_g4_integrated_cs ν hm hbound

#print axioms fp81s21_g4_kernel_cs
end HRS.Fp81.S21
end
