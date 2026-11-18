import HRS.MS.Fp81S21GaussG4U5Kernel
import HRS.MS.Fp81S21GaussG4U5CS
import HRS.MS.Fp81S21GaussG4U6Triangle

/-! Triangular Cauchy–Schwarz for the new-noise interval. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2WinErr HRS.MS.R2WinOrbNL

theorem fp81s21_g4_triangle_kernel_cs
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
    let T : Set ((ℝ × Euc p.d) × ℝ) := {z | z.1.1 ≤ z.2}
    (∫⁻ z, (∫⁻ q in Icc v w,
      ‖T.indicator (fun y => V (y.1.1, y.2) y.1.2) (z, q)‖ₑ)^2
      ∂((volume.restrict (Icc (0 : ℝ) w)).prod (HRS.Whole.withDensityReal R.ρβ))) ≤
      ENNReal.ofReal (w-v) * (ENNReal.ofReal (w-v) * ENNReal.ofReal B) := by
  let μ := HRS.Whole.withDensityReal R.ρβ
  letI : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  let ν := (volume.restrict (Icc (0 : ℝ) w)).prod μ
  let T : Set ((ℝ × Euc p.d) × ℝ) := {z | z.1.1 ≤ z.2}
  have hT : MeasurableSet T := measurableSet_le measurable_fst.fst measurable_snd
  let G : (ℝ × Euc p.d) × ℝ → Euc p.d := T.indicator (fun y => V (y.1.1, y.2) y.1.2)
  have hG : Measurable G :=
    (hV.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)).indicator hT
  let h : (ℝ × Euc p.d) → ℝ → ℝ≥0∞ := fun z q => ‖G (z, q)‖ₑ
  have hm : Measurable (fun z : (ℝ × Euc p.d) × ℝ => h z.1 z.2) := hG.enorm
  have hqne : ∀ᵐ q ∂(volume.restrict (Icc v w)), q ≠ 0 :=
    ae_restrict_of_ae ((volume : Measure ℝ).ae_ne 0)
  have hqmem : ∀ᵐ q ∂(volume.restrict (Icc v w)), q ∈ Icc v w :=
    ae_restrict_mem measurableSet_Icc
  have hbound : ∀ᵐ q ∂(volume.restrict (Icc v w)), ∫⁻ z, h z q ^ 2 ∂ν ≤ ENNReal.ofReal B := by
    filter_upwards [hqne, hqmem] with q hqne hq
    have hqpos : 0 < q := lt_of_le_of_ne (hv.trans hq.1) (Ne.symm hqne)
    obtain ⟨hi, hb⟩ := hE q hqpos
    have hk := fp81s21_g4_kernel_energy p R hterm hf V hV hVe hqpos.le le_rfl hq.2 hi hb
    have ht := fp81s21_g4_triangle_lintegral μ w q (fun z => ‖V (z.1, q) z.2‖ₑ^2)
    have heq : (∫⁻ z, h z q ^ 2 ∂ν) =
        ∫⁻ z, (Iic q ×ˢ (univ : Set (Euc p.d))).indicator
          (fun z => ‖V (z.1, q) z.2‖ₑ^2) z ∂ν := by
      apply lintegral_congr
      intro z
      by_cases hz : z.1 ≤ q <;> simp [h, G, T, Set.indicator_apply, hz]
    rw [heq]
    apply ht.trans
    simpa only [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)] using hk
  exact fp81s21_g4_integrated_cs ν hm hbound

#print axioms fp81s21_g4_triangle_kernel_cs
end HRS.Fp81.S21
end
