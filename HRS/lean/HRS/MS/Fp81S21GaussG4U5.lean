import HRS.MS.Fp81S21GaussG4U5Bound
import HRS.MS.Fp81S21GaussG4U5KernelCS
import HRS.MS.Fp81S21GaussG4U5Integral

/-! Old-noise gradient increment estimated by the uniform energy budget. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2WinErr HRS.MS.R2WinOrbNL

def fp81s21_g4_Old {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    (f : Euc p.d → ℝ) (v w : ℝ) : ℝ :=
  ∫ r in Icc (0 : ℝ) v, ∫ x,
    ‖gradient (r26t3_U R r w f) x - gradient (r26t3_U R r v f) x‖^2
      ∂HRS.Whole.withDensityReal R.ρβ

theorem fp81s21_g4_old_combo (p : Parameters) :
    fp81s21_g4Phys p (fun _ R =>
      ∃ A : ℝ, 0 ≤ A ∧ ∀ f, IsR2DualCombo (wholeSpaceIndex p.d : ℝ) f →
        ∀ v w, 0 ≤ v → v ≤ w →
          fp81s21_g4_Old R f v w ≤ A * (w-v)^2 * fp81s21_g4_J p.d f) := by
  obtain ⟨δe, hδe, hehalf, he⟩ := fp81s21_g4_generator_energy p
  obtain ⟨δd, hδd, hdhalf, hd⟩ := fp81s21_g4_gradient_duhamel_combo p
  obtain ⟨δc, C, c, hδc, hchalf, hc, hcommon⟩ := fp81s21_common_radius p
  refine ⟨min δe (min δd δc), lt_min hδe (lt_min hδd hδc),
    (min_le_left _ _).trans hehalf, ?_⟩
  intro δ hδ hδle R
  have hδe' := hδle.trans (min_le_left δe (min δd δc))
  have hδd' := hδle.trans ((min_le_right δe (min δd δc)).trans (min_le_left δd δc))
  have hδc' := hδle.trans ((min_le_right δe (min δd δc)).trans (min_le_right δd δc))
  obtain ⟨A, hA, henergy⟩ := he δ hδ hδe' R
  obtain ⟨_, _, hterm, _⟩ := hcommon δ hδ hδc' R.ρβ R.thermal
  have hduh := hd δ hδ hδd' R
  refine ⟨A, hA, ?_⟩
  intro f hf v w hv hvw
  let μ := HRS.Whole.withDensityReal R.ρβ
  letI : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  let ν := (volume.restrict (Icc (0 : ℝ) v)).prod μ
  have hw : 0 ≤ w := hv.trans hvw
  obtain ⟨V, hV, hVe⟩ := fp81s21_g4_combo_gradient_joint_meas p R hw hterm hf
  have hcost : 0 ≤ fp81s21_g4_J p.d f := by
    unfold fp81s21_g4_J
    exact sq_nonneg _
  let B : ℝ := A * fp81s21_g4_J p.d f
  let D : ℝ := (w-v)^2 * B
  have hB : 0 ≤ B := mul_nonneg hA hcost
  have hD : 0 ≤ D := mul_nonneg (sq_nonneg _) hB
  have hcs := fp81s21_g4_kernel_cs p R hterm hf V hV hVe hv hvw
    (fun q hq => henergy f hf q hq)
  have hcs' : (∫⁻ z, (∫⁻ q in Icc v w, ‖V (z.1, q) z.2‖ₑ)^2 ∂ν) ≤
      ENNReal.ofReal D := by
    calc
      _ ≤ ENNReal.ofReal (w-v) * (ENNReal.ofReal (w-v) * ENNReal.ofReal B) := hcs
      _ = ENNReal.ofReal D := by
        dsimp [D]
        rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (sub_nonneg.mpr hvw)]
        ring
  let G : (ℝ × Euc p.d) × ℝ → Euc p.d := fun z => V (z.1.1, z.2) z.1.2
  have hG : Measurable G :=
    hV.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)
  obtain ⟨hi, hb⟩ := fp81s21_g4_bochner_energy ν (volume.restrict (Icc v w)) hG hcs' hD
  have heq : ∀ r ∈ Icc (0 : ℝ) v, ∀ x,
      (∫ q in Icc v w, G ((r, x), q)) =
      gradient (r26t3_U R r w f) x - gradient (r26t3_U R r v f) x := by
    intro r hr x
    rw [(hduh f hf r v w hr.1 hr.2 hvw x).2]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with q hq
    exact hVe r q hr.1 (hr.2.trans hq.1) hq.2 x
  have hrow : ∀ r ∈ Icc (0 : ℝ) v,
      (∫ x, ‖∫ q in Icc v w, G ((r, x), q)‖^2 ∂μ) =
      ∫ x, ‖gradient (r26t3_U R r w f) x - gradient (r26t3_U R r v f) x‖^2 ∂μ := by
    intro r hr
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change ‖∫ q in Icc v w, G ((r, x), q)‖^2 =
        ‖gradient (r26t3_U R r w f) x - gradient (r26t3_U R r v f) x‖^2
      rw [heq r hr x]
  have hid : (∫ z, ‖∫ q in Icc v w, G (z, q)‖^2 ∂ν) = fp81s21_g4_Old R f v w := by
    rw [integral_prod _ hi]
    unfold fp81s21_g4_Old
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact hrow r hr
  rw [hid] at hb
  dsimp [D, B] at hb
  nlinarith

#print axioms fp81s21_g4_old_combo
end HRS.Fp81.S21
end
