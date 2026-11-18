import HRS.MS.Fp81S21GaussG4U5Bound
import HRS.MS.Fp81S21GaussG4U5Integral
import HRS.MS.Fp81S21GaussG4U6KernelCS

/-! Quadratic energy bound for the triangular terminal-gradient increment. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2WinErr HRS.MS.R2WinOrbNL

theorem fp81s21_g4_triangle_diff (p : Parameters) :
    fp81s21_g4Phys p (fun _ R =>
      ∃ A : ℝ, 0 ≤ A ∧ ∀ f, IsR2DualCombo (wholeSpaceIndex p.d : ℝ) f →
      ∀ v w, 0 ≤ v → v ≤ w →
        Integrable (fun z : ℝ × Euc p.d =>
          ‖gradient (r26t3_U R z.1 w f) z.2 - gradient f z.2‖^2)
          ((volume.restrict (Icc v w)).prod (HRS.Whole.withDensityReal R.ρβ)) ∧
        (∫ r in Icc v w, ∫ x,
          ‖gradient (r26t3_U R r w f) x - gradient f x‖^2
          ∂HRS.Whole.withDensityReal R.ρβ) ≤ A * (w-v)^2 * fp81s21_g4_J p.d f) := by
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
  let ν := (volume.restrict (Icc v w)).prod μ
  let ν' := (volume.restrict (Icc (0 : ℝ) w)).prod μ
  have hw : 0 ≤ w := hv.trans hvw
  obtain ⟨V, hV, hVe⟩ := fp81s21_g4_combo_gradient_joint_meas p R hw hterm hf
  have hcost : 0 ≤ fp81s21_g4_J p.d f := by unfold fp81s21_g4_J; exact sq_nonneg _
  let B : ℝ := A * fp81s21_g4_J p.d f
  let D : ℝ := (w-v)^2 * B
  have hB : 0 ≤ B := mul_nonneg hA hcost
  have hD : 0 ≤ D := mul_nonneg (sq_nonneg _) hB
  let T : Set ((ℝ × Euc p.d) × ℝ) := {z | z.1.1 ≤ z.2}
  have hT : MeasurableSet T := measurableSet_le measurable_fst.fst measurable_snd
  let G : (ℝ × Euc p.d) × ℝ → Euc p.d := T.indicator (fun y => V (y.1.1, y.2) y.1.2)
  have hG : Measurable G :=
    (hV.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)).indicator hT
  have hcs := fp81s21_g4_triangle_kernel_cs p R hterm hf V hV hVe hv hvw
    (fun q hq => henergy f hf q hq)
  have hν : ν ≤ ν' := Measure.prod_mono
    (Measure.restrict_mono (Icc_subset_Icc_left hv) le_rfl) le_rfl
  have hcs' : (∫⁻ z, (∫⁻ q in Icc v w, ‖G (z, q)‖ₑ)^2 ∂ν) ≤ ENNReal.ofReal D := by
    calc
      _ ≤ ∫⁻ z, (∫⁻ q in Icc v w, ‖G (z, q)‖ₑ)^2 ∂ν' := lintegral_mono' hν le_rfl
      _ ≤ ENNReal.ofReal (w-v) * (ENNReal.ofReal (w-v) * ENNReal.ofReal B) := hcs
      _ = ENNReal.ofReal D := by
        dsimp [D]
        rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (sub_nonneg.mpr hvw)]
        ring
  obtain ⟨hi, hb⟩ := fp81s21_g4_bochner_energy ν (volume.restrict (Icc v w)) hG hcs' hD
  have heq : ∀ r ∈ Icc v w, ∀ x,
      (∫ q in Icc v w, G ((r, x), q)) =
      gradient (r26t3_U R r w f) x - gradient f x := by
    intro r hr x
    have hdiag : r26t3_U R r r f = f :=
      (HRS.MS.Fcau.propagatorW_isClassical
        (fp81s21_adjoint_of_hermite_combo p R hf (hv.trans hr.1))).terminal
    have hduhr := (hduh f hf r r w (hv.trans hr.1) le_rfl hr.2 x).2
    rw [hdiag] at hduhr
    rw [hduhr]
    have hg : (fun q => G ((r, x), q)) = (Ici r).indicator (fun q => V (r, q) x) := by
      funext q
      by_cases h : r ≤ q <;> simp [G, T, Set.indicator_apply, h]
    rw [hg, integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
    have hset : Ici r ∩ Icc v w = Icc r w := by
      ext q
      simp only [mem_inter_iff, mem_Ici, mem_Icc]
      constructor
      · rintro ⟨hrq, _, hqw⟩; exact ⟨hrq, hqw⟩
      · rintro ⟨hrq, hqw⟩; exact ⟨hrq, hr.1.trans hrq, hqw⟩
    rw [hset]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with q hq
    exact hVe r q (hv.trans hr.1) hq.1 hq.2 x
  have hae : ∀ᵐ z ∂ν, z.1 ∈ Icc v w := by
    dsimp [ν]
    rw [Measure.restrict_prod_eq_prod_univ]
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod MeasurableSet.univ)] with z hz
    exact hz.1
  have hiae : (fun z : ℝ × Euc p.d => ‖∫ q in Icc v w, G (z, q)‖^2) =ᵐ[ν]
      (fun z => ‖gradient (r26t3_U R z.1 w f) z.2 - gradient f z.2‖^2) := by
    filter_upwards [hae] with z hz
    change ‖∫ q in Icc v w, G (z, q)‖^2 = _
    rw [heq z.1 hz z.2]
  have hid : Integrable (fun z : ℝ × Euc p.d =>
      ‖gradient (r26t3_U R z.1 w f) z.2 - gradient f z.2‖^2) ν := hi.congr hiae
  refine ⟨hid, ?_⟩
  have he : (∫ z, ‖∫ q in Icc v w, G (z, q)‖^2 ∂ν) =
      ∫ r in Icc v w, ∫ x, ‖gradient (r26t3_U R r w f) x - gradient f x‖^2 ∂μ := by
    rw [integral_congr_ae hiae, integral_prod _ hid]
  rw [he] at hb
  dsimp [D, B] at hb
  nlinarith

#print axioms fp81s21_g4_triangle_diff
end HRS.Fp81.S21
end
