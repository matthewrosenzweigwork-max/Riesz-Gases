import HRS.Commutator.Torus.NRSTAux4
import HRS.Energy.Commutator.AbsConv

/-!
# NRS-T, part 5: integrability of the commutator kernel against a continuous density
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace HRS.Commutator.TorusNote.NRST

open HRS HRS.Commutator

variable {d : ℕ} {s : ℝ}

/-- The commutator integrand is integrable on `𝕋^d × 𝕋^d` for Lipschitz `v` and bounded measurable `w`. -/
lemma integrable_commProd (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {L : ℝ} (hL : 0 ≤ L)
    {v : Torus d → Euc d} (hv : IsLipschitzVF L v) {w : Torus d → ℝ} (hwm : Measurable w)
    {B : ℝ} (hB : ∀ x, |w x| ≤ B) :
    Integrable (fun p : Torus d × Torus d =>
      commKernel (periodicRieszGrad d s) v p.1 p.2 * w p.1 * w p.2) (volume.prod volume) := by
  obtain ⟨C, hC0, hC⟩ := commKernel_bound hd hs0 hsd
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hK : 0 ≤ C * L * (B * B) := by positivity
  have hvc : Continuous v := IsLipschitzVF.continuous hL hv
  have hmeas0 : Measurable (fun p : Torus d × Torus d => commKernel (periodicRieszGrad d s) v p.1 p.2) := by
    unfold commKernel
    refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const ?_
    refine Measurable.inner ?_ ?_
    · exact (hvc.measurable.comp measurable_fst).sub (hvc.measurable.comp measurable_snd)
    · exact (KernelGrad.measurable_periodicRieszGrad hsd).comp (measurable_fst.sub measurable_snd)
  have hmeas : Measurable (fun p : Torus d × Torus d =>
      commKernel (periodicRieszGrad d s) v p.1 p.2 * w p.1 * w p.2) :=
    (hmeas0.mul (hwm.comp measurable_fst)).mul (hwm.comp measurable_snd)
  have hbound0 : ∀ x y : Torus d,
      |commKernel (periodicRieszGrad d s) v x y| ≤ (C * L) * (‖x - y‖ ^ (-s) + 1) := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      unfold commKernel
      rw [if_pos rfl, abs_zero]
      exact mul_nonneg (mul_nonneg hC0 hL) (add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) zero_le_one)
    · have h1 := hC L v hL hv x y hxy
      have hz : x - y ≠ 0 := sub_ne_zero.mpr hxy
      have h2 : KernelGrad.tdist x y ^ (-s) ≤ ‖x - y‖ ^ (-s) := by
        rw [KernelGrad.tdist_eq_sub_zero]
        exact Real.rpow_le_rpow_of_nonpos (norm_pos_iff.mpr hz) (KernelGrad.norm_le_tdist _)
          (by linarith)
      calc |commKernel (periodicRieszGrad d s) v x y|
          ≤ C * L * (KernelGrad.tdist x y ^ (-s) + 1) := h1
        _ ≤ (C * L) * (‖x - y‖ ^ (-s) + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC0 hL)
  set Φ : Torus d → ℝ := fun z => (C * L * (B * B)) * (‖z‖ ^ (-s) + 1) with hΦ
  have hbound : ∀ x y : Torus d,
      |commKernel (periodicRieszGrad d s) v x y * w x * w y| ≤ Φ (x - y) := by
    intro x y
    rw [abs_mul, abs_mul]
    calc |commKernel (periodicRieszGrad d s) v x y| * |w x| * |w y|
        ≤ ((C * L) * (‖x - y‖ ^ (-s) + 1)) * B * B := by
          gcongr
          · exact hbound0 x y
          · exact hB x
          · exact hB y
      _ = Φ (x - y) := by rw [hΦ]; ring
  have hgi : Integrable Φ volume :=
    ((KernelGrad.integrable_norm_rpow_neg (by omega) hsd).add (integrable_const _)).const_mul _
  have hgi' : ∀ x : Torus d, Integrable (fun y : Torus d => Φ (x - y)) volume :=
    fun x => hgi.comp_sub_left x
  have hx : ∀ x : Torus d, Integrable (fun y : Torus d =>
      commKernel (periodicRieszGrad d s) v x y * w x * w y) volume := by
    intro x
    refine Integrable.mono' (hgi' x) ?_ (Filter.Eventually.of_forall fun y => ?_)
    · exact (hmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact hbound x y
  refine absConv_integrable_prod (ν := volume) (μ := volume) hmeas hx
    (M := ∫ z : Torus d, Φ z) fun x => ?_
  have h1 : ∫ y, ‖commKernel (periodicRieszGrad d s) v x y * w x * w y‖
      ≤ ∫ y, Φ (x - y) :=
    integral_mono (hx x).norm (hgi' x) fun y => by
      rw [Real.norm_eq_abs]; exact hbound x y
  have h2 : ∫ y : Torus d, Φ (x - y) = ∫ z : Torus d, Φ z :=
    integral_sub_left_eq_self Φ volume x
  exact h1.trans h2.le

end HRS.Commutator.TorusNote.NRST
