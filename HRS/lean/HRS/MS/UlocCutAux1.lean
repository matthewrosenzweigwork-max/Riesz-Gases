import HRS.MS.SobMul

/-!
# MS-ULOC-CUT, part 1: the triangle inequality for `sobolevNormE`
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate FourierTransform

namespace HRS.MS.UlocCut
open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

/-- `⟨ξ⟩^{s/2} |û(ξ)|` in `ℝ≥0∞` -/
def uc_A (s : ℝ) (u : Euc d → ℝ) (ξ : Euc d) : ℝ≥0∞ :=
  ENNReal.ofReal (wt ξ ^ (s / 2) * ‖fourierL2 u ξ‖)

theorem uc_A_sq (s : ℝ) (u : Euc d → ℝ) (ξ : Euc d) :
    uc_A s u ξ ^ (2 : ℝ) = ENNReal.ofReal (wt ξ ^ s * ‖fourierL2 u ξ‖ ^ 2) := by
  unfold uc_A
  have h0 : 0 ≤ wt ξ ^ (s / 2) * ‖fourierL2 u ξ‖ :=
    mul_nonneg (Real.rpow_nonneg (wt_pos ξ).le _) (norm_nonneg _)
  rw [ENNReal.ofReal_rpow_of_nonneg h0 (by norm_num)]
  congr 1
  rw [Real.mul_rpow (Real.rpow_nonneg (wt_pos ξ).le _) (norm_nonneg _),
    ← Real.rpow_mul (wt_pos ξ).le, show s / 2 * 2 = s by ring, Real.rpow_two]

theorem uc_A_aemeasurable (s : ℝ) {u : Euc d → ℝ} (hu : MemLp u 2 volume) :
    AEMeasurable (uc_A s u) volume := by
  have hm := aestronglyMeasurable_fourierL2 hu
  have : AEStronglyMeasurable (fun ξ : Euc d => wt ξ ^ (s / 2) * ‖fourierL2 u ξ‖) volume :=
    (continuous_wt_rpow (s / 2)).aestronglyMeasurable.mul hm.norm
  exact this.aemeasurable.ennreal_ofReal

theorem uc_eq {s : ℝ} {u : Euc d → ℝ} (hu : HRS.PDE.ToolboxRd.MemSobolev s u) :
    HRS.Whole.sobolevNormE s u = (∫⁻ ξ, uc_A s u ξ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  unfold HRS.Whole.sobolevNormE
  rw [if_pos hu]
  simp_rw [uc_A_sq]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun ξ =>
      mul_nonneg (Real.rpow_nonneg (wt_pos ξ).le _) (sq_nonneg _)) (by norm_num)]
    rw [sobolevNormSq_eq, Real.sqrt_eq_rpow]
  · exact hu.2
  · exact Filter.Eventually.of_forall fun ξ =>
      mul_nonneg (Real.rpow_nonneg (wt_pos ξ).le _) (sq_nonneg _)

theorem uc_tri (s : ℝ) (u v : Euc d → ℝ) :
    HRS.Whole.sobolevNormE s (fun x => u x + v x) ≤
      HRS.Whole.sobolevNormE s u + HRS.Whole.sobolevNormE s v := by
  by_cases hu : HRS.PDE.ToolboxRd.MemSobolev s u
  swap
  · unfold HRS.Whole.sobolevNormE; rw [if_neg hu]; simp
  by_cases hv : HRS.PDE.ToolboxRd.MemSobolev s v
  swap
  · unfold HRS.Whole.sobolevNormE; rw [if_neg hv]; simp
  have hae := fourierL2_add hu.1 hv.1
  have hW : HRS.PDE.ToolboxRd.MemSobolev s (fun x => u x + v x) := by
    refine ⟨hu.1.add hv.1, ?_⟩
    have hm := aesm_wt_mul (aestronglyMeasurable_fourierL2 (hu.1.add hv.1)) s
    refine Integrable.mono' ((hu.2.add hv.2).const_mul 2) hm ?_
    filter_upwards [hae] with ξ hξ
    show ‖wt ξ ^ s * ‖fourierL2 (fun x => u x + v x) ξ‖ ^ 2‖ ≤
      2 * (wt ξ ^ s * ‖fourierL2 u ξ‖ ^ 2 + wt ξ ^ s * ‖fourierL2 v ξ‖ ^ 2)
    have h0 : 0 ≤ wt ξ ^ s * ‖fourierL2 (fun x => u x + v x) ξ‖ ^ 2 :=
      mul_nonneg (Real.rpow_nonneg (wt_pos ξ).le _) (sq_nonneg _)
    rw [Real.norm_of_nonneg h0, hξ]
    have hw := Real.rpow_nonneg (wt_pos ξ).le s
    have h1 : ‖fourierL2 u ξ + fourierL2 v ξ‖ ^ 2 ≤
        2 * (‖fourierL2 u ξ‖ ^ 2 + ‖fourierL2 v ξ‖ ^ 2) := by
      have := norm_add_le (fourierL2 u ξ) (fourierL2 v ξ)
      nlinarith [norm_nonneg (fourierL2 u ξ), norm_nonneg (fourierL2 v ξ),
        norm_nonneg (fourierL2 u ξ + fourierL2 v ξ),
        sq_nonneg (‖fourierL2 u ξ‖ - ‖fourierL2 v ξ‖)]
    calc wt ξ ^ s * ‖fourierL2 u ξ + fourierL2 v ξ‖ ^ 2
        ≤ wt ξ ^ s * (2 * (‖fourierL2 u ξ‖ ^ 2 + ‖fourierL2 v ξ‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left h1 hw
      _ = 2 * (wt ξ ^ s * ‖fourierL2 u ξ‖ ^ 2 + wt ξ ^ s * ‖fourierL2 v ξ‖ ^ 2) := by ring
  rw [uc_eq hW, uc_eq hu, uc_eq hv]
  have hle : ∀ᵐ ξ ∂(volume : Measure (Euc d)),
      uc_A s (fun x => u x + v x) ξ ≤ uc_A s u ξ + uc_A s v ξ := by
    filter_upwards [hae] with ξ hξ
    unfold uc_A
    rw [hξ, ← ENNReal.ofReal_add
      (mul_nonneg (Real.rpow_nonneg (wt_pos ξ).le _) (norm_nonneg _))
      (mul_nonneg (Real.rpow_nonneg (wt_pos ξ).le _) (norm_nonneg _))]
    apply ENNReal.ofReal_le_ofReal
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.rpow_nonneg (wt_pos ξ).le _)
  calc (∫⁻ ξ, uc_A s (fun x => u x + v x) ξ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
      ≤ (∫⁻ ξ, (uc_A s u + uc_A s v) ξ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        apply ENNReal.rpow_le_rpow _ (by norm_num)
        apply lintegral_mono_ae
        filter_upwards [hle] with ξ hξ
        exact ENNReal.rpow_le_rpow hξ (by norm_num)
    _ ≤ _ := ENNReal.lintegral_Lp_add_le (uc_A_aemeasurable s hu.1) (uc_A_aemeasurable s hv.1)
        (by norm_num)

theorem uc_zero (s : ℝ) : HRS.Whole.sobolevNormE s (fun _ : Euc d => (0 : ℝ)) = 0 := by
  have hz : MemLp (fun _ : Euc d => (0 : ℝ)) 2 volume := by simpa using (MeasureTheory.MemLp.zero (E := ℝ) (p := 2) (μ := (volume : Measure (Euc d))))
  have hae := fourierL2_smul hz 0
  have hS : HRS.PDE.ToolboxRd.MemSobolev s (fun _ : Euc d => (0 : ℝ)) := by
    refine ⟨hz, ?_⟩
    have : (fun ξ => (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ s * ‖fourierL2 (fun _ : Euc d => (0 : ℝ)) ξ‖ ^ 2)
        =ᵐ[volume] fun _ => 0 := by
      filter_upwards [hae] with ξ hξ
      simp only [zero_mul] at hξ
      rw [hξ]; simp
    exact (integrable_zero _ _ _).congr this.symm
  rw [uc_eq hS]
  have : ∀ᵐ ξ ∂(volume : Measure (Euc d)), uc_A s (fun _ : Euc d => (0 : ℝ)) ξ ^ (2 : ℝ) = 0 := by
    filter_upwards [hae] with ξ hξ
    simp only [zero_mul] at hξ
    unfold uc_A
    rw [hξ]; simp
  rw [lintegral_congr_ae this]; simp

theorem uc_sum_le (s : ℝ) {ι : Type*} (S : Finset ι) (f : ι → Euc d → ℝ) :
    HRS.Whole.sobolevNormE s (fun x => ∑ i ∈ S, f i x) ≤ ∑ i ∈ S, HRS.Whole.sobolevNormE s (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [uc_zero]
  | insert a S ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (uc_tri s (f a) (fun x => ∑ i ∈ S, f i x)).trans (add_le_add_right ih _)

end HRS.MS.UlocCut
