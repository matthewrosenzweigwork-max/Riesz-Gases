import HRS.MS.S111K4Q2

/-!
# S11.1 / T03 (S11K4): bounds along a classical orbit and the uniform bound of the screened forcing
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4

open HRS HRS.Whole
open HRS.MS.S111X1 (KData Wf kA kG_measurable prod_integrable_kernel)

variable {d : ℕ}

/-- Uniform `C_b²` bounds of a classical adjoint orbit. -/
theorem k4_cb_of_classical {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C t φ f) :
    ∃ Bf : ℝ, ∀ r ∈ Icc (0 : ℝ) t, MemCb 2 (f r) ∧ cbNorm 2 (f r) ≤ Bf := by
  obtain ⟨B0, h0⟩ := hf.bdd 0 (by norm_num)
  obtain ⟨B1, h1⟩ := hf.bdd 1 (by norm_num)
  obtain ⟨B2, h2⟩ := hf.bdd 2 (by norm_num)
  refine ⟨B0 + B1 + B2, fun r hr => ⟨⟨hf.c2 r hr, fun j hj => ?_⟩, ?_⟩⟩
  · interval_cases j
    · exact ⟨B0, by rintro _ ⟨x, rfl⟩; exact h0 r hr x⟩
    · exact ⟨B1, by rintro _ ⟨x, rfl⟩; exact h1 r hr x⟩
    · exact ⟨B2, by rintro _ ⟨x, rfl⟩; exact h2 r hr x⟩
  · unfold cbNorm
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have e0 : (⨆ z : Euc d, ‖iteratedFDeriv ℝ 0 (f r) z‖) ≤ B0 := ciSup_le fun z => h0 r hr z
    have e1 : (⨆ z : Euc d, ‖iteratedFDeriv ℝ 1 (f r) z‖) ≤ B1 := ciSup_le fun z => h1 r hr z
    have e2 : (⨆ z : Euc d, ‖iteratedFDeriv ℝ 2 (f r) z‖) ≤ B2 := ciSup_le fun z => h2 r hr z
    linarith

/-- Uniform bound of the screened forcing. -/
theorem k4_sf_bound {s : ℝ} {ρ : Euc d → ℝ} {M : ℝ} (K : KData d s ρ M)
    (hρ : HRS.Whole.IsProbDensity ρ) {β : ℝ} (hβ : 0 < β) (F H : Fin 3 → Euc d → ℝ) {B1 Bh : ℝ}
    (hF1 : ∀ i x, ‖gradient (F i) x‖ ≤ B1) (hFc : ∀ i, Continuous (gradient (F i)))
    (hHb : ∀ i x, |H i x| ≤ Bh) (hHc : ∀ i, Continuous (H i)) :
    |k4_screenedForcing s β (HRS.Whole.withDensityReal ρ) (fun i _ => F i) (fun i _ => H i) 0| ≤
      6 * B1 * Bh ^ 2 * (∫ p : Euc d × Euc d, ρ p.1 * (ρ p.2 * ‖rieszKernelGrad d s (p.1 - p.2)‖)
        ∂(volume.prod volume)) + 6 / β * (B1 ^ 2 * Bh) := by
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  have hB1 : 0 ≤ B1 := (norm_nonneg _).trans (hF1 0 0)
  have hBh : 0 ≤ Bh := (abs_nonneg _).trans (hHb 0 0)
  set J : ℝ := ∫ p : Euc d × Euc d, ρ p.1 * (ρ p.2 * ‖rieszKernelGrad d s (p.1 - p.2)‖) ∂(volume.prod volume) with hJ
  have hJ0 : 0 ≤ J := integral_nonneg fun p => mul_nonneg (K.nonneg _) (mul_nonneg (K.nonneg _) (norm_nonneg _))
  have hT : ∀ i : Fin 3, |∫ xy, commutatorKernel d s (gradient (F i)) xy.1 xy.2 * H (i + 1) xy.1 * H (i + 2) xy.2
      ∂((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ))| ≤ 2 * B1 * Bh ^ 2 * J := by
    intro i
    rw [k4_integral_prod_nu hρ, ← Real.norm_eq_abs]
    have hi := (k4_integrable_prod_nu hρ _).1 (k4_comm_integrable K hρ (hFc i).measurable (hF1 i)
      (hHc (i + 1)).measurable (hHb (i + 1)) (hHc (i + 2)).measurable (hHb (i + 2)))
    refine (norm_integral_le_of_norm_le (((prod_integrable_kernel K).const_mul (2 * B1 * Bh ^ 2)))
      (Filter.Eventually.of_forall fun p => ?_)).trans ?_
    · rw [Real.norm_eq_abs]
      simp only [abs_mul]
      rw [abs_of_nonneg (K.nonneg p.1), abs_of_nonneg (K.nonneg p.2)]
      have h1 : |commutatorKernel d s (gradient (F i)) p.1 p.2| ≤ 2 * B1 * ‖rieszKernelGrad d s (p.1 - p.2)‖ := by
        unfold commutatorKernel
        refine (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
        calc ‖gradient (F i) p.1 - gradient (F i) p.2‖ ≤ ‖gradient (F i) p.1‖ + ‖gradient (F i) p.2‖ :=
              norm_sub_le _ _
          _ ≤ 2 * B1 := by linarith [hF1 i p.1, hF1 i p.2]
      have h2 := hHb (i + 1) p.1
      have h3 := hHb (i + 2) p.2
      have hρ1 := K.nonneg p.1
      have hρ2 := K.nonneg p.2
      calc ρ p.1 * ρ p.2 * (|commutatorKernel d s (gradient (F i)) p.1 p.2| * |H (i + 1) p.1| * |H (i + 2) p.2|)
          ≤ ρ p.1 * ρ p.2 * (2 * B1 * ‖rieszKernelGrad d s (p.1 - p.2)‖ * Bh * Bh) := by gcongr
        _ = 2 * B1 * Bh ^ 2 * (ρ p.1 * (ρ p.2 * ‖rieszKernelGrad d s (p.1 - p.2)‖)) := by ring
    · rw [integral_const_mul]
  have hU : ∀ i : Fin 3, |∫ x, inner ℝ (gradient (F i) x) (gradient (F (i + 1)) x) * H (i + 2) x
      ∂(HRS.Whole.withDensityReal ρ)| ≤ B1 ^ 2 * Bh := by
    intro i
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := B1 ^ 2 * Bh) (Filter.Eventually.of_forall fun x => ?_)).trans ?_
    · rw [Real.norm_eq_abs, abs_mul]
      have h1 : |inner ℝ (gradient (F i) x) (gradient (F (i + 1)) x)| ≤ B1 ^ 2 := by
        refine (abs_real_inner_le_norm _ _).trans ?_
        rw [sq]; exact mul_le_mul (hF1 i x) (hF1 (i + 1) x) (norm_nonneg _) hB1
      exact mul_le_mul h1 (hHb (i + 2) x) (abs_nonneg _) (sq_nonneg _)
    · simp
  unfold k4_screenedForcing
  have hs1 : |∑ i : Fin 3, ∫ xy, commutatorKernel d s (gradient (F i)) xy.1 xy.2 * H (i + 1) xy.1 * H (i + 2) xy.2
      ∂((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ))| ≤ 3 * (2 * B1 * Bh ^ 2 * J) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ _i : Fin 3, 2 * B1 * Bh ^ 2 * J := Finset.sum_le_sum fun i _ => hT i
      _ = 3 * (2 * B1 * Bh ^ 2 * J) := by simp
  have hs2 : |∑ i : Fin 3, ∫ x, inner ℝ (gradient (F i) x) (gradient (F (i + 1)) x) * H (i + 2) x
      ∂(HRS.Whole.withDensityReal ρ)| ≤ 3 * (B1 ^ 2 * Bh) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ _i : Fin 3, B1 ^ 2 * Bh := Finset.sum_le_sum fun i _ => hU i
      _ = 3 * (B1 ^ 2 * Bh) := by simp
  have h2b : |2 / β| = 2 / β := abs_of_pos (by positivity)
  calc _ ≤ |-(∑ i : Fin 3, ∫ xy, commutatorKernel d s (gradient (F i)) xy.1 xy.2 * H (i + 1) xy.1 * H (i + 2) xy.2
        ∂((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ)))| +
      |2 / β * ∑ i : Fin 3, ∫ x, inner ℝ (gradient (F i) x) (gradient (F (i + 1)) x) * H (i + 2) x
        ∂(HRS.Whole.withDensityReal ρ)| := abs_add_le _ _
    _ ≤ 3 * (2 * B1 * Bh ^ 2 * J) + 2 / β * (3 * (B1 ^ 2 * Bh)) := by
        rw [abs_neg, abs_mul, h2b]
        exact add_le_add hs1 (mul_le_mul_of_nonneg_left hs2 (by positivity))
    _ = _ := by ring

end HRS.MS.S111K4
