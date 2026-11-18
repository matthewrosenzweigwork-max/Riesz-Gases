import HRS.MS.SA12V3K

/-!
# S.A.12 C2 (SA12V3 worker), part L: one mollified cell is controlled by finitely many lattice cells

For `ε ≤ 1`: `‖χ(·-c) (G_ε * φ)‖_{H^m} ≤ C ∑_{j∈J} ‖χ(·-cellPt(k₀+j)) φ‖_{H^m}`, `k₀ = k₀(c)` the fine-lattice rounding
of the real centre `c`, `J` a finite offset set, `C` independent of `ε ≤ 1`, `c`, `φ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Pointwise

namespace HRS.MH.AdjointRd.Phase2SA12V3

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
  HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12v3_cellPt_eq (z : Fin d → ℤ) : cellPt d z = HRS.MS.UlocCut.uc_fp z := by
  have h : ((⌈Real.sqrt d⌉ : ℤ) : ℝ) = ((⌈Real.sqrt d⌉₊ : ℕ) : ℝ) := by
    rw [← natCast_ceil_eq_intCast_ceil (Real.sqrt_nonneg _)]
  unfold cellPt HRS.MS.UlocCut.uc_fp
  rw [h]

/-- The cutoff `χ(·/3)`: `1` on `closedBall 0 3`, supported in `‖p‖ < 6`. -/
theorem sa12v3_chi3 {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) :
    ContDiff ℝ ∞ (fun p : Euc d => χ ((3 : ℝ)⁻¹ • p)) ∧ HasCompactSupport (fun p : Euc d => χ ((3 : ℝ)⁻¹ • p)) ∧
      (∀ p : Euc d, χ ((3 : ℝ)⁻¹ • p) ≠ 0 → ‖p‖ ≤ 6) ∧
      ∀ p : Euc d, ‖p‖ ≤ 3 → χ ((3 : ℝ)⁻¹ • p) = 1 := by
  refine ⟨hχ.1.comp (contDiff_const_smul _), hχ.2.1.comp_smul (by norm_num), ?_, ?_⟩
  · intro p hp
    have h1 : (3 : ℝ)⁻¹ • p ∈ Metric.ball (0 : Euc d) 2 :=
      hχ.2.2.1 (subset_tsupport _ (Function.mem_support.2 hp))
    rw [Metric.mem_ball, dist_zero_right, norm_smul] at h1
    simp only [norm_inv, Real.norm_ofNat] at h1
    linarith
  · intro p hp
    apply hχ.2.2.2.2
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul]
    simp only [norm_inv, Real.norm_ofNat]
    linarith

theorem sa12v3_moll_cell {η : Euc d → ℝ} (hη : IsMollifier η) {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) (m : ℕ) :
    ∃ (J : Finset (Fin d → ℤ)) (C : ℝ), 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ c : Euc d,
      ∃ k₀ : Fin d → ℤ, ‖c - cellPt d k₀‖ ≤ 1 / 2 ∧ ∀ φ : Euc d → ℝ,
        sobolevNormE (m : ℝ) (fun x => χ (x - c) * mollify η ε φ x) ≤
          ENNReal.ofReal C * ∑ j ∈ J, sobolevNormE (m : ℝ) (fun x => χ (x - cellPt d (k₀ + j)) * φ x) := by
  obtain ⟨ha, hac, hasup, ha1⟩ := sa12v3_chi3 hχ
  obtain ⟨J, hJ⟩ := HRS.MS.UlocCut.uc_cover (HRS.MS.UlocCut.uc_fp (d := d)) (fun p => by
    obtain ⟨k, hk⟩ := HRS.MS.UlocCut.uc_fine_approx p
    exact ⟨k, by linarith⟩) (6 + 1 / 2)
  obtain ⟨Ck, hCk, hkey⟩ := HRS.MS.Ul.ul0_key m (fun p : Euc d => χ ((3 : ℝ)⁻¹ • p)) χ ha hac hχ.1 hχ.2.1
    (J.image HRS.MS.UlocCut.uc_fp) 6 (1 / 2) (6 + 1 / 2) (by norm_num) le_rfl hasup
    (fun p hp => by
      obtain ⟨j, hj, hpj⟩ := hJ p hp
      exact ⟨HRS.MS.UlocCut.uc_fp j, Finset.mem_image_of_mem _ hj,
        hχ.2.2.2.2 _ (by rw [Metric.mem_closedBall, dist_zero_right]; exact hpj.le)⟩)
  obtain ⟨Cm, hCm, hmul⟩ := HRS.MS.SobMul.sobolevNormE_mul_translate_le (d := d) (m : ℝ) (Nat.cast_nonneg m)
    χ hχ.1 hχ.2.1
  refine ⟨J, Cm * Ck, mul_pos hCm hCk, fun ε hε hε1 c => ?_⟩
  obtain ⟨k₀, hk₀⟩ := HRS.MS.UlocCut.uc_fine_approx c
  refine ⟨k₀, by rw [sa12v3_cellPt_eq]; exact hk₀, fun φ => ?_⟩
  -- the cutoff-enlargement identity
  have hid : (fun x => χ (x - c) * mollify η ε φ x) =
      fun x => χ (x - c) * mollify η ε (fun y => χ ((3 : ℝ)⁻¹ • (y - c)) * φ y) x := by
    funext x
    by_cases hx : χ (x - c) = 0
    · simp [hx]
    · congr 1
      have hxn : ‖x - c‖ < 2 := by
        have := hχ.2.2.1 (subset_tsupport _ (Function.mem_support.2 hx))
        simpa using this
      unfold mollify
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      beta_reduce
      by_cases hy : ε ^ (-(d : ℤ)) * η (ε⁻¹ • y) = 0
      · rw [hy, zero_mul, zero_mul]
      · have hη0 : η (ε⁻¹ • y) ≠ 0 := fun h => hy (by rw [h, mul_zero])
        have hyn : ‖y‖ ≤ ε := by
          have h1 : ε⁻¹ • y ∈ Metric.closedBall (0 : Euc d) 1 :=
            hη.2.2.1 (subset_tsupport _ (Function.mem_support.2 hη0))
          rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs,
            abs_of_pos hε] at h1
          rwa [inv_mul_le_iff₀ hε, mul_one] at h1
        have h3 : ‖x - y - c‖ ≤ 3 := by
          calc ‖x - y - c‖ = ‖(x - c) - y‖ := by congr 1; abel
            _ ≤ ‖x - c‖ + ‖y‖ := norm_sub_le _ _
            _ ≤ 3 := by linarith
        have : χ ((3 : ℝ)⁻¹ • (x - y - c)) = 1 := ha1 _ h3
        rw [show x - y - c = (x - y) - c from rfl] at this
        simp only [this, one_mul]
  rw [hid]
  have h1 := hmul c (mollify η ε (fun y => χ ((3 : ℝ)⁻¹ • (y - c)) * φ y))
  have h2 := sa12v3_mollify_sobolevNormE_le hη hε (m : ℝ) (fun y => χ ((3 : ℝ)⁻¹ • (y - c)) * φ y)
  have h3 := hkey c (cellPt d k₀) (by rw [sa12v3_cellPt_eq]; exact hk₀) φ
  have hform : (fun y => χ ((3 : ℝ)⁻¹ • (y - c)) * φ y) = fun y => (fun p : Euc d => χ ((3 : ℝ)⁻¹ • p)) (y - c) * φ y := rfl
  rw [hform] at h2
  calc _ ≤ ENNReal.ofReal Cm * sobolevNormE (m : ℝ) (mollify η ε fun y => (fun p : Euc d => χ ((3 : ℝ)⁻¹ • p)) (y - c) * φ y) := h1
    _ ≤ ENNReal.ofReal Cm * sobolevNormE (m : ℝ) (fun y => (fun p : Euc d => χ ((3 : ℝ)⁻¹ • p)) (y - c) * φ y) := by
        gcongr
    _ ≤ ENNReal.ofReal Cm * (ENNReal.ofReal Ck * ∑ y ∈ J.image HRS.MS.UlocCut.uc_fp,
          sobolevNormE (m : ℝ) (fun x => χ (x - (cellPt d k₀ + y)) * φ x)) := by gcongr
    _ ≤ ENNReal.ofReal (Cm * Ck) * ∑ j ∈ J, sobolevNormE (m : ℝ) (fun x => χ (x - cellPt d (k₀ + j)) * φ x) := by
        rw [ENNReal.ofReal_mul hCm.le, mul_assoc]
        gcongr
        refine (Finset.sum_image_le_of_nonneg (fun _ _ => bot_le)).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl fun j _ => ?_
        have e : HRS.MS.UlocCut.uc_fp (d := d) j = cellPt d j := (sa12v3_cellPt_eq j).symm
        have e2 : cellPt d k₀ + cellPt d j = cellPt d (k₀ + j) := by
          rw [sa12v3_cellPt_eq, sa12v3_cellPt_eq, sa12v3_cellPt_eq, HRS.MS.UlocCut.uc_fp_add]
        simp only [e, e2]

end HRS.MH.AdjointRd.Phase2SA12V3
