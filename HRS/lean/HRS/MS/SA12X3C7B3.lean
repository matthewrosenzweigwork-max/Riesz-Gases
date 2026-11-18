import HRS.MS.SA12X3C7B2

/-!
# S.A.12 C7 (SA12X3), part B3: the derivative bound for the smooth-kernel term
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.MS.UniqT3 HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12
  HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12x3_smooth_pd {q : Euc d → ℝ} (hq : ContDiff ℝ ∞ q) (m : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ Kk : ℝ, 0 ≤ Kk ∧ ∀ (L : ℝ), 1 ≤ L → ∀ (i : Fin d) (c : Euc d) (g : Euc d → ℝ), Continuous g →
      tsupport g ⊆ ball c ρ → ∀ n ≤ m, ∀ idx : Fin n → Fin d, ∀ x ∈ ball c ρ,
      |partialDeriv idx (fun x => ∫ y, fderiv ℝ q (L⁻¹ • (x - y)) (EuclideanSpace.single i (1 : ℝ)) * g y) x| ≤
        Kk * ∫ y, |g y| := by
  let ψ : ContDiffBump (0 : Euc d) := ⟨2 * ρ, 2 * ρ + 1, by linarith, by linarith⟩
  have hψ : ContDiff ℝ ∞ (⇑ψ) := ψ.contDiff
  obtain ⟨Bψ, hBψ0, hBψ⟩ := sa12x3_jets_bounded hψ ψ.hasCompactSupport m
  obtain ⟨Q, hQ0, hQ⟩ := sa12x3_kernel_jets hq m (2 * ρ + 1)
  refine ⟨2 ^ m * (Bψ * Q), by positivity, ?_⟩
  intro L hL i c g hg hgs n hn idx x hx
  set e : Euc d := EuclideanSpace.single i (1 : ℝ) with he
  have hne : ‖e‖ ≤ 1 := by simp [he]
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  set kL : Euc d → ℝ := fun u => fderiv ℝ q (L⁻¹ • u) e with hkL
  have hkLc : ContDiff ℝ ∞ kL := by
    have h1 : ContDiff ℝ ∞ (fderiv ℝ q) := hq.fderiv_right (m := ∞) (by simp)
    exact (h1.comp (contDiff_id.const_smul L⁻¹)).clm_apply contDiff_const
  set kt : Euc d → ℝ := fun u => ψ u * kL u with hkt
  have hktc : ContDiff ℝ ∞ kt := hψ.mul hkLc
  have hktcs : HasCompactSupport kt := ψ.hasCompactSupport.mul_right
  have hktT : tsupport kt ⊆ closedBall (0 : Euc d) (2 * ρ + 1) := by
    refine tsupport_mul_subset_left.trans ?_
    rw [ψ.tsupport_eq]
  -- the cut kernel agrees with the kernel on the relevant region
  have hEq : EqOn (fun x => ∫ y, kL (x - y) * g y) (fun x => ∫ y, kt (x - y) * g y) (ball c ρ) := by
    intro x' hx'
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    by_cases hy : g y = 0
    · simp [hy]
    · have hyb : y ∈ ball c ρ := hgs (subset_tsupport _ hy)
      have : ‖x' - y‖ ≤ 2 * ρ := by
        have h1 := mem_ball_iff_norm.1 hx'
        have h2 := mem_ball_iff_norm.1 hyb
        calc ‖x' - y‖ = ‖(x' - c) - (y - c)‖ := by congr 1; abel
          _ ≤ ‖x' - c‖ + ‖y - c‖ := norm_sub_le _ _
          _ ≤ 2 * ρ := by linarith
      have h1 : ψ (x' - y) = 1 := ψ.one_of_mem_closedBall (by simpa [ψ] using this)
      simp only [hkt, h1, one_mul]
  have hpd := sa12x3_pd_congr_open (isOpen_ball (x := c) (ε := ρ)) hEq idx hx
  -- convolution form
  have hconv : (fun x' => ∫ y, kt (x' - y) * g y) = HRS.Whole.convFun g kt := by
    funext x'
    have h := integral_sub_left_eq_self (μ := (volume : Measure (Euc d)))
      (fun t => kt (x' - t) * g t) x'
    simp only [sub_sub_cancel] at h
    unfold HRS.Whole.convFun
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    ring
  have hgi : LocallyIntegrable g (volume : Measure (Euc d)) := hg.locallyIntegrable
  have hgcs : HasCompactSupport g := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c ρ) fun y hy => ?_
    exact (closure_minimal (fun z hz => hgs (subset_tsupport g hz) |> fun h => ball_subset_closedBall h)
      isClosed_closedBall : tsupport g ⊆ _) (subset_tsupport _ hy)
  have hpc := sa12x3_pd_conv_gen hgi n kt (hktc.of_le (sa12x2_le_top n)) hktcs idx x
  rw [hpd, hconv, hpc]
  -- bound the convolution
  have hbd : ∀ y, |partialDeriv idx kt y| ≤ 2 ^ m * (Bψ * Q) := by
    intro y
    by_cases hy : ‖y‖ ≤ 2 * ρ + 1
    · refine (sa12x2_pd_le_norm kt idx y).trans ?_
      have hle := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := ⇑ψ) (g := kL) (N := ∞)
        (hψ) hkLc y (n := n) (sa12x2_le_top n)
      refine hle.trans ?_
      have hterm : ∀ a ∈ Finset.range (n + 1),
          (n.choose a : ℝ) * ‖iteratedFDeriv ℝ a (⇑ψ) y‖ * ‖iteratedFDeriv ℝ (n - a) kL y‖ ≤
            (n.choose a : ℝ) * (Bψ * Q) := by
        intro a ha
        have h1 := hBψ a (by have := Finset.mem_range.1 ha; omega) y
        have h2 := hQ L hL e hne (n - a) (by omega) y (by linarith [hy])
        calc (n.choose a : ℝ) * ‖iteratedFDeriv ℝ a (⇑ψ) y‖ * ‖iteratedFDeriv ℝ (n - a) kL y‖
            = (n.choose a : ℝ) * (‖iteratedFDeriv ℝ a (⇑ψ) y‖ * ‖iteratedFDeriv ℝ (n - a) kL y‖) := by ring
          _ ≤ (n.choose a : ℝ) * (Bψ * Q) := by
              gcongr
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      have : (2 : ℝ) ^ n ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hn
      push_cast
      exact mul_le_mul_of_nonneg_right this (by positivity)
    · have : y ∉ closedBall (0 : Euc d) (2 * ρ + 1) := by simpa using hy
      rw [sa12x2_pd_zero_gen hktT idx this]
      simp only [abs_zero]
      positivity
  have hI1 : Integrable (fun y => g (x - y) * partialDeriv idx kt y) := by
    have hc : Continuous (partialDeriv idx kt) := (sa12x2_pd_cd (k := 0) (by simpa using hktc.of_le (sa12x2_le_top n)) idx).continuous
    refine Continuous.integrable_of_hasCompactSupport (hg.comp (continuous_const.sub continuous_id) |>.mul hc) ?_
    refine HasCompactSupport.intro (K := tsupport (partialDeriv idx kt))
      (sa12z3_pd_compact hktcs idx).isCompact ?_
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport hy]
    simp
  have hI2 : Integrable (fun y => |g (x - y)|) := by
    have hgm : Integrable g := hg.integrable_of_hasCompactSupport hgcs
    have := hgm.comp_sub_left x
    exact this.abs
  have hmaj : Integrable (fun y => |g (x - y)| * (2 ^ m * (Bψ * Q))) := hI2.mul_const _
  calc |HRS.Whole.convFun g (partialDeriv idx kt) x| = |∫ y, g (x - y) * partialDeriv idx kt y| := rfl
    _ ≤ ∫ y, |g (x - y) * partialDeriv idx kt y| := abs_integral_le_integral_abs
    _ ≤ ∫ y, |g (x - y)| * (2 ^ m * (Bψ * Q)) := by
        refine integral_mono hI1.abs hmaj fun y => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hbd y) (abs_nonneg _)
    _ = (2 ^ m * (Bψ * Q)) * ∫ y, |g y| := by
        rw [integral_mul_const, mul_comm]
        congr 1
        exact integral_sub_left_eq_self (μ := (volume : Measure (Euc d))) (fun t => |g t|) x

end HRS.MH.AdjointRd.Phase2SA12Near
