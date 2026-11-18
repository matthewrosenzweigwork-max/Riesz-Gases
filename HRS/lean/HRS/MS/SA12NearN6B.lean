import HRS.MS.SA12NearN6A
import HRS.MS.SA12CompB3Z
import HRS.MS.SA12CompB4A
import HRS.MS.UniqN0b
import HRS.MP.RdRemainder

/-!
# S.A.12 N6, part B: the cut-off kernel and the integration-by-parts bound
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

/-- A `C_c^∞` kernel that equals the Riesz kernel on the shell `h/2 < |z| < R`. -/
theorem sa12n_cutoff_kernel (s : ℝ) {h R : ℝ} (hh : 0 < h) (hR : 0 < R) :
    ∃ Gh : Euc d → ℝ, ContDiff ℝ ∞ Gh ∧ HasCompactSupport Gh ∧
      ∀ z : Euc d, h / 2 < ‖z‖ → ‖z‖ < R → Gh =ᶠ[𝓝 z] rieszKernel d s := by
  let b : ContDiffBump (0 : Euc d) := ⟨h / 4, h / 2, by positivity, by linarith⟩
  let η : ContDiffBump (0 : Euc d) := ⟨R, R + 1, hR, by linarith⟩
  refine ⟨fun z => η z * ((1 - b z) * rieszKernel d s z), ?_, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro z
    refine η.contDiff.contDiffAt.mul ?_
    by_cases hz : z = 0
    · subst hz
      have hev : (fun w : Euc d => (1 - b w) * rieszKernel d s w) =ᶠ[𝓝 0] fun _ => 0 := by
        filter_upwards [Metric.ball_mem_nhds (0 : Euc d) (show 0 < h / 4 by positivity)] with w hw
        have : b w = 1 := b.one_of_mem_closedBall (by
          rw [Metric.mem_closedBall]; exact (Metric.mem_ball.1 hw).le)
        simp [this]
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · refine (contDiffAt_const.sub b.contDiff.contDiffAt).mul ?_
      exact (rieszKernel_contDiffOn (d := d) (s := s)).contDiffAt
        ((isOpen_ne : IsOpen {x : Euc d | x ≠ 0}).mem_nhds hz)
  · exact η.hasCompactSupport.mul_right
  · intro z hz1 hz2
    have hopen : IsOpen {w : Euc d | h / 2 < ‖w‖ ∧ ‖w‖ < R} :=
      (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
    filter_upwards [hopen.mem_nhds ⟨hz1, hz2⟩] with w hw
    have h1 : η w = 1 := η.one_of_mem_closedBall (by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hw.2.le)
    have h2 : b w = 0 := b.zero_of_le_dist (by rw [dist_zero_right]; exact hw.1.le)
    simp [h1, h2]

/-- Integration by parts in the source variable: only `F` itself remains. -/
theorem sa12n_conv_ibp_bound {a F P : Euc d → ℝ} (ha : MemCb 1 a) (hF : ContDiff ℝ ∞ F)
    (hP : ContDiff ℝ ∞ P) {c : Euc d} {ρ : ℝ} (hts : tsupport a ⊆ Metric.closedBall c ρ)
    (j : Fin d) (x : Euc d) {B1 B2 : ℝ} (hB1n : 0 ≤ B1) (hB2n : 0 ≤ B2)
    (hB1 : ∀ y ∈ tsupport a, |P (x - y)| ≤ B1)
    (hB2 : ∀ y ∈ tsupport a, |fderiv ℝ P (x - y) (EuclideanSpace.single j (1 : ℝ))| ≤ B2) :
    |sa12n_conv (fun y => a y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ))) P x| ≤
      cbNorm 1 a * (B1 + B2) * ∫ y in Metric.closedBall c ρ, |F y| := by
  have hacs : HasCompactSupport a :=
    IsCompact.of_isClosed_subset (isCompact_closedBall c ρ) (isClosed_tsupport a) hts
  have ha1 : ContDiff ℝ 1 a := by simpa using ha.1
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by exact_mod_cast le_top)
  have hP1 : ContDiff ℝ 1 P := hP.of_le (by exact_mod_cast le_top)
  set e : Euc d := EuclideanSpace.single j (1 : ℝ) with he
  have hen : ‖e‖ = 1 := by simp [he]
  set h : Euc d → ℝ := fun y => a y * P (x - y) with hh
  have hPx : ContDiff ℝ 1 (fun y => P (x - y)) := hP1.comp (contDiff_const.sub contDiff_id)
  have hh1 : ContDiff ℝ 1 h := ha1.mul hPx
  have hhc : HasCompactSupport h := hacs.mul_right
  have hibp := HRS.MS.UniqN0.n0_ibp (F := h) (k := F) hh1 hhc (fun t _ => hF1.contDiffAt) e
  have cbnn : 0 ≤ cbNorm 1 a := HRS.MH.AdjointRd.Phase2SA12Companions.sa12z_cb_nonneg ha
  unfold sa12n_conv
  have e1 : ∫ y, (a y * fderiv ℝ F y e) * P (x - y) = -∫ y, F y * fderiv ℝ h y e := by
    have : ∫ y, (a y * fderiv ℝ F y e) * P (x - y) = ∫ t, fderiv ℝ F t e * h t :=
      integral_congr_ae (Eventually.of_forall fun y => by simp only [hh]; ring)
    rw [this]; linarith [hibp]
  rw [e1, abs_neg]
  -- derivative of `h`
  have hdh : ∀ y, fderiv ℝ h y e = -(a y * fderiv ℝ P (x - y) e) + P (x - y) * fderiv ℝ a y e := by
    intro y
    have h0 := (hP1.differentiable (by norm_num) (x - y)).hasFDerivAt.comp y
      ((hasFDerivAt_id y).const_sub x)
    have hPd : HasFDerivAt (fun y => P (x - y)) (-(fderiv ℝ P (x - y))) y :=
      h0.congr_fderiv (by ext v; simp)
    have had : HasFDerivAt a (fderiv ℝ a y) y := (ha1.differentiable (by norm_num) y).hasFDerivAt
    have hm : HasFDerivAt h (a y • (-(fderiv ℝ P (x - y))) + P (x - y) • fderiv ℝ a y) y :=
      had.mul hPd
    rw [hm.fderiv]
    simp
  have hcb0 : ∀ y, |a y| ≤ cbNorm 1 a := fun y => HRS.MP.RdRem.mrr_abs_le_cbNorm ha y
  have hcb1 : ∀ y, |fderiv ℝ a y e| ≤ cbNorm 1 a := by
    intro y
    have h1 : ‖fderiv ℝ a y‖ ≤ cbNorm 1 a := by
      rw [← norm_iteratedFDeriv_one]
      exact HRS.MH.AdjointRd.Phase2SA12Companions.sa12z_norm_iteratedFDeriv_le_cbNorm ha le_rfl y
    calc |fderiv ℝ a y e| = ‖fderiv ℝ a y e‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ a y‖ * ‖e‖ := (fderiv ℝ a y).le_opNorm e
      _ ≤ cbNorm 1 a := by rw [hen, mul_one]; exact h1
  set K : ℝ := cbNorm 1 a * (B1 + B2) with hK
  have hpt : ∀ y, ‖F y * fderiv ℝ h y e‖ ≤
      K * (Metric.closedBall c ρ).indicator (fun y => |F y|) y := by
    intro y
    by_cases hy : y ∈ tsupport a
    · rw [Set.indicator_of_mem (hts hy), hdh y, Real.norm_eq_abs, abs_mul]
      have h1 : |-(a y * fderiv ℝ P (x - y) e) + P (x - y) * fderiv ℝ a y e| ≤ K := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_neg, abs_mul, abs_mul, hK]
        have := mul_le_mul (hcb0 y) (hB2 y hy) (abs_nonneg _) cbnn
        have := mul_le_mul (hB1 y hy) (hcb1 y) (abs_nonneg _) hB1n
        nlinarith
      calc |F y| * |-(a y * fderiv ℝ P (x - y) e) + P (x - y) * fderiv ℝ a y e|
          ≤ |F y| * K := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ = K * |F y| := by ring
    · have hz : fderiv ℝ h y = 0 := by
        by_contra hne
        exact hy (tsupport_mul_subset_left (f := a) (g := fun y => P (x - y))
          ((support_fderiv_subset (𝕜 := ℝ)) (Function.mem_support.2 hne)))
      have hnn : 0 ≤ K * (Metric.closedBall c ρ).indicator (fun y => |F y|) y := by
        have : 0 ≤ (Metric.closedBall c ρ).indicator (fun y => |F y|) y :=
          Set.indicator_nonneg (fun _ _ => abs_nonneg _) y
        have hK0 : 0 ≤ K := by rw [hK]; positivity
        positivity
      simpa [hz] using hnn
  have hint : Integrable ((Metric.closedBall c ρ).indicator (fun y => |F y|)) volume :=
    (hF.continuous.abs.continuousOn.integrableOn_compact (isCompact_closedBall c ρ)).integrable_indicator
      Metric.isClosed_closedBall.measurableSet
  calc |∫ y, F y * fderiv ℝ h y e| = ‖∫ y, F y * fderiv ℝ h y e‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ y, K * (Metric.closedBall c ρ).indicator (fun y => |F y|) y :=
        norm_integral_le_of_norm_le (hint.const_mul K) (Eventually.of_forall hpt)
    _ = K * ∫ y in Metric.closedBall c ρ, |F y| := by
        rw [integral_const_mul, integral_indicator Metric.isClosed_closedBall.measurableSet]

end HRS.MH.AdjointRd.Phase2SA12Near
