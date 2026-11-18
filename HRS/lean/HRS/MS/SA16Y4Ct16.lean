import HRS.MS.SA16Y4Ct15

/-!
# S.A.16 (SA16Y4) Ct16: `wrep (M_θ Y) = θ · wrep Y` a.e.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Q Phase2SA16Evolution Phase2SA16Transfer

section Ct16
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

lemma sa16y4_ellK_zero_Jcc (k : ℕ) {N : EuclideanSpace ℝ (Fin d) → ℝ} (hN : IsCcInfty N) (φ : ccSub d) :
    sa16y4_ellK (p := p) k (wZero d k) hN (sa16r_Jcc d k p φ) = ∫ x, φ.1 x * N x := by
  rw [sa16y4_ellK_apply, sa16r_Jcc_eq]
  refine integral_congr_ae ?_
  filter_upwards [sa16r_cc_elt_wrep (p := p) φ.2 k] with x hx
  rw [← hx]
  rfl

theorem sa16y4_M_wrep (k : ℕ) {θ : EuclideanSpace ℝ (Fin d) → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hθc : HasCompactSupport θ) (M : WmpSpace d k p →L[ℝ] WmpSpace d k p)
    (hM : ∀ ψ : ccSub d, M (sa16r_Jcc d k p ψ) = sa16r_Jcc d k p ⟨fun x => θ x * ψ.1 x, sa16y4_mul_cc hθ ψ.2⟩)
    (Y : WmpSpace d k p) :
    wrep d k p (M Y) =ᵐ[volume] fun x => θ x * wrep d k p Y x := by
  have hp1 : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 (le_trans one_le_two (Fact.out : 2 ≤ p))
  obtain ⟨C, hC⟩ := hθ.continuous.bounded_above_of_compact_support hθc
  have hmem : MemLp (fun x => θ x * wrep d k p Y x) (ENNReal.ofReal p) volume := by
    refine (sa16y3_wrep_memLp Y).of_le_mul (c := C) ?_ (Eventually.of_forall fun x => ?_)
    · exact (hθ.continuous.aestronglyMeasurable).mul (sa16y3_wrep_aesm Y)
    · rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)
  have hpair : ∀ {N : EuclideanSpace ℝ (Fin d) → ℝ} (hN : IsCcInfty N) (Y : WmpSpace d k p),
      sa16y4_ellK k (wZero d k) hN (M Y) = sa16y4_ellK k (wZero d k) (sa16y4_mul_cc hθ hN) Y := by
    intro N hN Y
    refine (sa16r_Jcc_dense d k p).induction_on Y (isClosed_eq ?_ ?_) (fun ψ => ?_)
    · exact (sa16y4_ellK k (wZero d k) hN).continuous.comp M.continuous
    · exact (sa16y4_ellK k (wZero d k) (sa16y4_mul_cc hθ hN)).continuous
    · rw [hM ψ, sa16y4_ellK_zero_Jcc, sa16y4_ellK_zero_Jcc]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only; ring
  refine ae_eq_of_integral_contDiff_smul_eq ((sa16y3_wrep_memLp (M Y)).locallyIntegrable hp1)
    (hmem.locallyIntegrable hp1) (fun g hg hgc => ?_)
  have hgcc : IsCcInfty g := ⟨hg, hgc⟩
  have h1 := hpair hgcc Y
  rw [sa16y4_ellK_apply, sa16y4_ellK_apply] at h1
  simp only [smul_eq_mul]
  calc ∫ x, g x * wrep d k p (M Y) x = ∫ x, wrep d k p (M Y) x * g x := by simp_rw [mul_comm]
    _ = ∫ x, wrep d k p Y x * (θ x * g x) := h1
    _ = _ := by refine integral_congr_ae (Eventually.of_forall fun x => ?_); simp only; ring
end Ct16

end HRS.Whole.AppendixA.Phase2SA16R
