import HRS.MH.ScreenedDefs

/-! Packet K5 of `B:lem:screened` (S.B.4): proof of `gk_unique` in `ScreenedSpec.lean`.
Representatives of `IsGradKernelRep` are locally integrable (bump test functions), so the difference
vanishes a.e. by `ae_eq_zero_of_integral_contDiff_smul_eq_zero`. -/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

/-- A representative `w` of `∂_i g * v` is locally integrable: test it against a bump equal to `1`
on a ball (the integrability conjunct of `IsGradKernelRep`). -/
theorem k5a_locInt {s : ℝ} (i : Fin d) {v w : Euc d → ℝ} (h : IsGradKernelRep d s i v w) :
    LocallyIntegrable w volume := by
  intro x
  let c : ContDiffBump x := ⟨1, 2, by norm_num, by norm_num⟩
  have hg : ContDiff ℝ ∞ (c : Euc d → ℝ) := c.contDiff
  have hgc : HasCompactSupport (c : Euc d → ℝ) := c.hasCompactSupport
  have hint := (h (hgc.toSchwartzMap hg)).1
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x one_pos, ?_⟩
  refine hint.integrableOn.congr_fun (fun y hy => ?_) Metric.isOpen_ball.measurableSet
  show w y * c y = w y
  rw [c.one_of_mem_closedBall (Metric.ball_subset_closedBall hy), mul_one]

theorem gk_unique_proof {s : ℝ} (i : Fin d) {v w w' : Euc d → ℝ} (h : IsGradKernelRep d s i v w)
    (h' : IsGradKernelRep d s i v w') : w =ᵐ[volume] w' := by
  have hf : LocallyIntegrable (fun x => w x - w' x) volume :=
    (k5a_locInt i h).sub (k5a_locInt i h')
  have key : ∀ g : Euc d → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      ∫ x, g x • (w x - w' x) = 0 := by
    intro g hg hgc
    obtain ⟨φ, hφ⟩ : ∃ φ : SchwartzMap (Euc d) ℝ, ⇑φ = g := ⟨hgc.toSchwartzMap hg, rfl⟩
    have hφx : ∀ x, φ x = g x := fun x => congrFun hφ x
    have h1 := h φ
    have h2 := h' φ
    have hI1 : Integrable (fun x => g x * w x) volume :=
      h1.1.congr (ae_of_all _ fun x => by
        show w x * φ x = g x * w x
        rw [hφx x, mul_comm])
    have hI2 : Integrable (fun x => g x * w' x) volume :=
      h2.1.congr (ae_of_all _ fun x => by
        show w' x * φ x = g x * w' x
        rw [hφx x, mul_comm])
    have e1 : ∫ x, g x * w x = ∫ x, w x * φ x :=
      integral_congr_ae (ae_of_all _ fun x => by
        show g x * w x = w x * φ x
        rw [hφx x, mul_comm])
    have e2 : ∫ x, g x * w' x = ∫ x, w' x * φ x :=
      integral_congr_ae (ae_of_all _ fun x => by
        show g x * w' x = w' x * φ x
        rw [hφx x, mul_comm])
    calc ∫ x, g x • (w x - w' x) = ∫ x, (g x * w x - g x * w' x) := by
          congr 1
          funext x
          rw [smul_eq_mul, mul_sub]
      _ = (∫ x, g x * w x) - ∫ x, g x * w' x := integral_sub hI1 hI2
      _ = 0 := by
          rw [e1, e2, h1.2.2, h2.2.2]
          ring
  filter_upwards [ae_eq_zero_of_integral_contDiff_smul_eq_zero hf key] with x hx
  exact sub_eq_zero.mp hx

end HRS.MH.Screened
