import HRS.Commutator.Whole.XNRSAux32
import HRS.Commutator.Whole.LocalAuxSAMP7

/-!
# Packet X-NRS, part 33: mollification of a transport field
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv Convolution

noncomputable section

namespace HRS.Commutator.Whole.XNRS

variable {d : ℕ}

open HRS.Commutator.Whole HRS.Commutator.Whole.SAMP1

/-- A mollifying kernel: continuous, compactly supported, nonnegative of integral one. -/
structure XMolKer (k : Euc d → ℝ) : Prop where
  cont : Continuous k
  cpt : HasCompactSupport k
  nonneg : ∀ x, 0 ≤ k x
  integral : ∫ x, k x = 1

namespace XMolKer

lemma integrable {k : Euc d → ℝ} (hk : XMolKer k) : Integrable k := hk.cont.integrable_of_hasCompactSupport hk.cpt

lemma moment {k : Euc d → ℝ} (hk : XMolKer k) : Integrable (fun y : Euc d => ‖y‖ * |k y|) := by
  refine (continuous_norm.mul hk.cont.abs).integrable_of_hasCompactSupport ?_
  exact (hk.cpt.abs).mul_left

lemma norm_integral {k : Euc d → ℝ} (hk : XMolKer k) : ∫ y, ‖k y‖ = 1 := by
  have : ∀ y, ‖k y‖ = k y := fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (hk.nonneg y)]
  simp_rw [this]; exact hk.integral

end XMolKer

/-- Mollification `k * v`. -/
def xmol (k : Euc d → ℝ) (v : Euc d → Euc d) (x : Euc d) : Euc d := ∫ y, k y • v (x - y)

lemma xmol_integrable {k : Euc d → ℝ} (hk : XMolKer k) {v : Euc d → Euc d} {L : ℝ≥0}
    (hL : LipschitzWith L v) (x : Euc d) : Integrable (fun y => k y • v (x - y)) := by
  have hb : Integrable (fun y : Euc d => (‖v x‖ + L * ‖y‖) * |k y|) := by
    have h1 := hk.integrable.norm.const_mul ‖v x‖
    have h2 := hk.moment.const_mul (L : ℝ)
    refine (h1.add h2).congr (Eventually.of_forall fun y => ?_)
    simp only [Pi.add_apply, Real.norm_eq_abs]; ring
  refine hb.mono' ((hk.cont.smul (hL.continuous.comp (continuous_const.sub
    continuous_id))).aestronglyMeasurable) (Eventually.of_forall fun y => ?_)
  rw [norm_smul, Real.norm_eq_abs, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  have h3 := lip_norm_le hL (x - y) x
  calc ‖v (x - y)‖ ≤ ‖v x‖ + ‖v (x - y) - v x‖ := by
        calc ‖v (x - y)‖ = ‖(v (x - y) - v x) + v x‖ := by rw [sub_add_cancel]
          _ ≤ _ := by rw [add_comm]; exact norm_add_le _ _
    _ ≤ ‖v x‖ + L * ‖(x - y) - x‖ := by gcongr
    _ = ‖v x‖ + L * ‖y‖ := by rw [sub_sub_cancel_left, norm_neg]

lemma xmol_lip {k : Euc d → ℝ} (hk : XMolKer k) {v : Euc d → Euc d} {L : ℝ≥0}
    (hL : LipschitzWith L v) (x x' : Euc d) :
    ‖xmol k v x - xmol k v x'‖ ≤ L * ‖x - x'‖ := by
  have e : xmol k v x - xmol k v x' = ∫ y : Euc d, k y • (v (x - y) - v (x' - y)) := by
    unfold xmol
    rw [← integral_sub (xmol_integrable hk hL x) (xmol_integrable hk hL x')]
    simp_rw [smul_sub]
  rw [e]
  have hb : Integrable (fun y : Euc d => |k y| * (L * ‖x - x'‖)) := hk.integrable.abs.mul_const _
  refine (norm_integral_le_of_norm_le hb (Eventually.of_forall fun y => ?_)).trans ?_
  · rw [norm_smul, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have := lip_norm_le hL (x - y) (x' - y)
    rwa [sub_sub_sub_cancel_right] at this
  · rw [integral_mul_const]
    have : ∫ y, |k y| = 1 := by
      have := hk.norm_integral
      simpa [Real.norm_eq_abs] using this
    rw [this, one_mul]

lemma xmol_close {k : Euc d → ℝ} (hk : XMolKer k) {v : Euc d → Euc d} {L : ℝ≥0}
    (hL : LipschitzWith L v) {R : ℝ} (hR : ∀ y, k y ≠ 0 → ‖y‖ ≤ R) (x : Euc d) :
    ‖xmol k v x - v x‖ ≤ L * R := by
  have e : xmol k v x - v x = ∫ y : Euc d, k y • (v (x - y) - v x) := by
    have h1 : ∫ y : Euc d, k y • v x = v x := by
      rw [integral_smul_const, hk.integral, one_smul]
    have h2 : Integrable (fun y : Euc d => k y • v x) := hk.integrable.smul_const _
    simp_rw [smul_sub]
    rw [integral_sub (xmol_integrable hk hL x) h2, h1]
    rfl
  rw [e]
  have hb : Integrable (fun y : Euc d => |k y| * (L * R)) := hk.integrable.abs.mul_const _
  refine (norm_integral_le_of_norm_le hb (Eventually.of_forall fun y => ?_)).trans ?_
  · by_cases hy : k y = 0
    · simp [hy]
    · rw [norm_smul, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have := lip_norm_le hL (x - y) x
      rw [sub_sub_cancel_left, norm_neg] at this
      exact this.trans (mul_le_mul_of_nonneg_left (hR y hy) L.2)
  · rw [integral_mul_const]
    have : ∫ y, |k y| = 1 := by
      have := hk.norm_integral
      simpa [Real.norm_eq_abs] using this
    rw [this, one_mul]

end HRS.Commutator.Whole.XNRS
