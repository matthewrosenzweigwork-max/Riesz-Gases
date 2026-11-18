import HRS.Commutator.Whole.INHOMAux5

/-!
# CMX-INHOM auxiliary 6: the pairing identity for the commutator form with an odd kernel

`inhom_pairing`: for an odd kernel `H`, `𝒞_H(V,a) = 2 ∫ a(x) V(x)·(H * a)(x) dx`
(`(4.low-pairing)`/`(4.crosslow)`), under the absolute convergence hypotheses.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff Convolution

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ}

/-- `(H * a)(x) = ∫ a(y) H(x-y) dy`, vector valued. -/
def inhom_conv (H : Euc d → Euc d) (a : Euc d → ℝ) (x : Euc d) : Euc d :=
  ∫ y, a y • H (x - y)

theorem inhom_pairing {H V : Euc d → Euc d} {a : Euc d → ℝ}
    (hodd : ∀ x, H (-x) = -H x)
    (hI1 : Integrable (fun p : Euc d × Euc d => inner ℝ (V p.1) (H (p.1 - p.2)) * a p.1 * a p.2)
      (volume.prod volume))
    (hI2 : Integrable (fun p : Euc d × Euc d => inner ℝ (V p.2) (H (p.1 - p.2)) * a p.1 * a p.2)
      (volume.prod volume))
    (hHb : ∀ x, Integrable (fun y => a y • H (x - y)) volume) :
    CcommFun H V a = 2 * ∫ x, a x * inner ℝ (V x) (inhom_conv H a x) := by
  have hkey : ∀ x y : Euc d, commKer H V x y * a x * a y =
      inner ℝ (V x) (H (x - y)) * a x * a y - inner ℝ (V y) (H (x - y)) * a x * a y := by
    intro x y
    rw [lowv_commKer_eq]
    unfold lowv_K
    rw [inner_sub_left]; ring
  have hint : Integrable (fun p : Euc d × Euc d => commKer H V p.1 p.2 * a p.1 * a p.2)
      (volume.prod volume) := by
    refine (hI1.sub hI2).congr (Eventually.of_forall fun p => ?_)
    simp only [Pi.sub_apply]
    rw [hkey]
  -- first piece
  have hP1 : ∫ x, ∫ y, inner ℝ (V x) (H (x - y)) * a x * a y =
      ∫ x, a x * inner ℝ (V x) (inhom_conv H a x) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have e : ∀ y : Euc d, inner ℝ (V x) (H (x - y)) * a x * a y =
        a x * inner ℝ (V x) (a y • H (x - y)) := by
      intro y
      rw [inner_smul_right]; ring
    simp_rw [e]
    rw [integral_const_mul, integral_inner (hHb x)]
    rfl
  -- second piece
  have hHb' : ∀ y, Integrable (fun x => a x • H (x - y)) volume := by
    intro y
    have := (hHb y).neg
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.neg_apply]
    have : H (x - y) = -H (y - x) := by
      rw [← hodd, neg_sub]
    rw [this, smul_neg]
  have hP2 : ∫ x, ∫ y, inner ℝ (V y) (H (x - y)) * a x * a y =
      -∫ y, a y * inner ℝ (V y) (inhom_conv H a y) := by
    rw [integral_integral_swap hI2, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    have e : ∀ x : Euc d, inner ℝ (V y) (H (x - y)) * a x * a y =
        a y * inner ℝ (V y) (a x • H (x - y)) := by
      intro x
      rw [inner_smul_right]; ring
    simp only
    simp_rw [e]
    rw [integral_const_mul, integral_inner (hHb' y)]
    have : ∫ x, a x • H (x - y) = -inhom_conv H a y := by
      unfold inhom_conv
      rw [← integral_neg]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      have : H (x - y) = -H (y - x) := by rw [← hodd, neg_sub]
      simp only [this, smul_neg]
    rw [this, inner_neg_right]
    ring
  unfold CcommFun
  rw [← integral_prod _ hint]
  have e2 : (fun p : Euc d × Euc d => commKer H V p.1 p.2 * a p.1 * a p.2) =
      fun p : Euc d × Euc d => inner ℝ (V p.1) (H (p.1 - p.2)) * a p.1 * a p.2 -
        inner ℝ (V p.2) (H (p.1 - p.2)) * a p.1 * a p.2 := by
    funext p; exact hkey p.1 p.2
  rw [e2, integral_sub hI1 hI2, integral_prod _ hI1, integral_prod _ hI2, hP1, hP2]
  ring

end HRS.Commutator.Whole
