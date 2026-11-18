import HRS.Main.A8PAux47

/-!
# Packet A8P, part 48: the Itô drift of `G_ε` along a real semimartingale
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

theorem a8pG1_fderiv {ε : ℝ} (hε : 0 < ε) (z w : ℝ) : fderiv ℝ (a8pG1 ε) z w = w * a8pG1' ε z := by
  rw [(a8pG1_hasDerivAt hε z).hasFDerivAt.fderiv]
  simp

theorem a8pG1_fderiv_fun {ε : ℝ} (hε : 0 < ε) :
    fderiv ℝ (a8pG1 ε) = fun y => (a8pG1' ε y) • (ContinuousLinearMap.id ℝ ℝ) := by
  funext y
  ext
  simp [(a8pG1_hasDerivAt hε y).deriv]

theorem a8pG1_fderiv2 {ε : ℝ} (hε : 0 < ε) (z w v : ℝ) :
    fderiv ℝ (fderiv ℝ (a8pG1 ε)) z w v = w * v * a8pG1'' ε z := by
  rw [a8pG1_fderiv_fun hε]
  have h := ((a8pG1'_hasDerivAt hε z).hasFDerivAt.smul_const (ContinuousLinearMap.id ℝ ℝ))
  rw [h.fderiv]
  simp
  ring

end HRS.Main.A8P
