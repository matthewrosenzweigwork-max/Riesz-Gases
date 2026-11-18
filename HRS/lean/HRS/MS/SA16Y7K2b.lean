import HRS.MS.SA16Y7K2a

/-!
# S.A.16 (SA16Y7) K2b: `L^p` norms of the derivatives of a difference quotient

For a smooth `w` and the difference `Δ_h w = w(·+h) - w`: `‖D^k Δ_h w‖_p ≤ |h| ‖D^{k+1} w‖_p` and
`‖D^k Δ_h w‖_p ≤ 2‖D^k w‖_p`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Q

open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

lemma sa16y7_iter_diff {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {w : Euc d → F}
    (hw : ContDiff ℝ ∞ w) (h : Euc d) (k : ℕ) (y : Euc d) :
    iteratedFDeriv ℝ k (fun z => w (z + h) - w z) y =
      iteratedFDeriv ℝ k w (y + h) - iteratedFDeriv ℝ k w y := by
  have hk : ContDiff ℝ k w := hw.of_le (by exact_mod_cast le_top)
  have hk' : ContDiff ℝ k (fun z => w (z + h)) := hk.comp (contDiff_id.add contDiff_const)
  have := iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := k) (x := y) (f := fun z => w (z + h)) (g := w)
    hk'.contDiffAt hk.contDiffAt
  have e : (fun z => w (z + h) - w z) = (fun z => w (z + h)) - w := rfl
  rw [e, this, iteratedFDeriv_comp_add_right]

lemma sa16y7_diff_lp_two {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : Euc d → E}
    (hg : Continuous g) {p : ℝ} (hp : 1 < p) (h : Euc d) :
    eLpNorm (fun y => ‖g (y + h) - g y‖) (ENNReal.ofReal p) volume ≤
      2 * eLpNorm (fun y => ‖g y‖) (ENNReal.ofReal p) volume := by
  have hp1 : 1 ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp.le
  have h1 : Continuous (fun y => ‖g (y + h)‖) := (hg.comp (continuous_id.add continuous_const)).norm
  have h2 : Continuous (fun y => ‖g y‖) := hg.norm
  have hmp : MeasurePreserving (fun y : Euc d => y + h) volume volume := measurePreserving_add_right volume h
  have h3 : eLpNorm (fun y => ‖g (y + h)‖) (ENNReal.ofReal p) volume =
      eLpNorm (fun y => ‖g y‖) (ENNReal.ofReal p) volume :=
    eLpNorm_comp_measurePreserving (g := fun y => ‖g y‖) h2.aestronglyMeasurable hmp
  have hmeas : AEStronglyMeasurable (fun y => ‖g (y + h) - g y‖) volume :=
    (((hg.comp (continuous_id.add continuous_const)).sub hg).norm).aestronglyMeasurable
  calc eLpNorm (fun y => ‖g (y + h) - g y‖) (ENNReal.ofReal p) volume
      ≤ eLpNorm ((fun y => ‖g (y + h)‖) + (fun y => ‖g y‖)) (ENNReal.ofReal p) volume :=
        eLpNorm_mono_ae_real hmeas (Eventually.of_forall fun y => by
          simpa [Pi.add_apply, norm_norm] using norm_sub_le (g (y + h)) (g y))
    _ ≤ eLpNorm (fun y => ‖g (y + h)‖) (ENNReal.ofReal p) volume +
          eLpNorm (fun y => ‖g y‖) (ENNReal.ofReal p) volume := eLpNorm_add_le hp1
    _ = 2 * eLpNorm (fun y => ‖g y‖) (ENNReal.ofReal p) volume := by rw [h3, two_mul]

set_option synthInstance.maxHeartbeats 200000 in
/-- `‖D^k Δ_h w‖_p ≤ |h| ‖D^{k+1} w‖_p`. -/
lemma sa16y7_Dk_diff_le {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {w : Euc d → F}
    (hw : ContDiff ℝ ∞ w) {p : ℝ} (hp : 1 < p) (h : Euc d) (k : ℕ) :
    eLpNorm (fun y => ‖iteratedFDeriv ℝ k (fun z => w (z + h) - w z) y‖) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ‖h‖ * eLpNorm (fun y => ‖iteratedFDeriv ℝ (k + 1) w y‖) (ENNReal.ofReal p) volume := by
  have hg1 : ContDiff ℝ 1 (iteratedFDeriv ℝ k w) :=
    hw.iteratedFDeriv_right (m := 1) (by exact_mod_cast le_top)
  have := sa16y7_diff_lp hg1 hp h
  simpa only [sa16y7_iter_diff hw h k, norm_fderiv_iteratedFDeriv] using this

lemma sa16y7_Dk_diff_two {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {w : Euc d → F}
    (hw : ContDiff ℝ ∞ w) {p : ℝ} (hp : 1 < p) (h : Euc d) (k : ℕ) :
    eLpNorm (fun y => ‖iteratedFDeriv ℝ k (fun z => w (z + h) - w z) y‖) (ENNReal.ofReal p) volume ≤
      2 * eLpNorm (fun y => ‖iteratedFDeriv ℝ k w y‖) (ENNReal.ofReal p) volume := by
  have hc : Continuous (iteratedFDeriv ℝ k w) :=
    hw.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have := sa16y7_diff_lp_two hc hp h
  simpa only [sa16y7_iter_diff hw h k] using this

end HRS.Whole.AppendixA.Phase2SA16Q
