import HRS.MS.R26T8AP17c
import HRS.MS.R26T8AP07r

/-!
# S8.2 local Newton layer, packet T8A.P17 (part d): local bilinear Leibniz bound
`r26t8a_p17_local_bilinear`: for `B` bilinear, `u` smooth only on `{w != 0}`, `Gf` globally smooth and `z != 0`:
`‖nest p q (Y,w |-> B (u w) (Gf (Y,w))) X z‖ <= ‖B‖ ∑_i C(q,i) ‖D^i u z‖ ‖nest p (q-i) Gf X z‖` (a bump in `w` around `z` makes `u` global).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff
open HRS HRS.Whole HRS.MS.Phase2S82

namespace HRS.MS.R26T8A

variable {d : ℕ}

theorem r26t8a_p07_congr_ball_gen {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (p q : ℕ)
    (Φ Φ' : Euc d × Euc d → V) {ρ : ℝ} (hρ : 0 < ρ) (X z : Euc d)
    (hΦ : ∀ Y w : Euc d, ‖w - z‖ < ρ → Φ (Y, w) = Φ' (Y, w)) :
    r26t8a_nest p q Φ X z = r26t8a_nest p q Φ' X z := by
  unfold r26t8a_nest
  have h : ∀ Y : Euc d, iteratedFDeriv ℝ q (fun w => Φ (Y, w)) z = iteratedFDeriv ℝ q (fun w => Φ' (Y, w)) z := by
    intro Y
    have hev : (fun w => Φ (Y, w)) =ᶠ[𝓝 z] fun w => Φ' (Y, w) := by
      filter_upwards [ball_mem_nhds z hρ] with w hw
      exact hΦ Y w (by simpa [dist_eq_norm] using hw)
    exact (hev.iteratedFDeriv ℝ q).self_of_nhds
  simp only [h]

theorem r26t8a_p17_local_bilinear {F1 F2 F3 : Type} [NormedAddCommGroup F1] [NormedSpace ℝ F1]
    [NormedAddCommGroup F2] [NormedSpace ℝ F2] [NormedAddCommGroup F3] [NormedSpace ℝ F3]
    (B : F1 →L[ℝ] F2 →L[ℝ] F3) (p q : ℕ) {u : Euc d → F1}
    (hu : ContDiffOn ℝ ((p + q : ℕ) : WithTop ℕ∞) u {w : Euc d | w ≠ 0}) {Gf : Euc d × Euc d → F2}
    (hG : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) Gf) (X z : Euc d) (hz : z ≠ 0) :
    ‖r26t8a_nest p q (fun Yw : Euc d × Euc d => B (u Yw.2) (Gf Yw)) X z‖ ≤
      ‖B‖ * ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * ‖iteratedFDeriv ℝ i u z‖ *
        ‖r26t8a_nest p (q - i) Gf X z‖ := by
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
  set ρ : ℝ := ‖z‖ / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  let bump : ContDiffBump z := ⟨ρ / 2, ρ, by positivity, by linarith⟩
  have hbc : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (fun w => bump w) :=
    bump.contDiff.of_le (by exact_mod_cast le_top)
  have hopen : IsOpen {w : Euc d | w ≠ 0} := isOpen_ne
  have hû : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (fun w => bump w • u w) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : ‖x - z‖ ≤ ρ
    · have hx0 : x ∈ {w : Euc d | w ≠ 0} := by
        intro h0
        rw [h0, zero_sub, norm_neg] at hx
        linarith
      exact (hbc.contDiffAt).smul (hu.contDiffAt (hopen.mem_nhds hx0))
    · push Not at hx
      have hev : (fun w => bump w • u w) =ᶠ[𝓝 x] fun _ => (0 : F1) := by
        have hop : IsOpen {w : Euc d | ρ < ‖w - z‖} := isOpen_lt continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))
        filter_upwards [hop.mem_nhds hx] with y hy
        have : bump y = 0 := bump.zero_of_le_dist (by rw [dist_eq_norm]; exact le_of_lt hy)
        simp [this]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have hone : ∀ w : Euc d, ‖w - z‖ < ρ / 2 → bump w = 1 := fun w hw =>
    bump.one_of_mem_closedBall (by rw [mem_closedBall, dist_eq_norm]; exact hw.le)
  have e1 : r26t8a_nest p q (fun Yw : Euc d × Euc d => B (u Yw.2) (Gf Yw)) X z =
      r26t8a_nest p q (fun Yw : Euc d × Euc d => B (bump Yw.2 • u Yw.2) (Gf Yw)) X z :=
    r26t8a_p07_congr_ball_gen p q _ _ (by positivity : 0 < ρ / 2) X z fun Y w hw => by
      simp [hone w hw]
  have e2 : ∀ i, iteratedFDeriv ℝ i (fun w => bump w • u w) z = iteratedFDeriv ℝ i u z := fun i => by
    have hev : (fun w => bump w • u w) =ᶠ[𝓝 z] u := by
      filter_upwards [ball_mem_nhds z (by positivity : 0 < ρ / 2)] with w hw
      simp [hone w (by simpa [dist_eq_norm] using hw)]
    exact (hev.iteratedFDeriv ℝ i).self_of_nhds
  rw [e1]
  have := r26t8a_nest_bilinear q p B (fun w => bump w • u w) Gf X z hû hG
  refine this.trans (le_of_eq ?_)
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [e2 i]

end HRS.MS.R26T8A
