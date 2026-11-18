import HRS.MS.R26T8AP07q
import HRS.MS.R26T8AP01b

/-!
# S8.2 local Newton layer, packet T8A.P07 (part r): a local Leibniz bound for `a(w) * N(Y,w)` with `N` smooth only near `z`
`r26t8a_p07_local_product`: if `N` is `C^(p+q)` on `{0 < |w| < 3}` and `0 < |z| <= 2`, then the nested jet of `a(w) N(Y,w)` at `(X,z)` obeys the usual
Leibniz bound (a bump in `w` around `z` makes `N` globally smooth without changing the jets at `(X,z)`).
-/

set_option autoImplicit false
noncomputable section
open Filter Topology Metric
open scoped ContDiff

namespace HRS.MS.R26T8A

variable {d : ℕ}

theorem r26t8a_p07_congr_ball (p q : ℕ) (Φ Φ' : Euc d × Euc d → ℝ) {ρ : ℝ} (hρ : 0 < ρ) (X z : Euc d)
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

theorem r26t8a_p07_local_product (p q : ℕ) {a : Euc d → ℝ} (ha : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) a)
    {N : Euc d × Euc d → ℝ}
    (hN : ContDiffOn ℝ ((p + q : ℕ) : WithTop ℕ∞) N {Yw : Euc d × Euc d | 0 < ‖Yw.2‖ ∧ ‖Yw.2‖ < 3})
    (X z : Euc d) (hz0 : 0 < ‖z‖) (hz2 : ‖z‖ ≤ 2) :
    ‖r26t8a_nest p q (fun Yw => a Yw.2 * N Yw) X z‖ ≤
      ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * ‖iteratedFDeriv ℝ i a z‖ * ‖r26t8a_nest p (q - i) N X z‖ := by
  set ρ : ℝ := min (‖z‖ / 4) (1 / 2) with hρ
  have hρ0 : 0 < ρ := lt_min (by positivity) (by norm_num)
  have hρ1 : ρ ≤ ‖z‖ / 4 := min_le_left _ _
  have hρ2 : ρ ≤ 1 / 2 := min_le_right _ _
  let bump : ContDiffBump z := ⟨ρ / 2, ρ, by positivity, by linarith⟩
  have hbc : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (fun w => bump w) :=
    bump.contDiff.of_le (by exact_mod_cast le_top)
  have hopen : IsOpen {Yw : Euc d × Euc d | 0 < ‖Yw.2‖ ∧ ‖Yw.2‖ < 3} :=
    (isOpen_lt continuous_const (continuous_norm.comp continuous_snd)).inter
      (isOpen_lt (continuous_norm.comp continuous_snd) continuous_const)
  have hG : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (fun Yw : Euc d × Euc d => bump Yw.2 * N Yw) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : ‖x.2 - z‖ ≤ ρ
    · have hxU : x ∈ {Yw : Euc d × Euc d | 0 < ‖Yw.2‖ ∧ ‖Yw.2‖ < 3} := by
        have h1 := norm_sub_norm_le z x.2
        have h2 := norm_le_insert' x.2 z
        rw [norm_sub_rev] at h1
        exact ⟨by linarith, by linarith⟩
      exact ((hbc.comp contDiff_snd).contDiffAt).mul (hN.contDiffAt (hopen.mem_nhds hxU))
    · push Not at hx
      have hev : (fun Yw : Euc d × Euc d => bump Yw.2 * N Yw) =ᶠ[𝓝 x] fun _ => 0 := by
        have hop : IsOpen {Yw : Euc d × Euc d | ρ < ‖Yw.2 - z‖} :=
          isOpen_lt continuous_const (continuous_norm.comp (continuous_snd.sub continuous_const))
        filter_upwards [hop.mem_nhds hx] with y hy
        have : bump y.2 = 0 := bump.zero_of_le_dist (by rw [dist_eq_norm]; exact le_of_lt hy)
        simp [this]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have hone : ∀ w : Euc d, ‖w - z‖ < ρ / 2 → bump w = 1 := fun w hw =>
    bump.one_of_mem_closedBall (by rw [mem_closedBall, dist_eq_norm]; exact hw.le)
  have e1 : r26t8a_nest p q (fun Yw => a Yw.2 * N Yw) X z =
      r26t8a_nest p q (fun Yw => a Yw.2 * (bump Yw.2 * N Yw)) X z :=
    r26t8a_p07_congr_ball p q _ _ (by positivity : 0 < ρ / 2) X z fun Y w hw => by
      simp [hone w hw]
  have e2 : ∀ j, r26t8a_nest p j N X z = r26t8a_nest p j (fun Yw => bump Yw.2 * N Yw) X z := fun j =>
    r26t8a_p07_congr_ball p j _ _ (by positivity : 0 < ρ / 2) X z fun Y w hw => by
      simp [hone w hw]
  rw [e1]
  have := r26t8a_nest_product_bound p q a (fun Yw => bump Yw.2 * N Yw) X z ha hG
  refine this.trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [e2 (q - i)]

end HRS.MS.R26T8A
