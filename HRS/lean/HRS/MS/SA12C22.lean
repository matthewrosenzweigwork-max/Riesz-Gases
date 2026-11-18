import HRS.MS.SA12C21

/-!
# S.A.12(c), packet E7.04 (part 6): jets of the smooth kernels equal the remainder kernel

For `z ≠ 0`, `|z| ≠ 4`, `|z_i| < 3L/5`, `|v| < 2`:
`D^β Ã(z) - χ̂(v-z) D^β B̃(z) = D^βγ_L(z) - χ̂(v-z) D^β g(z) = sa12cRho`.
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12C

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MH.AdjointRd.Phase2SA12Construction HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRd.Phase2SA12Near

variable {d : ℕ}

theorem sa12c_pd_congr {f g : Euc d → ℝ} {z : Euc d} (h : f =ᶠ[𝓝 z] g) {n : ℕ} (β : Fin n → Fin d) :
    partialDeriv β f z = partialDeriv β g z := by
  unfold partialDeriv
  rw [(h.iteratedFDeriv ℝ n).eq_of_nhds]

theorem sa12c_pd_add' {f g : Euc d → ℝ} {z : Euc d} (hf : ContDiffAt ℝ ∞ f z) (hg : ContDiffAt ℝ ∞ g z)
    {n : ℕ} (β : Fin n → Fin d) :
    partialDeriv β (fun u => f u + g u) z = partialDeriv β f z + partialDeriv β g z := by
  unfold partialDeriv
  have := iteratedFDeriv_add_apply (𝕜 := ℝ) (i := n) (hf.of_le (by exact_mod_cast le_top))
    (hg.of_le (by exact_mod_cast le_top))
  have e : (fun u => f u + g u) = f + g := rfl
  rw [e, this]
  rfl

theorem sa12c_open_small {r : ℝ} : IsOpen {u : Euc d | ∀ i, |u i| < r} := by
  have : {u : Euc d | ∀ i, |u i| < r} = ⋂ i : Fin d, (fun u : Euc d => |u i|) ⁻¹' Iio r := by
    ext u; simp
  rw [this]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_Iio.preimage (continuous_abs.comp (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous)

theorem sa12c_deriv_kernel {s L c0 : ℝ} (hL : 40 ≤ L) {q χ χh γ : Euc d → ℝ} (hχ : IsCutoffPair χ χh)
    (hq : ContDiff ℝ ∞ q)
    (hΘ : ∀ z : Euc d, z ≠ 0 → ‖z‖ < 4 → γ z = rieszKernel d s z + sa12cTh s L c0 q z)
    {n : ℕ} (β : Fin n → Fin d) (v z : Euc d) (hv : ‖v‖ < 2) (hz0 : z ≠ 0) (hz4 : ‖z‖ ≠ 4)
    (hzc : ∀ i, |z i| < 3 * L / 5) :
    partialDeriv β (sa12cA s L c0 q χ γ) z - χh (v - z) * partialDeriv β (sa12cB s L χ) z =
      sa12cRho s χh γ β v z := by
  have hL0 : 0 < L := by linarith
  have hΞnear : ∀ᶠ u in 𝓝 z, sa12cXi d L u = 1 := by
    filter_upwards [((sa12c_open_small (r := 3 * L / 5)).mem_nhds hzc)] with u hu
    exact sa12cXi_one hL0 fun i => (hu i).le
  unfold sa12cRho
  rcases lt_or_gt_of_ne hz4 with h4 | h4
  · -- near region
    have hnear : ∀ᶠ u in 𝓝 z, u ≠ 0 ∧ ‖u‖ < 4 := by
      have hball : z ∈ Metric.ball (0 : Euc d) 4 := by
        simpa only [Metric.mem_ball, dist_zero_right] using h4
      filter_upwards [isOpen_compl_singleton.mem_nhds hz0,
        Metric.isOpen_ball.mem_nhds hball] with u hu1 hu2
      exact ⟨hu1, by simpa using hu2⟩
    have hΘs : ContDiff ℝ ∞ (sa12cTh s L c0 q) :=
      contDiff_const.add (contDiff_const.mul (hq.comp (contDiff_const_smul _)))
    have hgat : ContDiffAt ℝ ∞ (rieszKernel d s) z :=
      (rieszKernel_contDiffOn (d := d) (s := s)).contDiffAt (isOpen_compl_singleton.mem_nhds hz0)
    have hζ := (sa12cZeta_contDiff hχ).contDiffAt (x := z)
    have hH : ContDiffAt ℝ ∞ (fun u => (1 - sa12cZeta χ u) * rieszKernel d s u) z :=
      (contDiffAt_const.sub hζ).mul hgat
    have hγev : γ =ᶠ[𝓝 z] fun u => rieszKernel d s u + sa12cTh s L c0 q u :=
      hnear.mono fun u hu => hΘ u hu.1 hu.2
    have hAev : sa12cA s L c0 q χ γ =ᶠ[𝓝 z]
        fun u => sa12cTh s L c0 q u + (1 - sa12cZeta χ u) * rieszKernel d s u := by
      filter_upwards [hΞnear, hnear] with u hΞ hu
      simp only [sa12cA, hΞ, one_mul, hΘ u hu.1 hu.2]
      ring
    have hBev : sa12cB s L χ =ᶠ[𝓝 z] fun u => (1 - sa12cZeta χ u) * rieszKernel d s u := by
      filter_upwards [hΞnear] with u hΞ
      simp [sa12cB, hΞ]
    have hχ1 : χh (v - z) = 1 := by
      apply hχ.2.2.2.2.2
      rw [Metric.mem_closedBall, dist_zero_right]
      calc ‖v - z‖ ≤ ‖v‖ + ‖z‖ := norm_sub_le _ _
        _ ≤ 6 := by linarith
    rw [sa12c_pd_congr hAev β, sa12c_pd_congr hBev β, sa12c_pd_congr hγev β, hχ1,
      sa12c_pd_add' hΘs.contDiffAt hH β, sa12c_pd_add' hgat hΘs.contDiffAt β]
    ring
  · have hfar : ∀ᶠ u in 𝓝 z, 4 < ‖u‖ :=
      (isOpen_lt continuous_const continuous_norm).mem_nhds h4
    have hAev : sa12cA s L c0 q χ γ =ᶠ[𝓝 z] γ := by
      filter_upwards [hΞnear, hfar] with u hΞ hu
      simp [sa12cA, sa12cZeta_zero hχ hu, hΞ]
    have hBev : sa12cB s L χ =ᶠ[𝓝 z] rieszKernel d s := by
      filter_upwards [hΞnear, hfar] with u hΞ hu
      simp [sa12cB, sa12cZeta_zero hχ hu, hΞ]
    rw [sa12c_pd_congr hAev β, sa12c_pd_congr hBev β]

end HRS.MH.AdjointRd.Phase2SA12C
