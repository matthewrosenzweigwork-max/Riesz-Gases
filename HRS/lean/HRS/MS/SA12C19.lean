import HRS.MS.SA12C18

/-!
# S.A.12(c), packet E7.04 (part 3): the smooth compactly supported kernels `Ã`, `B̃`

`ζ(z) = χ(z/2)`, `Θ_L(z) = c + L^{-s} q(z/L)`,
`Ã = ζ Θ_L + (1-ζ) Ξ_L γ_L`, `B̃ = (1-ζ) Ξ_L g`.
Both are `C^∞` with compact support (`γ_L` is smooth off the lattice, `Ξ_L` vanishes near nonzero lattice points,
`1-ζ` vanishes near `0`, `g` is smooth off `0`).
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12C

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

def sa12cZeta (χ : Euc d → ℝ) (z : Euc d) : ℝ := χ ((1 / 2 : ℝ) • z)

def sa12cTh (s L c0 : ℝ) (q : Euc d → ℝ) (z : Euc d) : ℝ := c0 + L ^ (-s) * q (L⁻¹ • z)

def sa12cA (s L c0 : ℝ) (q χ γ : Euc d → ℝ) (z : Euc d) : ℝ :=
  sa12cZeta χ z * sa12cTh s L c0 q z + (1 - sa12cZeta χ z) * (sa12cXi d L z * γ z)

def sa12cB (s L : ℝ) (χ : Euc d → ℝ) (z : Euc d) : ℝ :=
  (1 - sa12cZeta χ z) * (sa12cXi d L z * rieszKernel d s z)

theorem sa12cZeta_contDiff {χ χh : Euc d → ℝ} (hχ : IsCutoffPair χ χh) : ContDiff ℝ ∞ (sa12cZeta χ) :=
  hχ.1.1.comp (contDiff_const_smul _)

theorem sa12cZeta_one {χ χh : Euc d → ℝ} (hχ : IsCutoffPair χ χh) {z : Euc d} (hz : ‖z‖ ≤ 2) :
    sa12cZeta χ z = 1 := by
  apply hχ.1.2.2.2.2
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  linarith

theorem sa12cZeta_lt {χ χh : Euc d → ℝ} (hχ : IsCutoffPair χ χh) {z : Euc d} (hz : sa12cZeta χ z ≠ 0) :
    ‖z‖ < 4 := by
  have h1 : (1 / 2 : ℝ) • z ∈ tsupport χ := subset_tsupport χ hz
  have h2 := hχ.1.2.2.1 h1
  rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)] at h2
  linarith

theorem sa12cZeta_zero {χ χh : Euc d → ℝ} (hχ : IsCutoffPair χ χh) {z : Euc d} (hz : 4 < ‖z‖) :
    sa12cZeta χ z = 0 := by
  by_contra h
  have := sa12cZeta_lt hχ h
  linarith

theorem sa12cXi_far {L : ℝ} (hL : 0 < L) : ∃ R : ℝ, ∀ z : Euc d, R < ‖z‖ → sa12cXi d L z = 0 := by
  obtain ⟨R, hR⟩ := (sa12cXi_compact (d := d) L hL).isCompact.isBounded.exists_norm_le
  refine ⟨R, fun z hz => ?_⟩
  by_contra hne
  have : z ∈ tsupport (sa12cXi d L) := subset_tsupport _ hne
  have := hR z this
  linarith

theorem sa12cA_contDiff {s L c0 : ℝ} (hL : 0 < L) {q χ χh γ : Euc d → ℝ} (hq : ContDiff ℝ ∞ q)
    (hχ : IsCutoffPair χ χh) (hγ : IsPeriodicRieszKernel d s L γ) :
    ContDiff ℝ ∞ (sa12cA s L c0 q χ γ) := by
  have hz := sa12cZeta_contDiff hχ
  have hΞ := sa12cXi_contDiff (d := d) L
  have hΘ : ContDiff ℝ ∞ (sa12cTh s L c0 q) :=
    contDiff_const.add (contDiff_const.mul (hq.comp (contDiff_const_smul _)))
  have h1 : ContDiff ℝ ∞ (fun z => sa12cZeta χ z * sa12cTh s L c0 q z) := hz.mul hΘ
  have h2 : ContDiff ℝ ∞ (fun z => (1 - sa12cZeta χ z) * (sa12cXi d L z * γ z)) := by
    rw [contDiff_iff_contDiffAt]
    intro z0
    by_cases h2 : ‖z0‖ < 2
    · have hev : (fun z => (1 - sa12cZeta χ z) * (sa12cXi d L z * γ z)) =ᶠ[𝓝 z0] fun _ => (0 : ℝ) := by
        filter_upwards [Metric.ball_mem_nhds z0 (by linarith : (0 : ℝ) < 2 - ‖z0‖)] with z hzb
        have : ‖z‖ ≤ 2 := by
          rw [Metric.mem_ball, dist_eq_norm] at hzb
          have := norm_sub_norm_le z z0
          linarith
        rw [sa12cZeta_one hχ this]; simp
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · push Not at h2
      by_cases hlat : ∃ k : Fin d → ℤ, k ≠ 0 ∧ z0 = L • latticePt k
      · obtain ⟨k, hk, hz0⟩ := hlat
        have hev : (fun z => (1 - sa12cZeta χ z) * (sa12cXi d L z * γ z)) =ᶠ[𝓝 z0] fun _ => (0 : ℝ) := by
          rw [hz0]
          filter_upwards [sa12cXi_zero_near_lattice hL hk] with z hzΞ
          rw [hzΞ]; simp
        exact contDiffAt_const.congr_of_eventuallyEq hev
      · push Not at hlat
        have hoff : ∀ k : Fin d → ℤ, z0 ≠ L • latticePt k := by
          intro k
          by_cases hk : k = 0
          · subst hk
            intro h
            simp [latticePt] at h
            rw [h] at h2
            have hz : (WithLp.toLp 2 (fun _ : Fin d => (0 : ℝ)) : Euc d) = 0 := by
              ext i; simp
            simp [hz] at h2; linarith
          · exact fun h => hlat k hk h
        have hγat : ContDiffAt ℝ ∞ γ z0 :=
          hγ.smooth.contDiffAt ((HRS.MS.Ker1.ker1_isOpen_offLattice hL).mem_nhds hoff)
        exact (contDiffAt_const.sub hz.contDiffAt).mul (hΞ.contDiffAt.mul hγat)
  exact h1.add h2

theorem sa12cB_contDiff {s L : ℝ} (hL : 0 < L) {χ χh : Euc d → ℝ} (hχ : IsCutoffPair χ χh) :
    ContDiff ℝ ∞ (sa12cB s L χ) := by
  have hz := sa12cZeta_contDiff hχ
  have hΞ := sa12cXi_contDiff (d := d) L
  unfold sa12cB
  rw [contDiff_iff_contDiffAt]
  intro z0
  by_cases h2 : ‖z0‖ < 2
  · have hev : (fun z => (1 - sa12cZeta χ z) * (sa12cXi d L z * rieszKernel d s z)) =ᶠ[𝓝 z0]
        fun _ => (0 : ℝ) := by
      filter_upwards [Metric.ball_mem_nhds z0 (by linarith : (0 : ℝ) < 2 - ‖z0‖)] with z hzb
      have : ‖z‖ ≤ 2 := by
        rw [Metric.mem_ball, dist_eq_norm] at hzb
        have := norm_sub_norm_le z z0
        linarith
      rw [sa12cZeta_one hχ this]; simp
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · push Not at h2
    have hz0 : z0 ≠ 0 := by
      intro h; rw [h] at h2; norm_num at h2
    have hg : ContDiffAt ℝ ∞ (rieszKernel d s) z0 :=
      (rieszKernel_contDiffOn (d := d) (s := s)).contDiffAt (isOpen_compl_singleton.mem_nhds hz0)
    exact (contDiffAt_const.sub hz.contDiffAt).mul (hΞ.contDiffAt.mul hg)

theorem sa12cA_compact {s L c0 : ℝ} (hL : 0 < L) {q χ χh γ : Euc d → ℝ} (hχ : IsCutoffPair χ χh) :
    HasCompactSupport (sa12cA s L c0 q χ γ) := by
  obtain ⟨R, hR⟩ := sa12cXi_far (d := d) hL
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) (max R 4)) fun z hz => ?_
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hz
  have h4 : 4 < ‖z‖ := lt_of_le_of_lt (le_max_right _ _) hz
  have hR' : R < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hz
  unfold sa12cA
  rw [sa12cZeta_zero hχ h4, hR z hR']; simp

theorem sa12cB_compact {s L : ℝ} (hL : 0 < L) {χ χh : Euc d → ℝ} (hχ : IsCutoffPair χ χh) :
    HasCompactSupport (sa12cB s L χ) := by
  obtain ⟨R, hR⟩ := sa12cXi_far (d := d) hL
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) R) fun z hz => ?_
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hz
  unfold sa12cB
  rw [hR z hz]; simp

end HRS.MH.AdjointRd.Phase2SA12C
