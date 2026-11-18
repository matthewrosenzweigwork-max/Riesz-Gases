import HRS.MS.SA16Y4Tc3
import HRS.MS.SA16Y4Nl2

/-!
# S.A.16 (SA16Y4) Mu1: the interpolated mollified density converges pointwise to the density

`sa16y4_aInt_tendsto`: with `a_N(σ) = ∑_{i ≤ N} hat_i(σ) ρ_N ⋆ μ_{t - i t/N}` and `μ_r` regular (`IsRegularDensityW (m+3) Λ`) and pointwise
continuous in `r`, `a_N(σ)(x) → μ_{t-σ}(x)` for every `x` and `σ ∈ [0,t]` (the pointwise convergence needed by `sa16y4_nl_tendsto`).
Obtained from `sa16y4_bcInt_tendsto` applied to the vector field `b_r = μ_r e_0`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Q

section Mu1
variable {d : ℕ}

theorem sa16y4_aInt_tendsto (hd : 1 ≤ d) {m : ℕ} {Λ t : ℝ} (ht : 0 < t)
    (μ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (hμ : ∀ r ∈ Icc (0 : ℝ) t, IsRegularDensityW (m + 3) Λ (μ r))
    (hpt : ∀ x, ContinuousOn (fun r => μ r x) (Icc (0 : ℝ) t)) {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) t)
    (x : EuclideanSpace ℝ (Fin d)) :
    Tendsto (fun N : ℕ => ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ *
      sa16q_mol N (μ (t - (i : ℝ) * t / N)) x) atTop (𝓝 (μ (t - σ) x)) := by
  set i0 : Fin d := ⟨0, by omega⟩
  set b : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun r y => EuclideanSpace.single i0 (μ r y) with hb
  have hbj : ∀ r y (j : Fin d), b r y j = if j = i0 then μ r y else 0 := by
    intro r y j; simp [hb, EuclideanSpace.single_apply]
  have hL : 0 ≤ max Λ 0 := le_max_right _ _
  have hlip : ∀ r ∈ Icc (0 : ℝ) t, ∀ (j : Fin d) (y z : EuclideanSpace ℝ (Fin d)),
      |b r y j - b r z j| ≤ max Λ 0 * ‖y - z‖ := by
    intro r hr j y z
    rw [hbj, hbj]
    by_cases hj : j = i0
    · simp only [hj, if_true]
      obtain ⟨hC, hbd, -⟩ := sa16q_reg_data (hμ r hr)
      have h1 := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := μ r) (s := Set.univ)
        (fun w _ => (hC.differentiable (by exact_mod_cast (by omega : (1 : ℕ) ≠ 0))) w)
        (fun w _ => by
          have := hbd 1 (by omega) w
          rwa [norm_iteratedFDeriv_one] at this) convex_univ (Set.mem_univ z) (Set.mem_univ y)
      simpa [Real.norm_eq_abs, mul_comm] using h1
    · simp [hj]; positivity
  have hbc : ∀ r ∈ Icc (0 : ℝ) t, ∀ j, Continuous (fun y => b r y j) := by
    intro r hr j
    simp_rw [hbj]
    by_cases hj : j = i0
    · simp only [hj, if_true]
      exact (sa16q_reg_data (hμ r hr)).1.continuous
    · simp only [hj, if_false]; exact continuous_const
  have hptb : ∀ y j, ContinuousOn (fun r => b r y j) (Icc (0 : ℝ) t) := by
    intro y j
    simp_rw [hbj]
    by_cases hj : j = i0
    · simp only [hj, if_true]; exact hpt y
    · simp [hj]; exact continuousOn_const
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h := sa16y4_bcInt_tendsto t (max Λ 0) ht hL b hbc hlip hptb hσ ‖x‖ (half_pos hε)
  have hev3 : ∀ᶠ N : ℕ in atTop, ‖x‖ ≤ (N : ℝ) + 1 := by
    obtain ⟨M, hM⟩ := exists_nat_gt ‖x‖
    exact (eventually_ge_atTop M).mono fun N hN => by
      have : (M : ℝ) ≤ N := by exact_mod_cast hN
      linarith
  filter_upwards [h, hev3, eventually_ge_atTop 1] with N hN hx hN1
  have h1 := hN i0 x le_rfl
  have hχ : sa16j_chi d ((N : ℝ) + 1) x = 1 := sa16j_chi_one d (by positivity) hx
  have heq : sa16y4_bcInt d N t b σ i0 x = ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ *
      sa16q_mol N (μ (t - (i : ℝ) * t / N)) x := by
    unfold sa16y4_bcInt sa16y4_tm
    simp only [hχ, one_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [sa16q_mol, sa16j_conv, ← integral_sub_left_eq_self (fun y => b (t - (i : ℝ) * t / N) y i0 *
      sa16y_rho d N (x - y)) volume x]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [sub_sub_cancel, hbj, if_true]
    ring
  rw [heq, hbj] at h1
  simp only [if_true] at h1
  rw [Real.dist_eq]
  exact lt_of_le_of_lt h1 (by linarith)

end Mu1

end HRS.Whole.AppendixA.Phase2SA16R
