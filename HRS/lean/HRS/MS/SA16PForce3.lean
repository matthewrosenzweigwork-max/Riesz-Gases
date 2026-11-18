import HRS.MS.SA16PForce2

/-!
# SA16P P4, part 3: `Φ_K ρ` is `C^k` with `‖D^j Φ_K ρ‖ ≤ C₀ A` for `ρ ∈ C^{k+1}` with weighted bounds

`sa16p_phi_contDiff`: if `ρ ∈ C^{k+1}` and `‖D^j ρ y‖ ≤ A (1+|y|)^{-(d+3)}` for `j ≤ k+1`, then `Φ_K ρ ∈ C^k` and
`‖D^j Φ_K ρ x‖ ≤ C₀ A` for `j ≤ k`, with `C₀ = sa16p_C0 d c s` independent of `k`, `ρ`, `F`.
The base case is the continuity of `Φ_K ρ` for `ρ ∈ C^1` (dominated convergence); the step uses part 2 and
`D Φ_K ρ = Φ_K (Dρ)`.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace HRS.Whole.AppendixA.Phase2SA16P

section Cont
variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma sa16p_norm_fderiv_eq {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (f : 𝔼 → G) (y : 𝔼) :
    ‖fderiv ℝ f y‖ = ‖iteratedFDeriv ℝ 1 f y‖ := by
  have := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (n := 0) (f := f) (x := y)
  rw [norm_iteratedFDeriv_zero] at this
  exact this

lemma sa16p_continuous_phi {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (hd : 1 ≤ d) {K : 𝔼 → ℝ} (hKm : Measurable K) {c s A : ℝ} (hc : 0 ≤ c)
    (hs0 : 0 ≤ s) (hsd : s < d) (hK : ∀ z, z ≠ 0 → |K z| ≤ c * ‖z‖ ^ (-s - 1)) {ρ : 𝔼 → F}
    (hρ : ContDiff ℝ 1 ρ) (hρw : ∀ y, ‖ρ y‖ ≤ A * sa16p_w d y) (hρ1 : ∀ y, ‖fderiv ℝ ρ y‖ ≤ A) :
    Continuous (sa16p_phiF K ρ) := by
  have hρd : Differentiable ℝ ρ := hρ.differentiable (by norm_num)
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  have hB1 : Integrable ((closedBall (0 : 𝔼) (1 / 4)).indicator (fun z => c * A * ‖z‖ ^ (-s))) volume :=
    (integrable_indicator_iff measurableSet_closedBall).2 ((sa16p_I1_integrable hd hsd).const_mul (c * A))
  have hB2 : Integrable (fun z : 𝔼 => c * 4 ^ (s + 1) * A * 2 ^ ((d : ℝ) + 3) * sa16p_w d (x₀ - z)) volume :=
    (sa16p_w_integrable.comp_sub_left x₀).const_mul _
  have hA : 0 ≤ A := (norm_nonneg _).trans (hρ1 0)
  refine continuousAt_of_dominated (bound := fun z => (closedBall (0 : 𝔼) (1 / 4)).indicator
      (fun z => c * A * ‖z‖ ^ (-s)) z + c * 4 ^ (s + 1) * A * 2 ^ ((d : ℝ) + 3) * sa16p_w d (x₀ - z))
    (Eventually.of_forall fun x => sa16p_phiI_aesm hKm hρ.continuous x) ?_ (hB1.add hB2)
    (Eventually.of_forall fun z => ?_)
  · filter_upwards [Metric.ball_mem_nhds x₀ one_pos] with x hx
    refine Eventually.of_forall fun z => ?_
    refine (sa16p_phiI_bound hc hs0 hK hρd hρw hρ1 x z).trans ?_
    have h2 : sa16p_w d (x - z) ≤ 2 ^ ((d : ℝ) + 3) * sa16p_w d (x₀ - z) :=
      sa16p_w_shift x₀ x z (by simpa [dist_eq_norm] using (mem_ball.1 hx).le)
    have : c * 4 ^ (s + 1) * A * sa16p_w d (x - z) ≤
        c * 4 ^ (s + 1) * A * (2 ^ ((d : ℝ) + 3) * sa16p_w d (x₀ - z)) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  · by_cases hn : ‖z‖ ≤ 1 / 4
    · have e : ∀ y, sa16p_phiI K ρ y z = K z • (ρ (y - z) - ρ y) := fun y => by
        unfold sa16p_phiI; rw [if_pos hn]
      simp_rw [e]
      exact (continuousAt_const.smul (((hρ.continuous.comp (continuous_id.sub continuous_const)).sub
        hρ.continuous).continuousAt))
    · have e : ∀ y, sa16p_phiI K ρ y z = K z • (ρ (y - z)) := fun y => by
        unfold sa16p_phiI; rw [if_neg hn, sub_zero]
      simp_rw [e]
      exact (continuousAt_const.smul ((hρ.continuous.comp (continuous_id.sub continuous_const)).continuousAt))

end Cont

end HRS.Whole.AppendixA.Phase2SA16P
