import HRS.MS.SA16PForce1

/-!
# SA16P P4, part 2: `Φ_K ρ` is differentiable and `D Φ_K ρ = Φ_K (Dρ)`

For `ρ ∈ C²` with `‖ρ y‖, ‖Dρ y‖ ≤ A (1+|y|)^{-(d+3)}` and `‖D²ρ‖ ≤ A`: `HasFDerivAt (Φ_K ρ) (Φ_K (Dρ) x) x`
(differentiation under the integral sign, domination by the bound of part 1 applied to `Dρ`).
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace HRS.Whole.AppendixA.Phase2SA16P

section Deriv
variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

set_option synthInstance.maxHeartbeats 400000 in
lemma sa16p_phi_hasFDerivAt (hd : 1 ≤ d) {K : 𝔼 → ℝ} (hKm : Measurable K) {c s A : ℝ} (hc : 0 ≤ c)
    (hs0 : 0 ≤ s) (hsd : s < d) (hK : ∀ z, z ≠ 0 → |K z| ≤ c * ‖z‖ ^ (-s - 1)) {ρ : 𝔼 → F}
    (hρ : ContDiff ℝ 2 ρ) (hρw : ∀ y, ‖ρ y‖ ≤ A * sa16p_w d y)
    (hρ1 : ∀ y, ‖fderiv ℝ ρ y‖ ≤ A * sa16p_w d y) (hρ2 : ∀ y, ‖fderiv ℝ (fderiv ℝ ρ) y‖ ≤ A)
    (x₀ : 𝔼) :
    HasFDerivAt (sa16p_phiF K ρ) (sa16p_phiF K (fderiv ℝ ρ) x₀) x₀ := by
  have hρd : Differentiable ℝ ρ := hρ.differentiable (by norm_num)
  have hρ' : ContDiff ℝ 1 (fderiv ℝ ρ) := hρ.fderiv_right (m := 1) (by norm_num)
  have hρ'd : Differentiable ℝ (fderiv ℝ ρ) := hρ'.differentiable (by norm_num)
  have hA : 0 ≤ A := le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ ρ) 0)) (hρ2 0)
  have hρ1' : ∀ y, ‖fderiv ℝ ρ y‖ ≤ A := fun y => (hρ1 y).trans
    (mul_le_of_le_one_right hA (sa16p_w_le_one y))
  -- bound function
  set bound : 𝔼 → ℝ := fun z => (closedBall (0 : 𝔼) (1 / 4)).indicator (fun z => c * A * ‖z‖ ^ (-s)) z +
    c * 4 ^ (s + 1) * A * 2 ^ ((d : ℝ) + 3) * sa16p_w d (x₀ - z) with hbound
  have hB1 : Integrable ((closedBall (0 : 𝔼) (1 / 4)).indicator (fun z => c * A * ‖z‖ ^ (-s))) volume :=
    (integrable_indicator_iff measurableSet_closedBall).2 ((sa16p_I1_integrable hd hsd).const_mul (c * A))
  have hB2 : Integrable (fun z : 𝔼 => c * 4 ^ (s + 1) * A * 2 ^ ((d : ℝ) + 3) * sa16p_w d (x₀ - z)) volume :=
    (sa16p_w_integrable.comp_sub_left x₀).const_mul _
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume)
    (F := fun x z => sa16p_phiI K ρ x z) (F' := fun x z => sa16p_phiI K (fderiv ℝ ρ) x z)
    (x₀ := x₀) (bound := bound) (s := ball x₀ 1) (ball_mem_nhds x₀ one_pos)
    (Eventually.of_forall fun x => sa16p_phiI_aesm hKm hρ.continuous x)
    (sa16p_phi_bound hd hKm hc hs0 hsd hK hρd hρw hρ1' x₀).1
    (sa16p_phiI_aesm hKm hρ'.continuous x₀)
    (Eventually.of_forall fun z x hx => ?_) (hB1.add hB2)
    (Eventually.of_forall fun z x hx => ?_)
  · exact key
  · -- the bound on the derivative integrand
    have h1 := sa16p_phiI_bound hc hs0 hK hρ'd hρ1 hρ2 x z
    have h2 : sa16p_w d (x - z) ≤ 2 ^ ((d : ℝ) + 3) * sa16p_w d (x₀ - z) :=
      sa16p_w_shift x₀ x z (by simpa [dist_eq_norm] using (mem_ball.1 hx).le)
    refine h1.trans ?_
    simp only [hbound]
    have : c * 4 ^ (s + 1) * A * sa16p_w d (x - z) ≤
        c * 4 ^ (s + 1) * A * (2 ^ ((d : ℝ) + 3) * sa16p_w d (x₀ - z)) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  · -- the derivative of the integrand
    by_cases hn : ‖z‖ ≤ 1 / 4
    · have e : ∀ y, sa16p_phiI K ρ y z = K z • (ρ (y - z) - ρ y) := fun y => by
        unfold sa16p_phiI; rw [if_pos hn]
      have e' : sa16p_phiI K (fderiv ℝ ρ) x z = K z • (fderiv ℝ ρ (x - z) - fderiv ℝ ρ x) := by
        unfold sa16p_phiI; rw [if_pos hn]
      simp_rw [e]; rw [e']
      have h1 : HasFDerivAt (fun y : 𝔼 => ρ (y - z)) (fderiv ℝ ρ (x - z)) x := by
        have := (hρd (x - z)).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const z)
        exact this
      exact (h1.sub (hρd x).hasFDerivAt).const_smul (K z)
    · have e : ∀ y, sa16p_phiI K ρ y z = K z • (ρ (y - z)) := fun y => by
        unfold sa16p_phiI; rw [if_neg hn, sub_zero]
      have e' : sa16p_phiI K (fderiv ℝ ρ) x z = K z • (fderiv ℝ ρ (x - z)) := by
        unfold sa16p_phiI; rw [if_neg hn, sub_zero]
      simp_rw [e]; rw [e']
      have h1 : HasFDerivAt (fun y : 𝔼 => ρ (y - z)) (fderiv ℝ ρ (x - z)) x := by
        have := (hρd (x - z)).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const z)
        exact this
      exact h1.const_smul (K z)

end Deriv

end HRS.Whole.AppendixA.Phase2SA16P
