import HRS.MS.Fp81S21WickG8

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace HRS.Fp81.S21

/-- The covariance form of an arbitrary finite family under a bounded
`L²` operator is dominated by the Gram form of the input family. -/
theorem fp81s21_wickG_operator_covariance_form_bound
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P) (Kstar : ℝ)
    (hL : ‖L‖ ≤ Kstar) (n : ℕ)
    (f : Fin n → Lp ℝ 2 μ) (α : Fin n → ℝ) :
    HRS.MS.R2Chaos.s94q P (fun i ω => (L (f i)) ω) α ≤
      Kstar ^ 2 * ‖∑ i, α i • f i‖ ^ 2 := by
  classical
  let g : Fin n → Ω → ℝ := fun i ω => (L (f i)) ω
  let v : Lp ℝ 2 μ := ∑ i, α i • f i
  have hLv : L v = ∑ i, α i • L (f i) := by
    simp [v, map_sum, map_smul]
  have hsum : (∑ i : Fin n, α i • L (f i) : Lp ℝ 2 P) =ᵐ[P]
      fun ω => ∑ i, α i * (L (f i)) ω := by
    have h1 : (∑ i : Fin n, α i • L (f i) : Lp ℝ 2 P) =ᵐ[P]
        fun ω => ∑ i, (α i • L (f i) : Lp ℝ 2 P) ω := by
      simpa using HRS.A33.a33_coeFn_sum (P := P) Finset.univ
        (fun i => α i • L (f i))
    have h2 : ∀ᵐ ω ∂P, ∀ i : Fin n,
        (α i • L (f i) : Lp ℝ 2 P) ω = α i * (L (f i)) ω := by
      rw [ae_all_iff]
      intro i
      filter_upwards [Lp.coeFn_smul (α i) (L (f i))] with ω hω
      simpa [smul_eq_mul] using hω
    filter_upwards [h1, h2] with ω hω hωi
    rw [hω]
    exact Finset.sum_congr rfl fun i _ => hωi i
  have hLvAE : (L v) =ᵐ[P]
      (∑ i : Fin n, α i • L (f i) : Lp ℝ 2 P) := by
    filter_upwards [ae_of_all P fun ω =>
      congrFun (congrArg (fun q : Lp ℝ 2 P => (q : Ω → ℝ)) hLv) ω] with ω hω
    exact hω
  have hrepr : HRS.MS.R2Chaos.s94lin g α =ᵐ[P] fun ω => (L v) ω := by
    filter_upwards [hLvAE, hsum] with ω hωv hωs
    simpa [HRS.MS.R2Chaos.s94lin, g] using (hωv.trans hωs).symm
  have hq : HRS.MS.R2Chaos.s94q P g α = ‖L v‖ ^ 2 := by
    unfold HRS.MS.R2Chaos.s94q
    calc
      ∫ ω, HRS.MS.R2Chaos.s94lin g α ω ^ 2 ∂P =
          ∫ ω, (L v) ω ^ 2 ∂P := by
            refine integral_congr_ae ?_
            filter_upwards [hrepr] with ω hω
            rw [hω]
      _ = inner ℝ (L v) (L v) := by
            rw [L2.inner_def]
            exact integral_congr_ae (ae_of_all P fun ω => by simp)
      _ = ‖L v‖ ^ 2 := real_inner_self_eq_norm_sq _
  have hLvBound : ‖L v‖ ≤ Kstar * ‖v‖ := by
    calc
      ‖L v‖ ≤ ‖L‖ * ‖v‖ := L.le_opNorm v
      _ ≤ Kstar * ‖v‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg _)
  have hK : 0 ≤ Kstar := le_trans (norm_nonneg L) hL
  have hsq : ‖L v‖ ^ 2 ≤ (Kstar * ‖v‖) ^ 2 := by
    have hA : 0 ≤ ‖L v‖ := norm_nonneg _
    have hB : 0 ≤ Kstar * ‖v‖ := mul_nonneg hK (norm_nonneg _)
    nlinarith
  calc
    HRS.MS.R2Chaos.s94q P g α = ‖L v‖ ^ 2 := hq
    _ ≤ (Kstar * ‖v‖) ^ 2 := hsq
    _ = Kstar ^ 2 * ‖v‖ ^ 2 := by ring

#print axioms fp81s21_wickG_operator_covariance_form_bound

end HRS.Fp81.S21

end
