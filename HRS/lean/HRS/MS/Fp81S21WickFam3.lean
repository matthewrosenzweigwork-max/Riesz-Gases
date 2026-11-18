import HRS.MS.Fp81S21WickFam2

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Filter Topology Set

namespace HRS.Fp81.S21

/-- Uniform operator bounds propagate time continuity from a dense collection
of inputs to the entire domain. -/
theorem fp81s21_wickFam_continuous_of_dense
    {A E F : Type*} [TopologicalSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S : Set A) (T : A → E →L[ℝ] F) (C : ℝ)
    (hbound : ∀ a ∈ S, ‖T a‖ ≤ C)
    (D : Set E) (hdense : Dense D)
    (hcont : ∀ x ∈ D, ContinuousOn (fun a => T a x) S) :
    ∀ x, ContinuousOn (fun a => T a x) S := by
  intro x
  obtain ⟨v, hvD, hvlim⟩ := mem_closure_iff_seq_limit.1 (hdense x)
  have hlim : Tendsto (fun n => C * ‖x - v n‖) atTop (𝓝 0) := by
    have hx : Tendsto (fun _ : ℕ => x) atTop (𝓝 x) := tendsto_const_nhds
    have hc : Tendsto (fun _ : ℕ => C) atTop (𝓝 C) := tendsto_const_nhds
    have h := hc.mul (hx.sub hvlim).norm
    simpa using h
  have hu : TendstoUniformlyOn (fun n a => T a (v n)) (fun a => T a x) atTop S := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [hlim.eventually (Iio_mem_nhds hε)] with n hn a ha
    calc
      dist (T a x) (T a (v n)) = ‖T a (x - v n)‖ := by
        rw [dist_eq_norm, map_sub]
      _ ≤ ‖T a‖ * ‖x - v n‖ := (T a).le_opNorm _
      _ ≤ C * ‖x - v n‖ := mul_le_mul_of_nonneg_right (hbound a ha) (norm_nonneg _)
      _ < ε := hn
  exact hu.continuousOn (Filter.Eventually.frequently (Filter.Eventually.of_forall
    fun n => hcont (v n) (hvD n)))

#print axioms fp81s21_wickFam_continuous_of_dense

end HRS.Fp81.S21
end
