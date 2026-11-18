import HRS.MS.Fp81S21BV07

/-! A variation-Cauchy sequence has a continuous anchored uniform limit. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Set Filter
open scoped Topology
namespace HRS.Fp81.S21
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : ℝ} (hH : 0 ≤ H)

theorem fp81s21_bvCauchy_path_limit (u : ℕ → fp81s21_BV0 (E := E) hH)
    (hu : CauchySeq u) :
    ∃ f : C(Icc (0 : ℝ) H, E),
      Tendsto (fun n => (u n).path) atTop (𝓝 f) ∧ f ⟨0, ⟨le_rfl, hH⟩⟩ = 0 := by
  have hc : CauchySeq (fun n => (u n).path) := by
    change CauchySeq ((fp81s21_bvPath hH) ∘ u)
    exact (fp81s21_bvPath hH).lipschitzWith.cauchySeq_comp hu
  obtain ⟨f, hf⟩ := cauchy_iff_exists_le_nhds.mp hc
  refine ⟨f, hf, ?_⟩
  have h0 : Tendsto (fun n => (u n).path ⟨0, ⟨le_rfl, hH⟩⟩) atTop
      (𝓝 (f ⟨0, ⟨le_rfl, hH⟩⟩)) := ((continuous_eval_const _).tendsto _).comp hf
  have hz : Tendsto (fun n : ℕ => (u n).path ⟨0, ⟨le_rfl, hH⟩⟩) atTop (𝓝 (0 : E)) := by
    simpa only [(u _).zero_at_left] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : E)) atTop (𝓝 0))
  exact tendsto_nhds_unique h0 hz

#print axioms fp81s21_bvCauchy_path_limit
end HRS.Fp81.S21
end
