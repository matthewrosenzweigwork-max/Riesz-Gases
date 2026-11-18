import HRS.MS.Fp81S21WickFam8

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS (Euc)

private theorem fp81s21_wickFam_continuous_of_mem_closure
    {A E F : Type*} [TopologicalSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S : Set A) (T : A → E →L[ℝ] F) (C : ℝ)
    (hbound : ∀ a ∈ S, ‖T a‖ ≤ C)
    (D : Set E) (hcont : ∀ x ∈ D, ContinuousOn (fun a => T a x) S)
    (x : E) (hx : x ∈ closure D) :
    ContinuousOn (fun a => T a x) S := by
  obtain ⟨v, hvD, hvlim⟩ := mem_closure_iff_seq_limit.1 hx
  have hlim : Tendsto (fun n => C * ‖x - v n‖) atTop (𝓝 0) := by
    have hx' : Tendsto (fun _ : ℕ => x) atTop (𝓝 x) := tendsto_const_nhds
    have hc : Tendsto (fun _ : ℕ => C) atTop (𝓝 C) := tendsto_const_nhds
    have h := hc.mul (hx'.sub hvlim).norm
    simpa using h
  have hu : TendstoUniformlyOn (fun n a => T a (v n)) (fun a => T a x) atTop S := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [hlim.eventually (Iio_mem_nhds hε)] with n hn a ha
    calc
      dist (T a x) (T a (v n)) = ‖T a (x - v n)‖ := by rw [dist_eq_norm, map_sub]
      _ ≤ ‖T a‖ * ‖x - v n‖ := (T a).le_opNorm _
      _ ≤ C * ‖x - v n‖ := mul_le_mul_of_nonneg_right (hbound a ha) (norm_nonneg _)
      _ < ε := hn
  exact hu.continuousOn (Filter.Eventually.frequently (Filter.Eventually.of_forall
    fun n => hcont (v n) (hvD n)))

/-- For a uniformly bounded family that ignores the antisymmetric kernel part,
continuity on smooth symmetric finite-rank generators suffices for continuity
on the entire product L² space. -/
theorem fp81s21_wickFam_continuous_of_symmetric_generators
    {d : ℕ} (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : Set ℝ) (T : ℝ → Lp ℝ 2 (μ.prod μ) →L[ℝ] Lp ℝ 2 P) (C : ℝ)
    (hbound : ∀ u ∈ S, ‖T u‖ ≤ C)
    (hsymm : ∀ u ∈ S, ∀ k, T u k = T u (fp81s21_wickB23_symmetrize μ k))
    (hgen : ∀ k ∈ fp81s21_wickB32_generators μ, ContinuousOn (fun u => T u k) S) :
    ∀ k, ContinuousOn (fun u => T u k) S := by
  let D := fp81s21_wickB32_finiteRankSubmodule μ
  have hspan : ∀ k ∈ (D : Set (Lp ℝ 2 (μ.prod μ))), ContinuousOn (fun u => T u k) S := by
    intro k hk
    induction hk using Submodule.span_induction with
    | mem k hk => exact hgen k hk
    | zero => simpa using (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : Lp ℝ 2 P)) S)
    | add x y hx hy ihx ihy =>
      convert ihx.add ihy using 1
      ext u
      simp
    | smul c x hx ihx =>
      convert ihx.const_smul c using 1
      ext u
      simp
  intro k
  have hf : fp81s21_wickB23_symmetrize μ k ∈ closure (D : Set (Lp ℝ 2 (μ.prod μ))) :=
    fp81s21_wickB33_symmetric_mem_closure μ _ (fp81s21_wickB23_symmetrize_idempotent μ k)
  have hc := fp81s21_wickFam_continuous_of_mem_closure S T C hbound D hspan _ hf
  exact hc.congr (fun u hu => hsymm u hu k)

#print axioms fp81s21_wickFam_continuous_of_symmetric_generators
end HRS.Fp81.S21
end
