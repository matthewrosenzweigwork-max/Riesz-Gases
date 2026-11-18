import HRS.MS.Fp81S21GaussMomRep
import HRS.MS.ProClosureS111JointLp

/-! Trace-class coefficient fields for continuous families of L² operators. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HRS.Fp81.S21
open HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- A uniformly bounded, strongly time-continuous family of L² operators
maps a square-summable family of source vectors to a jointly measurable
coefficient field. At each nonnegative time all coordinates agree with
their L² classes on a single full event. -/
theorem fp81s21_operator_coeff_field
    {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (μ : Measure X) (P : Measure Ω) [IsFiniteMeasure P]
    (T : ℝ → Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P) (K : ℝ) (hK : 0 ≤ K)
    (hT : ∀ u, 0 ≤ u → ‖T u‖ ≤ K)
    (hc : ∀ v, ContinuousOn (fun u => T u v) (Set.Ici 0))
    (v : ℕ → Lp ℝ 2 μ) (hv : Summable (fun j => ‖v j‖ ^ 2)) :
    ∃ q : ℝ → Ω → r26t6_Coeff,
      Measurable (Function.uncurry q) ∧
      ∀ u, 0 ≤ u → MemLp (q u) 2 P ∧
        (∫ ω, ‖q u ω‖ ^ 2 ∂P) ≤ K ^ 2 * ∑' j, ‖v j‖ ^ 2 ∧
        ∀ᵐ ω ∂P, ∀ j, q u ω j = (T u (v j) : Ω → ℝ) ω := by
  have hex : ∀ j, ∃ F : ℝ × Ω → ℝ, Measurable F ∧
      ∀ u, 0 ≤ u → MemLp (fun ω => F (u, ω)) 2 P ∧
        (fun ω => F (u, ω)) =ᵐ[P] (T u (v j) : Ω → ℝ) := by
    intro j
    have hc' : Continuous (fun u : ℝ => T (max u 0) (v j)) :=
      (hc (v j)).comp_continuous (continuous_id.max continuous_const)
        (fun u => Set.mem_Ici.mpr (le_max_right u 0))
    obtain ⟨F, hFm, hFs⟩ := joint_Lp_representative P 2 (by norm_num)
      (fun u : ℝ => T (max u 0) (v j)) hc'.stronglyMeasurable
    refine ⟨F, hFm.measurable, ?_⟩
    intro u hu
    simpa [max_eq_left hu] using hFs u
  choose F hFm hFs using hex
  let b : ℕ → ℝ := fun j => K ^ 2 * ‖v j‖ ^ 2
  have hb : Summable b := hv.mul_left (K ^ 2)
  have hsec : ∀ u, 0 ≤ u → ∀ j,
      MemLp (fun ω => F j (u, ω)) 2 P ∧
        (∫ ω, F j (u, ω) ^ 2 ∂P) ≤ b j := by
    intro u hu j
    refine ⟨(hFs j u hu).1, ?_⟩
    have he : (∫ ω, F j (u, ω) ^ 2 ∂P) = ‖T u (v j)‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
      refine integral_congr_ae ((hFs j u hu).2.mono fun ω hω => ?_)
      simp [hω, sq]
    have hn : ‖T u (v j)‖ ≤ K * ‖v j‖ :=
      ((T u).le_opNorm (v j)).trans
        (mul_le_mul_of_nonneg_right (hT u hu) (norm_nonneg _))
    calc
      _ = ‖T u (v j)‖ ^ 2 := he
      _ ≤ (K * ‖v j‖) ^ 2 := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))).2 hn
      _ = b j := by simp [b, mul_pow]
  obtain ⟨q, hq, hqsec⟩ := fp81s21_coeff_field_every_time P F hFm b hb hsec
  refine ⟨q, hq, ?_⟩
  intro u hu
  obtain ⟨hmem, hbound, hagree⟩ := hqsec u hu
  refine ⟨hmem, ?_, ?_⟩
  · simpa [b, tsum_mul_left] using hbound
  · filter_upwards [hagree, ae_all_iff.mpr (fun j => (hFs j u hu).2)] with ω hqω hFω j
    exact (hqω j).trans (hFω j)

#print axioms fp81s21_operator_coeff_field
end HRS.Fp81.S21
end
