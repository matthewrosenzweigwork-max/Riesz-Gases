import HRS.MS.Fp81S21GaussMomRep2
import HRS.MS.Fp81S21WickFam7
import HRS.MS.Fp81S21WeightTrace2

/-! Moving Gaussian chart coordinates with an every-time trace bound. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- The moving Gaussian's strong-chart coordinates have a common bound
selected before the realization and time. Coordinate agreement is
simultaneous in the countable chart index at each nonnegative time. -/
theorem fp81s21_gaussian_strong_chart_coordinates (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∀ Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4),
      ∀ E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2),
        ∃ M : ℝ, 0 ≤ M ∧ ∀ G : GaussianRealization R,
          ∃ q : ℝ → G.Ω → r26t6_Coeff,
            Measurable (Function.uncurry q) ∧
            ∀ u, 0 ≤ u → MemLp (q u) 2 G.P ∧
              (∫ ω, ‖q u ω‖ ^ 2 ∂G.P) ≤ M ∧
              ∀ᵐ ω ∂G.P, ∀ j,
                q u ω j = OscDual.eval (G.Z u ω) (Es.test j) := by
  obtain ⟨B, B', hB, _, htrace⟩ := fp81s21_physical_reference_thermal_traces p
  obtain ⟨δ0, hδ0, hδhalf, hfamily⟩ := fp81s21_wickFam_supplied_linear_continuous p
  refine ⟨δ0, hδ0, hδhalf, ?_⟩
  intro δ hδ hδle R Es E
  obtain ⟨K, hK, hfamilyR⟩ := hfamily δ hδ hδle R
  let μ := HRS.Whole.withDensityReal R.ρβ
  have hval := (htrace δ R Es E).1.1
  let v : ℕ → Lp ℝ 2 μ := fun j => (hval.1 j).toLp (Es.test j)
  have hvnorm (j : ℕ) : ‖v j‖ ^ 2 = ∫ x, Es.test j x ^ 2 ∂μ := by
    symm
    exact HRS.Whole.Q34.integral_sq_eq (MemLp.coeFn_toLp (hval.1 j)).symm
  have hv : Summable (fun j => ‖v j‖ ^ 2) := by
    simpa only [hvnorm] using hval.2.1
  refine ⟨K ^ 2 * B, mul_nonneg (sq_nonneg K) hB, ?_⟩
  intro G
  obtain ⟨T, hgood, hc⟩ := hfamilyR G
  obtain ⟨q, hq, hsec⟩ := fp81s21_operator_coeff_field μ G.P T K hK
    (fun u hu => (hgood u hu).choose) hc v hv
  refine ⟨q, hq, ?_⟩
  intro u hu
  obtain ⟨hmem, hmom, hcoords⟩ := hsec u hu
  refine ⟨hmem, ?_, ?_⟩
  · refine hmom.trans ?_
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg K)
    simpa only [hvnorm] using hval.2.2
  · have hagree : ∀ j, (T u (v j) : G.Ω → ℝ) =ᵐ[G.P]
        fun ω => OscDual.eval (G.Z u ω) (Es.test j) := by
      intro j
      obtain ⟨_, _, ha, _⟩ := hgood u hu
      exact ha (Es.test j) (r2Test_isOscTest _ (Es.test_smooth j)) (hval.1 j)
    filter_upwards [hcoords, ae_all_iff.mpr hagree] with ω hqω hTω j
    exact (hqω j).trans (hTω j)

#print axioms fp81s21_gaussian_strong_chart_coordinates
end HRS.Fp81.S21
end
