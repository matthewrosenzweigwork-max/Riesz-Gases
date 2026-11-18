import HRS.MS.R26T8AO03b11

/-!
# S8.2 T8A O03b (part 12): the corrected drift defect `D` has mean zero under the Gibbs law
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82U HRS.MS.S82W HRS.MS.Wad

variable {d : ℕ}

set_option maxHeartbeats 6400000 in
theorem r26t8a_o03b_D_mean_zero (N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N) (a beta M C : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ) (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    {A : ℝ} {f : Euc d → ℝ} (hf : TestBound (testOrder d) A f) :
    ∫ Y, r26t8a_correctedD (N := N) a beta rho Psi f Y ∂(canonicalP d N a beta) = 0 := by
  haveI hPp : IsProbabilityMeasure (canonicalP d N a beta) := HRS.MS.S82U.u4_prob (N := N) hd ha hbeta
  set P := canonicalP d N a beta with hPdef
  have hk : 1 ≤ testOrder d := by unfold testOrder; omega
  have hA := r26t8a_o03b_tb_nonneg hk hf
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hDint : Integrable (r26t8a_correctedD (N := N) a beta rho Psi f) P :=
    (hPsi.bound N hN f A hA hf).1.integrable one_le_two
  obtain ⟨Ca, hCa0, hCa⟩ := r26t8a_o02_aSource_bound hd ha hbeta hrho
  have hacont := r26t8a_o03b_aSource_cont hd ha hbeta hrho hf
  set μ := HRS.Whole.withDensityReal rho with hμ
  set S : EucConfig d N → ℝ := fun Y => (1 / (N : ℝ)) * ∑ i, aSource μ f (Y i) with hS
  have hSint : Integrable S P := by
    refine Integrable.mono' (integrable_const (Ca * A)) ?_ (Filter.Eventually.of_forall fun Y => ?_)
    · exact (continuous_const.mul (continuous_finset_sum _ fun i _ =>
        hacont.comp (continuous_apply i))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, hS]
      show |1 / (N : ℝ) * ∑ i, aSource μ f (Y i)| ≤ Ca * A
      rw [abs_mul, abs_of_pos (by positivity)]
      have h1 : |∑ i, aSource μ f (Y i)| ≤ N * (Ca * A) := by
        calc |∑ i, aSource μ f (Y i)| ≤ ∑ i, |aSource μ f (Y i)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i : Fin N, Ca * A := Finset.sum_le_sum fun i _ => hCa f A hA hf (Y i)
          _ = N * (Ca * A) := by simp
      calc 1 / (N : ℝ) * |∑ i, aSource μ f (Y i)| ≤ 1 / (N : ℝ) * (N * (Ca * A)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = Ca * A := by field_simp
  set ζ : EucConfig d N → ℝ := fun Y => Real.sqrt N * (S Y - ∫ Z, S Z ∂P) with hζ
  have hζint : Integrable ζ P := (hSint.sub (integrable_const _)).const_mul _
  have hζ0 : ∫ Y, ζ Y ∂P = 0 := by
    simp only [hζ]
    rw [integral_const_mul, integral_sub hSint (integrable_const _)]
    simp
  set E : EucConfig d N → ℝ := errorStatistic (critCoeff d a beta rho) rho (Psi f) with hE
  set c0 : ℝ := ∫ Y, E Y ∂P with hc0
  set Ec : EucConfig d N → ℝ := fun Y => E Y - c0 with hEc
  have hDeq : ∀ Y, r26t8a_correctedD (N := N) a beta rho Psi f Y = Ec Y - (2 / (N : ℝ)) * ζ Y := fun Y => rfl
  have hEcint : Integrable Ec P := by
    have := hDint.add (hζint.const_mul (2 / (N : ℝ)))
    refine this.congr (Filter.Eventually.of_forall fun Y => ?_)
    simp only [Pi.add_apply, hDeq]; ring
  have hEint : Integrable E P := by
    have := hEcint.add (integrable_const c0)
    refine this.congr (Filter.Eventually.of_forall fun Y => ?_)
    simp only [Pi.add_apply, hEc]; ring
  have hEc0 : ∫ Y, Ec Y ∂P = 0 := by
    simp only [hEc]
    rw [integral_sub hEint (integrable_const _)]
    simp [hc0]
  have : ∫ Y, r26t8a_correctedD (N := N) a beta rho Psi f Y ∂P = ∫ Y, (Ec Y - (2 / (N : ℝ)) * ζ Y) ∂P :=
    integral_congr_ae (Filter.Eventually.of_forall hDeq)
  rw [this, integral_sub hEcint (hζint.const_mul _), integral_const_mul, hEc0, hζ0]
  simp

end HRS.MS.R26T8A
