import HRS.MS.Fp81S21WickFam3
import HRS.MS.ProClosureS111InitialTestsApprox

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped BigOperators
namespace HRS.Fp81.S21
open HRS (Euc)
open HRS.Whole HRS.MS.R26T3 HRS.MS.ProClosureS111

def fp81s21_wickFam_coordinate_class (p : Parameters) {δ : ℝ}
    (R : Trajectory p δ)
    (hS : ∀ φ ∈ HRS.MS.S111X1.oscSub p.d (wholeSpaceIndex p.d : ℝ),
      MemLp φ 2 (HRS.Whole.withDensityReal R.ρβ)) :
    MultiIndex p.d → Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ) := fun α =>
  HRS.MS.TensRel.s111_toLp (μ := HRS.Whole.withDensityReal R.ρβ)
    (HRS.MS.S111X1.oscSub p.d (wholeSpaceIndex p.d : ℝ)) hS
    (initialTestBasis (wholeSpaceIndex p.d : ℝ) α)

/-- The oscillator-coordinate test classes span a dense subspace of the
thermal reference L² space. -/
theorem fp81s21_wickFam_coordinate_dense (p : Parameters) {δ : ℝ}
    (R : Trajectory p δ)
    (hS : ∀ φ ∈ HRS.MS.S111X1.oscSub p.d (wholeSpaceIndex p.d : ℝ),
      MemLp φ 2 (HRS.Whole.withDensityReal R.ρβ)) :
    Dense (↑(Submodule.span ℝ (Set.range (fp81s21_wickFam_coordinate_class p R hS))) :
      Set (Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ))) := by
  classical
  let S := HRS.MS.S111X1.oscSub p.d (wholeSpaceIndex p.d : ℝ)
  let T := HRS.MS.TensRel.s111_toLp (μ := HRS.Whole.withDensityReal R.ρβ) S hS
  let D := Submodule.span ℝ (Set.range fun α : MultiIndex p.d =>
    T (initialTestBasis (wholeSpaceIndex p.d : ℝ) α))
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  have hρeq : R.ρβ = HRS.Whole.thermalDensity p.d p.s p.a p.β :=
    HRS.MS.Mov0.mv0_rho_eq p.hd p.hs0 hsd p.ha p.hβ R.thermal
  have hρmeas : Measurable R.ρβ := by
    obtain ⟨-, ψ, hψ⟩ := HRS.MS.S21.s21_schwartz_thermal p.hd p.hs0 hsd p.ha p.hβ
    rw [hρeq, ← hψ]
    exact ψ.continuous.measurable
  obtain ⟨M, hM, hthermal⟩ := sol13_uniform_thermal_sup_bound p
  have htest : ∀ φ : S, T φ ∈ closure (D : Set _) := by
    intro φ
    apply mem_closure_of_tendsto (b := atTop) (f := fun n : ℕ => T (initialTestSection φ n))
    · apply tendsto_iff_norm_sub_tendsto_zero.mpr
      have hb : ∀ n : ℕ, ‖T (initialTestSection φ n) - T φ‖ ^ 2 ≤
          M * oscNorm (wholeSpaceIndex p.d : ℝ)
            ((φ - initialTestSection φ n : S) : Euc p.d → ℝ) ^ 2 := by
        intro n
        rw [norm_sub_rev, ← map_sub]
        have hi := initialTest_sq_bound hρmeas
          (fun x => (HRS.Whole.u4_thermal_pos R.thermal x).le) hM
          (hthermal δ R) (by positivity : (0 : ℝ) ≤ (wholeSpaceIndex p.d : ℝ))
          (φ - initialTestSection φ n)
        have heq : ‖T (φ - initialTestSection φ n)‖ ^ 2 =
            ∫ x, ((φ - initialTestSection φ n : S) : Euc p.d → ℝ) x ^ 2 ∂HRS.Whole.withDensityReal R.ρβ := by
          rw [← real_inner_self_eq_norm_sq, L2.inner_def]
          apply integral_congr_ae
          filter_upwards [(hS _ (φ - initialTestSection φ n).2).coeFn_toLp] with x hx
          change (T (φ - initialTestSection φ n) : Euc p.d → ℝ) x = _ at hx
          rw [hx]
          simp [sq]
        rw [heq]
        exact hi
      have htail := initialTestSection_tail φ
      have hboundlim : Tendsto (fun n : ℕ => M *
          oscNorm (wholeSpaceIndex p.d : ℝ)
            ((φ - initialTestSection φ n : S) : Euc p.d → ℝ) ^ 2) atTop (𝓝 0) := by
        simpa using tendsto_const_nhds.mul (htail.pow 2)
      have hsq : Tendsto (fun n : ℕ => ‖T (initialTestSection φ n) - T φ‖ ^ 2)
          atTop (𝓝 0) := squeeze_zero (fun n => sq_nonneg _) hb hboundlim
      have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
      simpa only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] using hsqrt
    · exact Filter.Eventually.of_forall fun n => by
        rw [initialTestSection, map_sum]
        apply Submodule.sum_mem
        intro α hα
        rw [map_smul]
        apply Submodule.smul_mem
        exact Submodule.subset_span ⟨α, rfl⟩
  have hden := fp81s21_gaussLin_test_dense p R hS
  apply Dense.of_closure
  apply hden.mono
  rintro x ⟨φ, rfl⟩
  exact htest φ

#print axioms fp81s21_wickFam_coordinate_dense
end HRS.Fp81.S21
end
