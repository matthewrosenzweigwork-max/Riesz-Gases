import HRS.MS.Fp81S21WickApprox28
import HRS.MS.Fp81S21WickApprox12

/-! Supplied Gaussian physical finite-rank time-error assembly. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter
open scoped BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

local instance fp81s21_wickApprox29_measSpace (H : ℝ) : MeasurableSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := borel _
local instance fp81s21_wickApprox29_borelSpace (H : ℝ) : BorelSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := ⟨rfl⟩

/-- The supplied Wick operator's fixed-test profile and finite-coordinate
versions imply the corresponding genuine time-L² squared error. -/
theorem fp81s21_wick_rankKernel_time_sqerr2
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ) (G : GaussianRealization R)
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (m : ℕ) (v : Fin m → Lp ℝ 2 ((HRS.Whole.withDensityReal R.ρβ).prod
      (HRS.Whole.withDensityReal R.ρβ)))
    (W : ℝ → Lp ℝ 2 ((HRS.Whole.withDensityReal R.ρβ).prod
      (HRS.Whole.withDensityReal R.ρβ)) →L[ℝ] Lp ℝ 2 G.P)
    (Q : ℝ → G.Ω → (Euc p.d → ℝ) → ℝ)
    (q r : ℝ → G.Ω → r26t6_Coeff) (Mq Mr a H ε : ℝ)
    (ha : 0 ≤ a) (hH : 0 ≤ H)
    (hqm : Measurable (Function.uncurry q))
    (hqcoord : ∀ u, 0 ≤ u → ∀ᵐ ω ∂G.P, ∀ j : ℕ,
      q u ω j = if hj : j < m then
        (W u (v ⟨j, hj⟩) : G.Ω → ℝ) ω else 0)
    (hrep : fp81s21_MomentRep E G.P Q r Mr)
    (U V : G.Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)))
    (hU : fp81s21_TimeL2Rep G.P q Mq a H U)
    (hV : fp81s21_TimeL2Rep G.P r Mr a H V)
    (hfixed : ∀ u, 0 ≤ u → ∀ j : Fin m,
      fp81s21_SqErr G.P (fun ω => W u (v j) ω)
        (fun ω => Q u ω (E.test j)) ε) :
    fp81s21_SqErr G.P U (fun ω => fp81s21_timeProject H m (V ω))
      (Real.sqrt (H * (m : ℝ)) * ε) := by
  let rproj : ℝ → G.Ω → r26t6_Coeff := fun u ω => fp81s21_projectField m (r u ω)
  have hrm : Measurable (Function.uncurry rproj) :=
    (fp81s21_projectField m).continuous.measurable.comp hrep.1
  have hVp : fp81s21_TimeL2Rep G.P rproj Mr a H
      (fun ω => fp81s21_timeProject H m (V ω)) :=
    fp81s21_TimeL2Rep_project2 G.P r Mr a H m V hV
  have hsupport : ∀ u, 0 ≤ u → ∀ᵐ ω ∂G.P,
      fp81s21_projectField m (q u ω - rproj u ω) = q u ω - rproj u ω := by
    intro u hu
    filter_upwards [hqcoord u hu] with ω hω
    ext j
    rw [fp81s21_projectField_coordinate2]
    by_cases hj : j < m
    · simp [hj]
    · simp only [hj, ↓reduceIte, lp.coeFn_sub, Pi.sub_apply]
      simp [hω j, hj, rproj, fp81s21_projectField_coordinate2]
  have hcoord : ∀ u, 0 ≤ u → ∀ j ∈ Finset.range m,
      fp81s21_SqErr G.P (fun ω => q u ω j) (fun ω => rproj u ω j) ε := by
    intro u hu j hj
    let i : Fin m := ⟨j, Finset.mem_range.mp hj⟩
    have hfixed' := hfixed u hu i
    have he : (fun ω => ‖W u (v i) ω -
        Q u ω (E.test j)‖ ^ 2) =ᵐ[G.P]
        (fun ω => ‖q u ω j - rproj u ω j‖ ^ 2) := by
      filter_upwards [hqcoord u hu, (hrep.2 u hu).2.2] with ω hqω hrω
      have hqcoord' : q u ω j = W u (v i) ω := by
        simpa [i, Finset.mem_range.mp hj] using hqω j
      have hrcoord : rproj u ω j = Q u ω (E.test j) := by
        rw [show rproj u ω j = r u ω j by simp [rproj, fp81s21_projectField_coordinate2,
          Finset.mem_range.mp hj]]
        rw [← fp81s21_chartAction_test_coordinate2 E (r u ω) j]
        exact hrω.1 (E.test j) (E.test_smooth j)
      rw [hqcoord', hrcoord]
    exact ⟨hfixed'.1.congr he, by rw [← integral_congr_ae he]; exact hfixed'.2⟩
  exact fp81s21_time_finite_coordinate_sqerr G.P q rproj Mq Mr a H U
    (fun ω => fp81s21_timeProject H m (V ω)) hqm hrm hU hVp ha hH m ε hsupport hcoord

#print axioms fp81s21_wick_rankKernel_time_sqerr2
end HRS.Fp81.S21
end
