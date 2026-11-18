import HRS.MS.S104eC1A

/-!
# S104E route C, packet C1 (part B): stability of the Hölder balls `HolB` under the OU semigroup
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S104e.C
open HRS HRS.Whole HRS.MS.R2WinOrbNL HRS.MS.Ul HRS.MS.Lc
variable {d : ℕ}

/-- `c1_ou_hol_stab` with the explicit constant `1`. -/
theorem s104c1_hol_stab (a ν : ℝ) (ha : 0 < a) (hν : 0 < ν) {η : ℝ} (hη0 : 0 < η) (j : ℕ)
    {h : ℝ} (hh : 0 ≤ h) {B : ℝ} {f : Euc d → ℝ} (hf : HolB j η B f) :
    HolB j η B (ouSg (ouQ d a) ν h f) := by
  refine ⟨s104c1_stab a ν ha hν (j + 1) hh hf.1, fun x z => ?_⟩
  set E := ouExp (ouQ d a) h with hE
  have hfs : ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) f := hf.1.1
  have hd := (ul3C_smooth (ouQ d a) ν h (j + 1) hfs (M := B) hf.1.2).2 (j + 1) le_rfl
  have hcont : Continuous (iteratedFDeriv ℝ (j + 1) f) :=
    hfs.continuous_iteratedFDeriv (by exact_mod_cast le_rfl)
  set T := ContinuousMultilinearMap.compContinuousLinearMapL (F := ℝ) (fun _ : Fin (j + 1) => E) with hT
  have hTn : ∀ m, ‖T m‖ ≤ ‖m‖ := fun m => s104c1_Dnorm ha hh (j + 1) m
  have hint : ∀ w : Euc d, Integrable (fun y => T (iteratedFDeriv ℝ (j + 1) f (w + y)))
      (ouLaw (ouQ d a) ν h) := fun w =>
    Integrable.of_bound (T.continuous.comp (hcont.comp (continuous_const.add continuous_id))).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun y => (hTn _).trans (hf.1.2 (j + 1) le_rfl _))
  rw [hd x, hd (x + z)]
  simp only [map_add]
  change ‖(∫ y, T (iteratedFDeriv ℝ (j + 1) f (E x + E z + y)) ∂(ouLaw (ouQ d a) ν h)) -
    ∫ y, T (iteratedFDeriv ℝ (j + 1) f (E x + y)) ∂(ouLaw (ouQ d a) ν h)‖ ≤ B * ‖z‖ ^ η
  rw [← integral_sub (by simpa [add_assoc] using hint (E x + E z)) (hint (E x))]
  have hEz : ‖E z‖ ≤ ‖z‖ := by
    calc ‖E z‖ ≤ ‖E‖ * ‖z‖ := E.le_opNorm z
      _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right (s104c1_Enorm ha hh) (norm_nonneg _)
      _ = ‖z‖ := one_mul _
  have := norm_integral_le_of_norm_le_const (μ := ouLaw (ouQ d a) ν h)
    (f := fun y => T (iteratedFDeriv ℝ (j + 1) f (E x + E z + y)) - T (iteratedFDeriv ℝ (j + 1) f (E x + y)))
    (C := B * ‖z‖ ^ η)
    (Filter.Eventually.of_forall fun y => by
      rw [← map_sub]
      refine (hTn _).trans ?_
      have h1 := hf.2 (E x + y) (E z)
      rw [show E x + E z + y = E x + y + E z by abel]
      refine h1.trans ?_
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hEz hη0.le) (hf.1.nonneg))
  simpa using this

/-- Stability in `C^{j+1,η}` (the skeleton statement `c1_ou_hol_stab`, with `C = 1`). -/
theorem c1_ou_hol_stab (a ν : ℝ) (ha : 0 < a) (hν : 0 < ν) {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (j : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ h : ℝ, 0 ≤ h → ∀ (B : ℝ) (f : Euc d → ℝ), HolB j η B f →
      HolB j η (C * B) (ouSg (ouQ d a) ν h f) :=
  ⟨1, le_rfl, fun h hh B f hf => by simpa using s104c1_hol_stab a ν ha hν hη0 j hh hf⟩

end HRS.MS.S104e.C
