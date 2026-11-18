import HRS.MS.S82VS5

/-!
# S8.2 A02 (S82V), part 11: the local Poisson identity `(L₀ₓ + L₀ᵧ) Q = -H - J`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82V
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

/-- The projected generator splits into the local part and the projected nonlocal part. -/
lemma s82v_projGen (C : WholeCoeff d) (mu : Measure (Euc d)) (psi : Euc d → ℝ)
    (hint : Integrable (fun w => C.ν * Laplacian.laplacian psi w +
      inner ℝ (C.drift 0 w) (gradient psi w)) mu)
    (hzero : ∫ w, (C.ν * Laplacian.laplacian psi w +
      inner ℝ (C.drift 0 w) (gradient psi w)) ∂mu = 0) (z : Euc d) :
    HRS.Whole.projGeneratorW C mu 0 psi z =
      C.ν * Laplacian.laplacian psi z + inner ℝ (C.drift 0 z) (gradient psi z) +
        HRS.Whole.projMean mu (fun x' => oneJ C psi x') z := by
  have hgen : ∀ w, generatorW C 0 psi w = (C.ν * Laplacian.laplacian psi w +
      inner ℝ (C.drift 0 w) (gradient psi w)) + oneJ C psi w := fun w => by
    unfold oneJ; ring
  have hint2 : ∫ w, generatorW C 0 psi w ∂mu = ∫ w, oneJ C psi w ∂mu := by
    simp_rw [hgen]
    by_cases h : Integrable (fun w => oneJ C psi w) mu
    · rw [integral_add hint h, hzero, zero_add]
    · have h' : ¬ Integrable (fun w => (C.ν * Laplacian.laplacian psi w +
          inner ℝ (C.drift 0 w) (gradient psi w)) + oneJ C psi w) mu := by
        intro h2
        apply h
        refine (h2.sub hint).congr (Filter.Eventually.of_forall fun w => ?_)
        simp
      rw [integral_undef h', integral_undef h]
  unfold HRS.Whole.projGeneratorW HRS.Whole.projMean HRS.Whole.pair
  rw [hint2, hgen]
  ring

/-- The local Poisson identity at a pair of distinct points. -/
theorem s82v_pair_poisson (hd : 2 ≤ d) {a beta M A : ℝ} (ha : 0 < a) (hbeta : 0 < beta)
    {rho : Euc d → ℝ} (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) {f : Euc d → ℝ}
    {Q : Euc d → Euc d → ℝ} (hQ : PairCorrector a beta rho M A f Q) (x y : Euc d) (hxy : x ≠ y) :
    ((critCoeff d a beta rho).ν * Laplacian.laplacian (fun w => Q w y) x +
        inner ℝ ((critCoeff d a beta rho).drift 0 x) (gradient (fun w => Q w y) x)) +
      ((critCoeff d a beta rho).ν * Laplacian.laplacian (fun w => Q w x) y +
        inner ℝ ((critCoeff d a beta rho).drift 0 y) (gradient (fun w => Q w x) y)) =
      -HSource (HRS.Whole.withDensityReal rho) f x y -
        pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Q x y := by
  have hP := hQ.poisson x y hxy
  have e : Q x = fun w => Q w x := funext fun w => hQ.symmetric x w
  obtain ⟨h1, h2⟩ := s82v_row_stat hd ha hbeta hrho hQ y
  obtain ⟨h3, h4⟩ := s82v_row_stat hd ha hbeta hrho hQ x
  have hA : pairA (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Q x y =
      ((critCoeff d a beta rho).ν * Laplacian.laplacian (fun w => Q w y) x +
        inner ℝ ((critCoeff d a beta rho).drift 0 x) (gradient (fun w => Q w y) x)) +
      ((critCoeff d a beta rho).ν * Laplacian.laplacian (fun w => Q w x) y +
        inner ℝ ((critCoeff d a beta rho).drift 0 y) (gradient (fun w => Q w x) y)) +
      pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Q x y := by
    unfold pairA pairJ
    rw [e, s82v_projGen _ _ _ h1 h2 x, s82v_projGen _ _ _ h3 h4 y]
    ring
  linarith

end HRS.MS.S82V

end
