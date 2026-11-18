import HRS.MS.R26T8AP29b

/-!
# S8.2 T8A P29 (part c): `pairA` of the symmetrization
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_p29_pairA_swap (C : WholeCoeff d) (mu : Measure (Euc d)) (F : Euc d → Euc d → ℝ) (x y : Euc d) :
    pairA C mu (fun x y => F y x) x y = pairA C mu F y x := by
  unfold pairA
  beta_reduce
  ring

theorem r26t8a_p29_pairA_sym (hd : 2 ≤ d) (a beta M sigma : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M)
    (hsd : sigma < d) (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {F : Euc d → Euc d → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hF : Conormal 2 1 M (sigma - 2) A F) {x y : Euc d} (hxy : x ≠ y) :
    pairA (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) (r26t8a_p29_sym F) x y =
      (1 / 2) * (pairA (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) F x y +
        pairA (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) F y x) := by
  have hFs : Conormal 2 1 M (sigma - 2) A (fun x y => F y x) := r26t8a_f24_conormal_swap hchi hF
  have hG : Conormal 2 1 M (sigma - 2) (A + A) (fun x y => F x y + F y x) := r26t8a_conormal_add hchi hF hFs
  have h1 := r26t8a_T3_pairA_smul hd (critCoeff d a beta rho) rho hG (1 / 2 : ℝ) hxy
  have h2 := r26t8a_V2_pairA_add hd a beta M sigma ha hbeta hM hsd rho hrho hchi hA hA hF hFs hxy
  have h3 := r26t8a_p29_pairA_swap (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) F x y
  show pairA (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) (fun x y => (1 / 2 : ℝ) * (F x y + F y x)) x y = _
  rw [h1, h2, h3]

end HRS.MS.R26T8A

end
