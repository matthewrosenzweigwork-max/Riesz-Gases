import HRS.MS.R26T8AP29c

/-!
# S8.2 T8A P29 (part d): the symmetrized smooth pair inverse of a smooth symmetric canonical remainder
For `R` with `C^8` weighted jets (weight `K`) that is symmetric and canonical, `Ψ := sym (pairInverseW U R)` (with the S8.3
semigroup `U = s85_Ulim a β ρ M_U`, `K < M_U`) is symmetric, canonical, `C^8`, has jets `≤ C B pairWeight M_U` and solves
`-pairA Ψ = R` off the diagonal.  The constant `C` depends only on `d, a, β, M_U`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

set_option maxHeartbeats 6400000 in
theorem r26t8a_p29_psi (hd : 2 ≤ d) (a beta K MU : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hMU : 0 < MU) (hK : K < MU) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ, IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ (R : Euc d → Euc d → ℝ) (B : ℝ), 0 ≤ B → ContDiff ℝ 8 (Function.uncurry R) →
      (∀ j : ℕ, j ≤ 8 → ∀ x y : Euc d, ‖iteratedFDeriv ℝ j (Function.uncurry R) (x, y)‖ ≤ B * Phase2S82.pairWeight K x y) →
      CanonicalPair (HRS.Whole.withDensityReal rho) R → (∀ x y, R x y = R y x) →
      let Psi := r26t8a_p29_sym (HRS.Whole.pairInverseW (s85_Ulim a beta rho MU) R)
      CanonicalPair (HRS.Whole.withDensityReal rho) Psi ∧ ContDiff ℝ 8 (Function.uncurry Psi) ∧
      (∀ x y, Psi x y = Psi y x) ∧
      (∀ j : ℕ, j ≤ 8 → ∀ x y : Euc d, ‖iteratedFDeriv ℝ j (Function.uncurry Psi) (x, y)‖ ≤ C * B * Phase2S82.pairWeight MU x y) ∧
      (∀ x y, x ≠ y → -pairA (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Psi x y = R x y) := by
  obtain ⟨C, hC0, hC⟩ := r26t8a_smooth_pair_inverse_bounded d hd a beta MU ha hbeta hMU
  refine ⟨C, hC0, fun rho hrho R B hB hRc hbd hcan hsymm => ?_⟩
  intro Psi
  have hrho' : IsThermalEquilibrium d ((d : ℝ) / 2) a beta rho := hrho
  have hU := s85_exists_semigroup hd ha hbeta hrho' hMU
  obtain ⟨hMem, hnormR⟩ := r26t8a_p29_pair_of_bound hB hK hRc hbd
  obtain ⟨hcanΨ, hcdΨ, hnormΨ, hpois, -⟩ := hC rho hrho _ hU R hMem hcan ⟨K, hK, B, hbd⟩
  have hnorm : pairNormE MU 8 (HRS.Whole.pairInverseW (s85_Ulim a beta rho MU) R) ≤ ENNReal.ofReal (C * B) := by
    refine hnormΨ.trans ?_
    rw [ENNReal.ofReal_mul hC0]
    exact mul_le_mul_of_nonneg_left hnormR (zero_le)
  have hjet := r26t8a_p29_of_norm (mul_nonneg hC0 hB) hnorm
  have hcd : ContDiff ℝ 8 (Function.uncurry (HRS.Whole.pairInverseW (s85_Ulim a beta rho MU) R)) := by
    exact_mod_cast hcdΨ
  refine ⟨r26t8a_p29_sym_canonical hcanΨ, r26t8a_p29_sym_contDiff hcd, r26t8a_p29_sym_symm _,
    fun j hj x y => r26t8a_p29_sym_jets hcd hjet j hj x y, fun x y hxy => ?_⟩
  -- the Poisson equation
  obtain ⟨chi, hchi⟩ := r26t8a_p10a_exists_cutoff d
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : criticalS d < d := by unfold criticalS; linarith
  have hCB : 0 ≤ C * B := mul_nonneg hC0 hB
  have hcon : Conormal 2 1 MU (criticalS d - 2) (2 ^ 2 * (C * B))
      (HRS.Whole.pairInverseW (s85_Ulim a beta rho MU) R) :=
    r26t8a_conormal_of_smooth hCB (hcd.of_le (by norm_num)) (fun j hj x y => hjet j (by omega) x y)
  have hA2 : 0 ≤ 2 ^ 2 * (C * B) := by positivity
  have hs := r26t8a_p29_pairA_sym hd a beta MU (criticalS d) ha hbeta hMU.le hsd rho hrho hchi hA2 hcon hxy
  show -pairA (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho)
      (r26t8a_p29_sym (HRS.Whole.pairInverseW (s85_Ulim a beta rho MU) R)) x y = R x y
  rw [hs]
  have e1 := hpois x y
  have e2 := hpois y x
  rw [hsymm y x] at e2
  linarith

end HRS.MS.R26T8A

end
