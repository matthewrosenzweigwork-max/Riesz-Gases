import HRS.MS.R26T8AP29d

/-!
# S8.2 T8A P29 (linearity, part 1): the symmetrized smooth pair inverse is linear in the remainder

For two remainders `R1, R2` (`C^8`, weighted jets of weight `K < MU`, canonical) and every `c`:
`sym (pairInverseW U (R1 + c R2)) = sym (pairInverseW U R1) + c • sym (pairInverseW U R2)`, `U = s85_Ulim a β ρ MU`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

/-- the weighted jet hypothesis on a remainder kernel -/
def r26t8a_p29_RemHyp (d : ℕ) (rho : Euc d → ℝ) (K B : ℝ) (R : Euc d → Euc d → ℝ) : Prop :=
  ContDiff ℝ 8 (Function.uncurry R) ∧
  (∀ j : ℕ, j ≤ 8 → ∀ x y : Euc d, ‖iteratedFDeriv ℝ j (Function.uncurry R) (x, y)‖ ≤ B * Phase2S82.pairWeight K x y) ∧
  CanonicalPair (HRS.Whole.withDensityReal rho) R

set_option maxHeartbeats 6400000 in
theorem r26t8a_p29_psi_lin (hd : 2 ≤ d) (a beta K MU : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hMU : 0 < MU) (hK : K < MU)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (R1 R2 : Euc d → Euc d → ℝ) (B1 B2 : ℝ) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (h1 : r26t8a_p29_RemHyp d rho K B1 R1) (h2 : r26t8a_p29_RemHyp d rho K B2 R2) (c : ℝ) :
    r26t8a_p29_sym (HRS.Whole.pairInverseW (s85_Ulim a beta rho MU) (R1 + c • R2)) =
      r26t8a_p29_sym (HRS.Whole.pairInverseW (s85_Ulim a beta rho MU) R1) +
        c • r26t8a_p29_sym (HRS.Whole.pairInverseW (s85_Ulim a beta rho MU) R2) := by
  obtain ⟨C, hC0, hC⟩ := r26t8a_smooth_pair_inverse_bounded d hd a beta MU ha hbeta hMU
  have hrho' : IsThermalEquilibrium d ((d : ℝ) / 2) a beta rho := hrho
  have hU := s85_exists_semigroup hd ha hbeta hrho' hMU
  obtain ⟨hc1, hb1, hcan1⟩ := h1
  obtain ⟨hc2, hb2, hcan2⟩ := h2
  obtain ⟨hMem1, -⟩ := r26t8a_p29_pair_of_bound hB1 hK hc1 hb1
  obtain ⟨hMem2, -⟩ := r26t8a_p29_pair_of_bound hB2 hK hc2 hb2
  obtain ⟨-, -, -, -, hlin⟩ := hC rho hrho _ hU R1 hMem1 hcan1 ⟨K, hK, B1, hb1⟩
  have hC5 := s8h2_c5 hd ha hbeta hrho' hMU hU 8 (by norm_num) R2 (by exact_mod_cast hc2) hcan2.2.2
    ⟨K, hK, fun k hk => ⟨B2, fun x y => by
      have := hb2 k hk x y
      unfold HRS.MS.Phase2S82.pairWeight at this
      simpa [mul_assoc] using this⟩⟩
  have hinv := hlin R2 hMem2 hcan2 hC5.1 c
  funext x y
  unfold r26t8a_p29_sym
  have e1 := congrFun (congrFun hinv x) y
  have e2 := congrFun (congrFun hinv y) x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 ⊢
  rw [e1, e2]
  ring

end HRS.MS.R26T8A

end
