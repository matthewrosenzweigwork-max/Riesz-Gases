import HRS.MS.R26T8AP29j

/-!
# S8.2 T8A P29 (part k): linearity of the smooth pair inverse on smooth canonical remainders
For `U = s85_Ulim a β ρ M_U` and remainders `R, R'` with `C^8` weighted jets (weight `K < M_U`) that are canonical,
`pairInverseW U (R + c • R') = pairInverseW U R + c • pairInverseW U R'`, and `pairInverseW U 0 = 0`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_p29_integrableOn (hd : 2 ≤ d) (a beta K MU : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hMU : 0 < MU)
    (hK : K < MU) (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (R : Euc d → Euc d → ℝ) (B : ℝ) (hRc : ContDiff ℝ 8 (Function.uncurry R))
    (hbd : ∀ j : ℕ, j ≤ 8 → ∀ x y : Euc d, ‖iteratedFDeriv ℝ j (Function.uncurry R) (x, y)‖ ≤ B * Phase2S82.pairWeight K x y)
    (hcan : CanonicalPair (HRS.Whole.withDensityReal rho) R) (x y : Euc d) :
    IntegrableOn (fun t => HRS.Whole.tensorU (s85_Ulim a beta rho MU) t R x y) (Set.Ioi 0) := by
  have hrho' : IsThermalEquilibrium d ((d : ℝ) / 2) a beta rho := hrho
  have hU := s85_exists_semigroup hd ha hbeta hrho' hMU
  have hC5 := s8h2_c5 hd ha hbeta hrho' hMU hU 8 (by norm_num) R (by exact_mod_cast hRc) hcan.2.2
    ⟨K, hK, fun k hk => ⟨B, fun x y => by
      have := hbd k hk x y
      unfold HRS.MS.Phase2S82.pairWeight at this
      simpa [mul_assoc] using this⟩⟩
  obtain ⟨hint, -, -, -⟩ := hC5
  exact hint x y

set_option maxHeartbeats 6400000 in
theorem r26t8a_p29_inverse_lin (hd : 2 ≤ d) (a beta K MU : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hMU : 0 < MU)
    (hK : K < MU) (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (R R' : Euc d → Euc d → ℝ) (B B' : ℝ) (hB : 0 ≤ B) (hB' : 0 ≤ B')
    (hRc : ContDiff ℝ 8 (Function.uncurry R)) (hRc' : ContDiff ℝ 8 (Function.uncurry R'))
    (hbd : ∀ j : ℕ, j ≤ 8 → ∀ x y : Euc d, ‖iteratedFDeriv ℝ j (Function.uncurry R) (x, y)‖ ≤ B * Phase2S82.pairWeight K x y)
    (hbd' : ∀ j : ℕ, j ≤ 8 → ∀ x y : Euc d, ‖iteratedFDeriv ℝ j (Function.uncurry R') (x, y)‖ ≤ B' * Phase2S82.pairWeight K x y)
    (hcan : CanonicalPair (HRS.Whole.withDensityReal rho) R) (hcan' : CanonicalPair (HRS.Whole.withDensityReal rho) R')
    (c : ℝ) :
    HRS.Whole.pairInverseW (s85_Ulim a beta rho MU) (R + c • R') =
      HRS.Whole.pairInverseW (s85_Ulim a beta rho MU) R + c • HRS.Whole.pairInverseW (s85_Ulim a beta rho MU) R' := by
  obtain ⟨C, -, hC⟩ := r26t8a_smooth_pair_inverse_bounded d hd a beta MU ha hbeta hMU
  have hrho' : IsThermalEquilibrium d ((d : ℝ) / 2) a beta rho := hrho
  have hU := s85_exists_semigroup hd ha hbeta hrho' hMU
  obtain ⟨hMem, -⟩ := r26t8a_p29_pair_of_bound hB hK hRc hbd
  obtain ⟨hMem', -⟩ := r26t8a_p29_pair_of_bound hB' hK hRc' hbd'
  obtain ⟨-, -, -, -, hlin⟩ := hC rho hrho _ hU R hMem hcan ⟨K, hK, B, hbd⟩
  exact hlin R' hMem' hcan' (r26t8a_p29_integrableOn hd a beta K MU ha hbeta hMU hK rho hrho R' B' hRc' hbd' hcan') c

theorem r26t8a_p29_inverse_zero (hd : 2 ≤ d) (a beta K MU : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hMU : 0 < MU)
    (hK : K < MU) (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) :
    HRS.Whole.pairInverseW (s85_Ulim a beta rho MU) (fun _ _ : Euc d => (0 : ℝ)) = 0 := by
  have hc : ContDiff ℝ 8 (Function.uncurry (fun _ _ : Euc d => (0 : ℝ))) := contDiff_const
  have hbd : ∀ j : ℕ, j ≤ 8 → ∀ x y : Euc d,
      ‖iteratedFDeriv ℝ j (Function.uncurry (fun _ _ : Euc d => (0 : ℝ))) (x, y)‖ ≤ 0 * Phase2S82.pairWeight K x y := by
    intro j _ x y
    have : iteratedFDeriv ℝ j (Function.uncurry (fun _ _ : Euc d => (0 : ℝ))) = 0 :=
      iteratedFDeriv_fun_zero
    simp [this]
  have hcan : CanonicalPair (HRS.Whole.withDensityReal rho) (fun _ _ : Euc d => (0 : ℝ)) :=
    ⟨fun _ => integrable_zero _ _ _, fun _ => integrable_zero _ _ _, fun _ => by simp, fun _ => by simp⟩
  have h := r26t8a_p29_inverse_lin hd a beta K MU ha hbeta hMU hK rho hrho _ _ 0 0 le_rfl le_rfl hc hc hbd hbd hcan hcan 1
  have e : ((fun _ _ : Euc d => (0 : ℝ)) + (1 : ℝ) • (fun _ _ : Euc d => (0 : ℝ))) = fun _ _ => 0 := by
    funext x y; simp
  rw [e] at h
  funext x y
  have := congrFun (congrFun h x) y
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul] at this
  simp only [Pi.zero_apply]
  linarith

end HRS.MS.R26T8A

end
