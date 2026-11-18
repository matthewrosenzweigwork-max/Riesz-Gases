import HRS.MS.R26T8AP29l

/-!
# S8.2 T8A P29 (part q): linearity and constants of the corrector map `f ↦ Q0 f + sym (pairInverseW U (R f))`
Generic in the kernels `Q0 f`, `R f`: if `Q0` and `R` are linear (`Q0 (f + c g) = Q0 f + c Q0 g`, same for `R`) and the remainders
have `C^8` weighted jets and are canonical, then so is the map.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_p29_testBound_nonneg {k : ℕ} (hk : 1 ≤ k) {A : ℝ} {f : Euc d → ℝ} (hf : TestBound k A f) : 0 ≤ A :=
  le_trans (norm_nonneg _) (hf.2 1 le_rfl hk 0)

theorem r26t8a_p29_map_linear (hd : 2 ≤ d) (a beta K MU : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hMU : 0 < MU)
    (hK : K < MU) (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Qf Qg Qfg Rf Rg Rfg : Euc d → Euc d → ℝ) (B B' : ℝ) (hB : 0 ≤ B) (hB' : 0 ≤ B') (c : ℝ)
    (hQ : Qfg = Qf + c • Qg) (hR : Rfg = Rf + c • Rg)
    (hRc : ContDiff ℝ 8 (Function.uncurry Rf)) (hRc' : ContDiff ℝ 8 (Function.uncurry Rg))
    (hbd : ∀ j : ℕ, j ≤ 8 → ∀ x y : Euc d, ‖iteratedFDeriv ℝ j (Function.uncurry Rf) (x, y)‖ ≤ B * Phase2S82.pairWeight K x y)
    (hbd' : ∀ j : ℕ, j ≤ 8 → ∀ x y : Euc d, ‖iteratedFDeriv ℝ j (Function.uncurry Rg) (x, y)‖ ≤ B' * Phase2S82.pairWeight K x y)
    (hcan : CanonicalPair (HRS.Whole.withDensityReal rho) Rf) (hcan' : CanonicalPair (HRS.Whole.withDensityReal rho) Rg) :
    (fun x y => Qfg x y + r26t8a_p29_sym (HRS.Whole.pairInverseW (s85_Ulim a beta rho MU) Rfg) x y) =
      (fun x y => Qf x y + r26t8a_p29_sym (HRS.Whole.pairInverseW (s85_Ulim a beta rho MU) Rf) x y) +
        c • (fun x y => Qg x y + r26t8a_p29_sym (HRS.Whole.pairInverseW (s85_Ulim a beta rho MU) Rg) x y) := by
  have hlin := r26t8a_p29_inverse_lin hd a beta K MU ha hbeta hMU hK rho hrho Rf Rg B B' hB hB' hRc hRc' hbd hbd' hcan hcan' c
  funext x y
  rw [hR, hlin, hQ]
  simp only [r26t8a_p29_sym, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem r26t8a_p29_map_zero (hd : 2 ≤ d) (a beta K MU : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hMU : 0 < MU)
    (hK : K < MU) (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Q R : Euc d → Euc d → ℝ) (hQ : Q = 0) (hR : R = 0) :
    (fun x y => Q x y + r26t8a_p29_sym (HRS.Whole.pairInverseW (s85_Ulim a beta rho MU) R) x y) = 0 := by
  have hz := r26t8a_p29_inverse_zero hd a beta K MU ha hbeta hMU hK rho hrho
  have hR' : R = fun _ _ => 0 := by rw [hR]; rfl
  funext x y
  rw [hR', hz, hQ]
  simp [r26t8a_p29_sym]

end HRS.MS.R26T8A

end
