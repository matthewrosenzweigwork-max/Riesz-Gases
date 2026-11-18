import HRS.MS.R26T8AP29L1
import HRS.MS.R26T8AV3
import HRS.MS.R26T8AP20b

/-!
# S8.2 T8A P29 (linearity, part 2): the zero remainder, `Psi`, and linearity / annihilation of constants of `Psi`

`r26t8a_p29_Psi C0 mu chi U f = parametrixZero f + sym (pairInverseW U (remainder f))`;
`r26t8a_p29_Psi_linear`: `Psi (f + c g) = Psi f + c Psi g` for `TestBound` data; `r26t8a_p29_Psi_const`: `Psi (const) = 0`.
`r26t8a_P20spec` is the conclusion of `r26t8a_finite_parametrix` for the constants `(C, M)`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

/-- the conclusion of `r26t8a_finite_parametrix` for the constants `C, M` -/
def r26t8a_P20spec (d : ℕ) (a beta : ℝ) (chi : Euc d → ℝ) (C M : ℝ) : Prop :=
  ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ f : Euc d → ℝ, ∀ A : ℝ, 0 ≤ A → TestBound (testOrder d) A f →
      ∃ Q R : Euc d → Euc d → ℝ,
        Q = r26t8a_parametrixZero (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f ∧
        R = r26t8a_remainder (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f ∧
        CanonicalPair (HRS.Whole.withDensityReal rho) Q ∧
        CanonicalPair (HRS.Whole.withDensityReal rho) R ∧
        (∀ x y, Q x y = Q y x ∧ R x y = R y x) ∧
        Conormal 8 1 M (criticalS d - 2) (C * A) Q ∧
        ContDiff ℝ 8 (Function.uncurry R) ∧
        (∀ j : ℕ, j ≤ 8 → ∀ x y,
          ‖iteratedFDeriv ℝ j (Function.uncurry R) (x, y)‖ ≤
            C * A * HRS.MS.Phase2S82.pairWeight M x y) ∧
        ∀ x y, x ≠ y →
          -pairA (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Q x y =
            HSource (HRS.Whole.withDensityReal rho) f x y - R x y

/-- the corrector kernel `Psi f = parametrixZero f + sym (pairInverseW U (remainder f))` -/
def r26t8a_p29_Psi (C0 : WholeCoeff d) (mu : Measure (Euc d)) (chi : Euc d → ℝ)
    (U : ℝ → (Euc d → ℝ) → Euc d → ℝ) (f : Euc d → ℝ) : Euc d → Euc d → ℝ :=
  fun x y => r26t8a_parametrixZero C0 mu chi f x y +
    r26t8a_p29_sym (HRS.Whole.pairInverseW U (r26t8a_remainder C0 mu chi f)) x y

set_option maxHeartbeats 6400000 in
theorem r26t8a_p29_psi_zero (hd : 2 ≤ d) (a beta K MU : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hMU : 0 < MU) (hK : K < MU)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) :
    r26t8a_p29_sym (HRS.Whole.pairInverseW (s85_Ulim a beta rho MU) (fun _ _ : Euc d => (0 : ℝ))) =
      fun _ _ => 0 := by
  have h0 : r26t8a_p29_RemHyp d rho K 0 (fun _ _ : Euc d => (0 : ℝ)) := by
    refine ⟨contDiff_const, fun j hj x y => ?_, r26t8a_V3_canonical_zero _⟩
    have : iteratedFDeriv ℝ j (Function.uncurry (fun _ _ : Euc d => (0 : ℝ))) (x, y) = 0 := by
      have : Function.uncurry (fun _ _ : Euc d => (0 : ℝ)) = fun _ => (0 : ℝ) := rfl
      rw [this]
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · simp
      · exact congrFun (iteratedFDeriv_const_of_ne (𝕜 := ℝ) (E := Euc d × Euc d) (Nat.pos_iff_ne_zero.1 hj0) (0 : ℝ)) (x, y)
    rw [this]; simp
  have hl := r26t8a_p29_psi_lin hd a beta K MU ha hbeta hMU hK rho hrho _ _ 0 0 le_rfl le_rfl h0 h0 1
  have e : ((fun _ _ : Euc d => (0 : ℝ)) + (1 : ℝ) • (fun _ _ : Euc d => (0 : ℝ))) = fun _ _ : Euc d => (0 : ℝ) := by
    funext x y; simp
  rw [e] at hl
  funext x y
  have := congrFun (congrFun hl x) y
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul] at this
  linarith

end HRS.MS.R26T8A

end
