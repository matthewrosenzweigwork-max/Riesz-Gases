import HRS.MS.SA12K4

/-!
# S.A.12 C1, the cutoff-normalised density and its uniform bounds

`f0 = Z⁻¹ ζ_L ρ(t)`, `μ0 = perL L f0`.  Uniform in `ρ` (with `CoeffHypRd`), `t ∈ [0,T]` and `L ≥ L₁`:
`Z ≥ 1/2`, weighted bounds of `f0`, global bounds of `μ0`, and the cube `L¹` bounds.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MS.ToriCoefA HRS.MS.ToriCoefB

variable {d : ℕ}

/-- `f0 = Z⁻¹ ζ_L ρ`. -/
def sa12k_f0 (ζ : Euc d → ℝ) (ρ : Euc d → ℝ) (L : ℝ) : Euc d → ℝ :=
  fun x => (∫ y, ζ (L⁻¹ • y) * ρ y)⁻¹ * (ζ (L⁻¹ • x) * ρ x)

/-- `μ0 = perL L f0`. -/
def sa12k_mu0 (ζ : Euc d → ℝ) (ρ : Euc d → ℝ) (L : ℝ) : Euc d → ℝ :=
  perL L (sa12k_f0 ζ ρ L)

theorem sa12k_base (s : ℝ) (m : ℕ) (T Λ : ℝ) (ζ : Euc d → ℝ)
    (hζ : IsCutoffRad (1 / 4) (1 / 3) ζ) :
    ∃ Bd Bc L₁ : ℝ, 0 ≤ Bd ∧ 0 ≤ Bc ∧ 7 ≤ L₁ ∧
      ∀ ρ : ℝ → Euc d → ℝ, CoeffHypRd s m Λ T ρ → ∀ L : ℝ, L₁ ≤ L → ∀ t ∈ Icc (0 : ℝ) T,
        1 / 2 ≤ ∫ y, ζ (L⁻¹ • y) * ρ t y ∧
        (∀ y : Euc d, L / 3 ≤ ‖y‖ → sa12k_f0 ζ (ρ t) L y = 0) ∧
        ContDiff ℝ ((m + 3 : ℕ) : WithTop ℕ∞) (sa12k_f0 ζ (ρ t) L) ∧
        ContDiff ℝ ((m + 3 : ℕ) : WithTop ℕ∞) (sa12k_mu0 ζ (ρ t) L) ∧
        (∀ j ≤ m + 3, ∀ y : Euc d, ‖iteratedFDeriv ℝ j (sa12k_mu0 ζ (ρ t) L) y‖ ≤ Bd) ∧
        (∀ j ≤ m + 3, ∀ w : Euc d,
          ‖iteratedFDeriv ℝ j (sa12k_f0 ζ (ρ t) L) w‖ ≤ Bd * tca_g w) ∧
        (∀ j ≤ m + 3, ∀ x : Euc d,
          ∫ z in tcb_Q d L, ‖iteratedFDeriv ℝ j (sa12k_mu0 ζ (ρ t) L) (x - z)‖ ≤ Bc) ∧
        (∀ y, 0 ≤ sa12k_f0 ζ (ρ t) L y) ∧ ∫ y, sa12k_f0 ζ (ρ t) L y = 1 := by
  choose K hK0 hK using fun i : ℕ => tca_bdd_iter ζ hζ i
  obtain ⟨N, hN⟩ := tca_tail (d := d) (1 / (2 * (|Λ| + 1))) (by positivity)
  have hBε : |Λ| * (1 / (2 * (|Λ| + 1))) ≤ 1 / 2 := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    nlinarith [abs_nonneg Λ]
  have hS0 : ∀ j : ℕ, 0 ≤ tca_S d K |Λ| j := fun j => tca_S_nonneg d K hK0 |Λ| (abs_nonneg _) j
  set Bd : ℝ := ∑ j ∈ Finset.range (m + 4), 2 * tca_S d K |Λ| j with hBd
  have hBd0 : 0 ≤ Bd := Finset.sum_nonneg fun j _ => by linarith [hS0 j]
  have hBdle : ∀ j : ℕ, j ≤ m + 3 → 2 * tca_S d K |Λ| j ≤ Bd := fun j hj =>
    Finset.single_le_sum (f := fun j => 2 * tca_S d K |Λ| j) (fun i _ => by linarith [hS0 i])
      (Finset.mem_range.2 (by omega))
  set I₀ : ℝ := ∫ w : Euc d, tca_g w with hI₀
  have hI₀0 : 0 ≤ I₀ := integral_nonneg fun w => (tcb_g_pos w).le
  refine ⟨Bd, 2 ^ d * Bd * I₀, max 7 (4 * (N : ℝ)), hBd0, by positivity, le_max_left _ _, ?_⟩
  intro ρ hρ L hL t ht
  have hL7 : 7 ≤ L := (le_max_left _ _).trans hL
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hL4 : (N : ℝ) ≤ L / 4 := by
    have := (le_max_right _ _).trans hL
    linarith
  obtain ⟨hρcd, hWk, hprob⟩ := sa12k_den_facts hρ ht
  have hρB : ∀ y : Euc d, |ρ t y| ≤ |Λ| * tca_g y := by
    intro y
    exact tca_abs_le_weight (ρ t) |Λ| (fun y' => by
      have := hWk 0 (Nat.zero_le _) y'
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, pow_zero, one_mul] at this
      exact this) y
  have hZ : 1 / 2 ≤ ∫ y, ζ (L⁻¹ • y) * ρ t y :=
    tca_Z_ge hζ (ρ t) hprob |Λ| (abs_nonneg _) hρB L hL0 N hL4 _ hN hBε
  have hc0 : 0 < (∫ y, ζ (L⁻¹ • y) * ρ t y)⁻¹ := inv_pos.2 (by linarith)
  have hc2 : (∫ y, ζ (L⁻¹ • y) * ρ t y)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
    linarith
  have hvan : ∀ y : Euc d, L / 3 ≤ ‖y‖ → sa12k_f0 ζ (ρ t) L y = 0 := by
    intro y hy
    show (∫ y, ζ (L⁻¹ • y) * ρ t y)⁻¹ * (ζ (L⁻¹ • y) * ρ t y) = 0
    rw [tca_zeta_far_val hζ L hL0 y hy, zero_mul, mul_zero]
  obtain ⟨hcd, hglob, -⟩ := tca_mu_package hζ L hL1 (m + 3) (ρ t) hρcd K hK hK0 |Λ|
    (abs_nonneg _) hWk _ hc0 hc2
  have hfw := fun j hj w => tcb_f_weighted hζ L hL1 (m + 3) (ρ t) hρcd K hK hK0 |Λ|
    (abs_nonneg _) hWk _ hc0 hc2 j hj w
  have hf0cd : ContDiff ℝ ((m + 3 : ℕ) : WithTop ℕ∞) (sa12k_f0 ζ (ρ t) L) := by
    exact contDiff_const.mul ((tca_zetaL_contDiff hζ L (m + 3)).mul hρcd)
  refine ⟨hZ, hvan, hf0cd, hcd, fun j hj y => (hglob j hj y).trans (hBdle j hj), ?_, ?_, ?_, ?_⟩
  · intro j hj w
    exact (hfw j hj w).trans (mul_le_mul_of_nonneg_right (hBdle j hj) (tca_g_nonneg w))
  · intro j hj x
    refine (tcb_cube_l1 hL0 _ hvan j (2 * tca_S d K |Λ| j) (hfw j hj) x).trans ?_
    have := hBdle j hj
    have h2 : (0 : ℝ) ≤ 2 ^ d := by positivity
    calc 2 ^ d * (2 * tca_S d K |Λ| j) * ∫ w : Euc d, tca_g w
        ≤ 2 ^ d * Bd * ∫ w : Euc d, tca_g w :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this h2) hI₀0
      _ = _ := rfl
  · intro y
    show 0 ≤ (∫ y, ζ (L⁻¹ • y) * ρ t y)⁻¹ * (ζ (L⁻¹ • y) * ρ t y)
    exact mul_nonneg hc0.le (mul_nonneg (hζ.2.2.2.1 _).1 (hprob.nonneg y))
  · show ∫ y, (∫ y, ζ (L⁻¹ • y) * ρ t y)⁻¹ * (ζ (L⁻¹ • y) * ρ t y) = 1
    rw [integral_const_mul]
    exact inv_mul_cancel₀ (by linarith)

end HRS.MH.AdjointRd.Phase2SA12Construction
