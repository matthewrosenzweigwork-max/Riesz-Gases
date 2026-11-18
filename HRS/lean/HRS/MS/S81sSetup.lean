import HRS.MS.S81sLinear
import HRS.MS.WsStatAux32
import HRS.MS.WsStatAux21
import HRS.MS.R2GenInitAux35

/-!
# S8.1 (worker S81S): the Section S5 setup at an arbitrary oscillator index `m ≥ wholeSpaceIndex d`

`s81s_setup`: for the critical thermal density `ρ`, a horizon `H > 0` and ANY real `m ≥ 24 d + 240`, there is a valid bound
record `b = s81s_bounds …` (definitionally `b.m = m`, `b.T = H`) and a Section S5 setup `S` for it, with `S.ρ ≡ ρ`, `S.invβ ≡ β⁻¹`, `S.κ N = √(Nβ)`,
`S.coeff N = critCoeff d a β ρ` and `OscAdjointInput (S.coeff N) m H`.  The setup `s21_setup_family` of S21 is built for the single
index `m = wholeSpaceIndex d`, but `WholeSetup b` does not depend on `b.m`, so it is re-based verbatim to any larger `m`.
-/

set_option autoImplicit false
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole

namespace HRS.Whole.S81S

variable {d : ℕ}

/-- The bound record of S21 re-based at the oscillator index `m` (definitionally `.m = m`, `.T = H`). -/
abbrev s81s_bounds (d : ℕ) (a β m H : ℝ) (θ : Euc d → ℝ) (Λ K C₀ : ℝ) : WholeBounds d :=
  { HRS.MS.S21.s21Bounds d ((d : ℝ) / 2) a β H θ Λ K C₀ with m := m }

theorem s81s_setup (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρ) {m : ℝ}
    (hm : (wholeSpaceIndex d : ℝ) ≤ m) {H : ℝ} (hH : 0 < H) :
    ∃ (θ : Euc d → ℝ) (Λ K C₀ : ℝ) (S : WholeSetup (s81s_bounds d a β m H θ Λ K C₀)),
      (s81s_bounds d a β m H θ Λ K C₀).Valid ∧
      (∀ N t, S.ρ N t = ρ) ∧ (∀ N, S.invβ N = β⁻¹) ∧
      (∀ N : ℕ, 1 ≤ N → S.κ N = Real.sqrt ((N : ℝ) * β)) ∧
      (∀ N, S.coeff N = critCoeff d a β ρ) ∧
      (∀ N, S.dyn N = quadraticGradientDyn d ((d : ℝ) / 2) a β) ∧
      (∀ N, OscAdjointInput (S.coeff N) m H) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : (0 : ℝ) < (d : ℝ) / 2 := by linarith
  have hsd : (d : ℝ) / 2 < d := by linarith
  obtain ⟨θ, Λ, K, hθ, hvalid, C₀thr, hthr0, hSetup⟩ :=
    HRS.MS.S21.s21_setup_family hd hs0.le hsd ha hβ hH hρ
  obtain ⟨S, h1, h2, h3, -⟩ := hSetup C₀thr le_rfl
  have hbv : (s81s_bounds d a β m H θ Λ K C₀thr).Valid := by
    refine
      { hd := hvalid.hd, hs0 := hvalid.hs0, hsd := hvalid.hsd, hT := hvalid.hT, hQ := hvalid.hQ,
        hθ := hvalid.hθ, hk := hvalid.hk, hm := lt_of_lt_of_le hvalid.hm hm, hL := hvalid.hL,
        hν := hvalid.hν }
  let S' : WholeSetup (s81s_bounds d a β m H θ Λ K C₀thr) :=
    ⟨S.invβ, S.ρ, S.κ, S.hinvβ, S.hκ, S.mf, S.dens, S.adjoint, S.regime, S.force, S.energy_nonneg⟩
  have hcoeff : ∀ N, S'.coeff N = critCoeff d a β ρ := by
    intro N
    have e := HRS.MS.S21.s21_coeff_setup S h1 h2 N
    show S.coeff N = _
    rw [e, ← HRS.MS.S21.s21_dyn_eq]
    rfl
  have hQ : (a • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm := by
    unfold Matrix.IsSymm; simp
  have hρeq : ρ = thermalDensity d ((d : ℝ) / 2) a β := HRS.MS.Mov0.mv0_rho_eq hd hs0.le hsd ha hβ hρ
  have hSch : IsSchwartzDensity ρ := by
    rw [hρeq]; exact HRS.MS.S21.s21_schwartz_thermal hd hs0.le hsd ha hβ
  refine ⟨θ, Λ, K, C₀thr, S', hbv, h1, h2, h3, hcoeff, ?_, ?_⟩
  · intro N
    show S.dyn N = _
    rw [HRS.MS.S21.s21_dyn_eq]
    unfold WholeSetup.dyn
    rw [h2 N]
    rfl
  · intro N
    rw [hcoeff N, critCoeff, HRS.MS.S21.s21_dyn_eq, HRS.MS.S85.s85_coeff_fv (a • (1 : Matrix (Fin d) (Fin d) ℝ)) hQ ρ]
    have hm' : (24 : ℝ) * d + 240 ≤ m := by
      have : ((wholeSpaceIndex d : ℕ) : ℝ) = 24 * d + 240 := by
        unfold wholeSpaceIndex; push_cast; ring
      linarith
    exact HRS.MS.S21.s21_oscAdjointInput hd hs0.le hsd (inv_pos.2 hβ) (a • (1 : Matrix (Fin d) (Fin d) ℝ))
      hQ hSch H hH.le m hm'

end HRS.Whole.S81S
