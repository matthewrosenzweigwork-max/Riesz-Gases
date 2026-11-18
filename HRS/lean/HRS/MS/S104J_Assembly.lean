import HRS.MS.S104gTermReg
import HRS.MS.S105rTie
import HRS.MS.S21B2_Wrap
import HRS.MS.S105rReg1

/-!
# S10.4 packet S104J: final assembly from the adjoint-existence hypothesis `hex`

Namespace `HRS.MS.S104j`.

* `S104jHex d s a β ρβ ε_* c₁ C₁`: the adjoint-existence hypothesis of `s104g_termRegGen_of_ex` (classical adjoint solutions with terminal datum `φ_α`, `α` arbitrary, at
  every terminal time `t ≥ 0`, for every admissible perturbation and resulting solution of the class).  `S104jHexSmall`: it holds for small `ε_*`, along every thermal equilibrium
  (supplied unconditionally by `s104e_hexSmall` in S104eFinal, from `s104e_hex`).
* `s104j_termRegGen_mono`: `S104bTermRegGen` at `ε₂` implies it at every `ε₁ ≤ ε₂` (the class for `ε₁` is contained in the class for `ε₂`, since `C₁ > 0`).
* `s104j_termReg : S105rTermReg` from `S104jHexSmall` (S104G: `s104g_termRegGen_of_ex`).
* Final theorems, all conditional only on `S104jHexSmall`: `s104j_general_initial`, `s104j_errors` (S10.5), `s104j_whole_space_prepared` (S2.1(ii)), `s104j_mov_translated_prepared` (S6.11).
  These four hypotheses are discharged with no remaining hypothesis by the `s104e_final_*` theorems of S104eFinal (via `s104e_hexSmall`); the statements here are unchanged.
  The frozen statements are the ED14 forms `∀ c₁ C₁, ∃ ε_*`; the existential `ε_*` is chosen inside the ties as the minimum of the orbit-claim radius and the
  `εn` of `S105rTermReg` (as `s103d_tie` does), so smallness of `ε_*` is legitimate.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

namespace HRS.MS.S104j

open HRS HRS.Whole HRS.MS.R2WinErr HRS.MS.R2WinOrbNL HRS.MS.S105r

variable {d : ℕ}

/-- Existence of classical adjoint solutions with datum `φ_α` along the class (the hypothesis of `s104g_termRegGen_of_ex`). -/
def S104jHex (d : ℕ) (s a β : ℝ) (ρβ : Euc d → ℝ) (εstar c₁ C₁ : ℝ) : Prop :=
  ∀ (ε : ℝ) (ψ : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ), IsAdmissiblePerturbation ρβ εstar ε ψ →
    IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ → ∀ α : MultiIndex d, ∀ t : ℝ, 0 ≤ t →
      ∃ f : ℝ → Euc d → ℝ, IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) t
        (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α) f

/-- The existence hypothesis for small `ε_*`. -/
def S104jHexSmall : Prop :=
  ∀ {d : ℕ}, 2 ≤ d → ∀ (s a β c₁ C₁ : ℝ), 0 ≤ s → s < d → 0 < a → 0 < β → ∃ εn : ℝ, 0 < εn ∧
    ∀ εstar : ℝ, 0 < εstar → εstar ≤ εn → ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ →
      S104jHex d s a β ρβ εstar c₁ C₁

theorem s104j_res_mono {s a β : ℝ} {ρβ : Euc d → ℝ} (hρβ : IsThermalEquilibrium d s a β ρβ) {e1 e2 ε c₁ C₁ : ℝ}
    {ψ : Euc d → ℝ} {ρ : ℝ → Euc d → ℝ} (hres : IsResultingSolution d s a β ρβ e1 ε ψ c₁ C₁ ρ) (he : e1 ≤ e2) :
    IsResultingSolution d s a β ρβ e2 ε ψ c₁ C₁ ρ := by
  have hC : 0 < C₁ := s105r_C1_pos hρβ hres
  have hm : ∀ t : ℝ, C₁ * e1 * Real.exp (-c₁ * t) ≤ C₁ * e2 * Real.exp (-c₁ * t) := fun t =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hC.le) (Real.exp_pos _).le
  exact { hres with
    weighted := fun t ht => ⟨(hres.weighted t ht).1, (hres.weighted t ht).2.trans (hm t)⟩
    velocity := fun t ht => (hres.velocity t ht).trans (ENNReal.ofReal_le_ofReal (hm t)) }

theorem s104j_termRegGen_mono {s a β : ℝ} {ρβ : Euc d → ℝ} (hρβ : IsThermalEquilibrium d s a β ρβ) {e1 e2 c₁ C₁ : ℝ}
    (he : e1 ≤ e2) (h : S104bTermRegGen d s a β ρβ e2 c₁ C₁) : S104bTermRegGen d s a β ρβ e1 c₁ C₁ :=
  fun ε ψ ρ hψ hres α T0 hT0 =>
    h ε ψ ρ { hψ with small := hψ.small.trans he } (s104j_res_mono hρβ hres he) α T0 hT0

/-- `S105rTermReg` (`S104bTermRegGen` for small `ε_*`) from the adjoint-existence hypothesis for small `ε_*`. -/
theorem s104j_termReg (hex : S104jHexSmall) : S105rTermReg := by
  intro d hd s a β c₁ C₁ hs0 hsd ha hβ
  obtain ⟨εe, hεe, hE⟩ := hex hd s a β c₁ C₁ hs0 hsd ha hβ
  by_cases hρ : ∃ ρ0 : Euc d → ℝ, IsThermalEquilibrium d s a β ρ0
  swap
  · exact ⟨1, one_pos, fun εstar _ ρβ hρβ => absurd ⟨ρβ, hρβ⟩ hρ⟩
  obtain ⟨ρ0, hρ0⟩ := hρ
  obtain ⟨ε₁, hε₁, hT⟩ := s104g_termRegGen_of_ex hd hs0 hsd ha hβ hρ0 c₁ C₁
  have hpos : 0 < min ε₁ εe := lt_min hε₁ hεe
  refine ⟨min ε₁ εe, hpos, fun εstar hle ρβ hρβ => ?_⟩
  have huniq : ρβ = ρ0 := by
    rw [HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρβ, HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ0]
  subst huniq
  refine s104j_termRegGen_mono hρβ hle (hT (min ε₁ εe) hpos (min_le_left _ _) ?_)
  exact hE (min ε₁ εe) hpos (min_le_right _ _) ρβ hρβ

/-- `r2_window_general_initial` (S10.5, nonlinear, general initial time), conditional only on the adjoint existence `hex`; discharged by `s104e_final_general_initial` (S104eFinal). -/
theorem s104j_general_initial (hex : S104jHexSmall) : type_of% @HRS.Whole.r2_window_general_initial :=
  s105r_general_initial_of_orbits HRS.MS.R2WinOrbNL.s103d_r2_window_orbits_proof (s104j_termReg hex)

/-- `r2_window_errors` (S10.4), conditional only on the adjoint existence `hex`; discharged by `s104e_final_errors` (S104eFinal). -/
theorem s104j_errors (hex : S104jHexSmall) : type_of% @HRS.Whole.r2_window_errors :=
  s105r_errors_of_orbits HRS.MS.R2WinOrbNL.s103d_r2_window_orbits_proof (s104j_termReg hex)

/-- **S2.1 (ii)** (`whole_space_prepared`), conditional only on the adjoint existence `hex`; discharged by `s104e_final_whole_space_prepared` (S104eFinal). -/
theorem s104j_whole_space_prepared (hex : S104jHexSmall) : HRS.Whole.WholeSpacePreparedStatement :=
  HRS.MS.S21B2.s21b2_whole_space_prepared_of_termReg (s104j_termReg hex)

/-- **S6.11 prepared form** (`mov_translated_prepared`), conditional only on the adjoint existence `hex`; discharged by `s104e_final_mov_translated_prepared` (S104eFinal). -/
theorem s104j_mov_translated_prepared (hex : S104jHexSmall) : type_of% @HRS.Whole.mov_translated_prepared :=
  HRS.MS.S21B2.s21b2_mov_translated_prepared_of_termReg (s104j_termReg hex)

end HRS.MS.S104j

end
