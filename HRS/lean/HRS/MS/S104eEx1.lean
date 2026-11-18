import HRS.MS.S104eCoeff2
import HRS.MS.R2WinOrbTRD11

/-!
# S10.4 (nonlinear), packet S104E-5: Gaussian bounds of the density path, `U2Dec`, and the terminal time `t = 0` of the existence clause

`S104eHex`: the existence interface (level-0 data `φ_α`, every terminal time `t ≥ 0`): classical adjoint solutions along the nonlinear coefficient.
(The data `L_tφ_α`, `L_t²φ_α + ∂_tL_tφ_α` of `S104bTermRegGen.ex` are obtained from level 0 by the layered step `s103c_step`, as in `s103d_core`.)
`s104e_gauss_rho`: Gaussian derivative bounds of `ρ^t` up to any order `n ≤ 100d + 1000`, uniformly in `t ≥ 0`.
`s104e_u2dec_of_gauss`: Gaussian bounds give `U2Dec K L` for every polynomial weight `L`.
`s104e_hex_zero`: the case `t = 0` of `S104eHex` (`f ≡ φ_α`; `generatorW` at time `0` is `DatD`, by `s103c_g1_datd`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S104e

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.S104b HRS.MS.Mov63 HRS.MS.S105r HRS.MS.R2WinOrbNL

variable {d : ℕ}

/-- The existence interface of `S104bTermRegGen.ex` at level 0 (Hermite data), for all terminal times `t ≥ 0`. -/
def S104eHex (d : ℕ) (s a β : ℝ) (ρβ : Euc d → ℝ) (εstar c₁ C₁ : ℝ) : Prop :=
  ∀ (ε : ℝ) (ψ : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ),
    IsAdmissiblePerturbation ρβ εstar ε ψ → IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ →
    ∀ (α : MultiIndex d) (t : ℝ), 0 ≤ t → ∃ f : ℝ → Euc d → ℝ,
      IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) t
        (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α) f

theorem s104e_gauss_rho (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    (εstar c₁ C₁ : ℝ) (n : ℕ) (hn : n ≤ 100 * d + 1000) {ρβ : Euc d → ℝ}
    (hρβ : IsThermalEquilibrium d s a β ρβ) {ε : ℝ} {ψ : Euc d → ℝ} {ρ : ℝ → Euc d → ℝ}
    (hres : IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ) :
    ∃ c K : ℝ, 0 < c ∧ 0 ≤ K ∧ ∀ t : ℝ, 0 ≤ t → ContDiff ℝ (n : WithTop ℕ∞) (ρ t) ∧
      ∀ k ≤ n, ∀ x : Euc d, ‖iteratedFDeriv ℝ k (ρ t) x‖ ≤ K * Real.exp (-c * ‖x‖ ^ 2) := by
  obtain ⟨B, hBdef, hR, -⟩ := HRS.MS.Mov0.mv0_gapref hd hs0 hsd ha hβ hρβ
  have hq : 0 < β * a := mul_pos hβ ha
  have hpos : ∀ x, 0 < ρβ x := hR.pos
  have hρβc : Continuous ρβ := hR.smooth.continuous
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = 102 * d + 1020 := ⟨_, rfl⟩
  have hmR : (m : ℝ) = 102 * (d : ℝ) + 1020 := by rw [hm]; push_cast; ring
  have hm1 : (d : ℝ) / 2 + (n : ℝ) + 2 < m := by
    rw [hmR]
    have h1 : (n : ℝ) ≤ 100 * (d : ℝ) + 1000 := by exact_mod_cast hn
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨Cv, hCv0, hCv⟩ := mn_force_bound hd hs0 hsd β a hβ ha ρβ hρβ n m hm1
  set E : ℝ := |C₁| * |εstar| with hEdef
  have hE0 : 0 ≤ E := by positivity
  obtain ⟨c, K, hc, hK0, hKb⟩ := s104e_leibniz hq hR n Cv E hCv0 hE0
  refine ⟨c, K, hc, hK0, fun t ht => ?_⟩
  have hdec : ρ t = fun x => ρβ x + Real.sqrt (ρβ x) * ((ρ t x - ρβ x) / Real.sqrt (ρβ x)) := by
    funext x
    have hsq : 0 < Real.sqrt (ρβ x) := Real.sqrt_pos.2 (hpos x)
    field_simp
    ring
  have hvc : Continuous (fun x => (ρ t x - ρβ x) / Real.sqrt (ρβ x)) :=
    ((hres.regular t ht).sub hρβc).div hρβc.sqrt (fun x => (Real.sqrt_pos.2 (hpos x)).ne')
  have hvm : MemOsc (m : ℝ) (fun x => (ρ t x - ρβ x) / Real.sqrt (ρβ x)) := by
    rw [hmR]; exact (hres.weighted t ht).1
  have hvn : oscNorm (m : ℝ) (fun x => (ρ t x - ρβ x) / Real.sqrt (ρβ x)) ≤ E := by
    rw [hmR]
    refine ((hres.weighted t ht).2).trans ?_
    have h1 : Real.exp (-c₁ * t) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := hres.cpos
      nlinarith
    have h2 : 0 ≤ Real.exp (-c₁ * t) := (Real.exp_pos _).le
    calc C₁ * εstar * Real.exp (-c₁ * t) ≤ |C₁ * εstar| * Real.exp (-c₁ * t) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) h2
      _ ≤ |C₁ * εstar| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = E := by rw [mul_one, abs_mul]
  obtain ⟨hvn2, hvb, -⟩ := hCv _ hvc hvm
  have hv' : ContDiff ℝ (n : WithTop ℕ∞) (fun x => (ρ t x - ρβ x) / Real.sqrt (ρβ x)) :=
    hvn2.of_le (by exact_mod_cast (by omega : n ≤ n + 2))
  have hvb' : ∀ k ≤ n, ∀ x : Euc d, ‖iteratedFDeriv ℝ k (fun x => (ρ t x - ρβ x) / Real.sqrt (ρβ x)) x‖ ≤
      Cv * E := fun k hk x => (hvb k (by omega) x).trans (mul_le_mul_of_nonneg_left hvn hCv0)
  obtain ⟨hcd, hKb'⟩ := hKb _ hv' hvb'
  rw [← hdec] at hcd hKb'
  exact ⟨hcd, hKb'⟩

theorem s104e_u2dec_of_gauss {c : ℝ} (hc : 0 < c) (K n : ℕ) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ (f : Euc d → ℝ) (A : ℝ), 0 ≤ A → ContDiff ℝ (K : WithTop ℕ∞) f →
      (∀ k ≤ K, ∀ x : Euc d, ‖iteratedFDeriv ℝ k f x‖ ≤ A * Real.exp (-c * ‖x‖ ^ 2)) →
      U2Dec K (n : ℝ) (P * A) f := by
  obtain ⟨P, hP0, hP⟩ := HRS.MS.Thm.rege_poly_gauss_bdd hc n
  refine ⟨P, hP0.le, fun f A hA hf hb => ⟨hf, fun m hm y => ?_⟩⟩
  have h1 := hb m hm y
  have h2 := hP ‖y‖ (norm_nonneg _)
  have hpos : 0 < (1 + ‖y‖) ^ n := by positivity
  have h3 : Real.exp (-c * ‖y‖ ^ 2) ≤ P * ((1 + ‖y‖) ^ n)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hpos]; linarith
  have e : u2Wt (n : ℝ) y = ((1 + ‖y‖) ^ n)⁻¹ := by
    unfold u2Wt
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  rw [e]
  calc ‖iteratedFDeriv ℝ m f y‖ ≤ A * Real.exp (-c * ‖y‖ ^ 2) := h1
    _ ≤ A * (P * ((1 + ‖y‖) ^ n)⁻¹) := mul_le_mul_of_nonneg_left h3 hA
    _ = P * A * ((1 + ‖y‖) ^ n)⁻¹ := by ring

end HRS.MS.S104e
