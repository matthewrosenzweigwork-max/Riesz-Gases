import HRS.MS.R2WinOrbNLAux17

/-!
# S10.3 (nonlinear branch), part 18: the orbit bound for a datum with bounded jets

Prefix `s103n_`, namespace `HRS.MS.R2WinOrbNL`.  `s103n_orbitSup_of_bd`: along a trajectory with the gradient estimate and the zeroth-order bound, every terminal datum
`g ∈ Bd (8d+80) A` satisfies `R2OrbitSup … (C A)` (the jets give `‖∇g‖_{C_b^{4d+42}}`, `‖g‖_∞` and, by `s103n_psi_of_jets`, `‖√ρ_β Πg‖_{Σ^{8d+80}}`; then
`s103n_orbit_of_data`).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole HRS.MS.Ul HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.Mov63 HRS.MS.Who HRS.MS.BreakdownS67
  HRS.MS.MovAdj HRS.MS.R2WinOrb

variable {d : ℕ}

theorem s103n_orbitSup_of_bd {s a β : ℝ} {ρβ : Euc d → ℝ} (H : Mov2dTh d s β a ρβ) {Cg cg Cz : ℝ}
    (hCg : 0 ≤ Cg) (hcg : 0 < cg) (hCz : 0 ≤ Cz) :
    ∃ C5 : ℝ, 0 ≤ C5 ∧ ∀ (ρ : ℝ → Euc d → ℝ), S103nGrad d s a β ρβ ρ Cg cg → S103nZero d s a β ρβ ρ Cz →
      ∀ (g : Euc d → ℝ) (A : ℝ), Bd (8 * d + 80) A g → ∀ t : ℝ, 0 ≤ t →
        R2OrbitSup ((quadraticGradientDyn d s a β).coeff ρ) (4 * d + 42) t g (C5 * A) := by
  obtain ⟨Cψ, hCψ0, hCψ⟩ := s103n_psi_of_jets H (8 * d + 80)
  refine ⟨((1 + 2 * Cz) + 2 * Cg) * (((4 * d + 42 : ℕ) + 1 : ℝ) + 1 + Cψ), by positivity,
    fun ρ hG hZ g A hg t ht => ?_⟩
  have hA := hg.nonneg
  have hgk : ContDiff ℝ ((4 * d + 42 + 1 : ℕ) : WithTop ℕ∞) g :=
    hg.1.of_le (by exact_mod_cast (by omega : 4 * d + 42 + 1 ≤ 8 * d + 80))
  have hcb := s103n_cb_of_jets (n := 4 * d + 42) hgk (E := A) (fun l hl x => hg.2 l (by omega) x)
  obtain ⟨hm1, hm2⟩ := hCψ A g hg
  set B : ℝ := (((4 * d + 42 : ℕ) + 1 : ℝ) + 1 + Cψ) * A with hB
  have hB0 : 0 ≤ B := by positivity
  have h1 : (((4 * d + 42 : ℕ) + 1 : ℝ)) * A ≤ B := by nlinarith [mul_nonneg hCψ0 hA]
  have h2 : A ≤ B := by
    have : (0 : ℝ) ≤ ((4 * d + 42 : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg hCψ0 hA, mul_nonneg this hA]
  have h3 : Cψ * A ≤ B := by
    have : (0 : ℝ) ≤ ((4 * d + 42 : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg hCψ0 hA, mul_nonneg this hA]
  obtain ⟨-, hsup⟩ := s103n_orbit_of_data hCg hcg hCz hG hZ g B hB0 hgk
    (hcb.trans (ENNReal.ofReal_le_ofReal h1))
    (fun x => by
      have := hg.2 0 (Nat.zero_le _) x
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
      exact this.trans h2)
    hm1 (hm2.trans h3) t ht
  refine s103_orbitSup_mono hsup (le_of_eq ?_)
  rw [hB]; ring

end HRS.MS.R2WinOrbNL

end
