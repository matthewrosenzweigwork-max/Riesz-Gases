import HRS.MS.S111X2Aux36
import HRS.MS.S111X2Aux25
import HRS.MS.FeatDecAux12
import HRS.MS.S111X1G2

/-!
# S11.1 X2, packet H01 (part 5): the Hermite sums

`s111x2_H01`: for the thermal reference and the dual Hermite tests `φ_α = λ_α^{-m/2} h_α`, `m = 24d+240`, put
`U_τ = propagatorW C 0 τ`, `κ = λ/β`.  There is `B` such that for all finite sets `S` of multi-indices and
`0 ≤ τ₁ ≤ τ₂`:
`∑_{α∈S} ‖P_μ U_{τ₁} φ_α‖² ≤ B e^{-2κτ₁}` and `∑_{α∈S} ‖P_μ(U_{τ₂}φ_α - U_{τ₁}φ_α)‖² ≤ B (τ₂-τ₁)² e^{-2κτ₁}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X2

open HRS (Euc)
open HRS.Whole HRS.Whole.Q34

variable {d : ℕ}

/-- Existence of the classical solutions for `φ_α` and `Gφ_α` on every horizon. -/
theorem s111x2_exist_osc (hd : 2 ≤ d) {s a β : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a) (hβ : 0 < β)
    {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) (α : MultiIndex d) {H : ℝ} (hH : 0 ≤ H) :
    (∃ f, IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) H
      (oscTestFun (wholeSpaceIndex d : ℝ) α) f) ∧
    ∃ h, IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) H
      (generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 (oscTestFun (wholeSpaceIndex d : ℝ) α)) h := by
  have hdr : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by linarith
  have hρeq : ρ = thermalDensity d s a β := HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ
  have hSch : IsSchwartzDensity ρ := by
    rw [hρeq]; exact HRS.MS.S21.s21_schwartz_thermal hd hs0 hsd ha hβ
  have hQ : (a • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm := by unfold Matrix.IsSymm; simp
  have hex := HRS.MS.S85.s85_exists_adjoint hd hs0 hsd (inv_pos.2 hβ) (a • (1 : Matrix (Fin d) (Fin d) ℝ)) hQ hSch
    H hH (wholeSpaceIndex d : ℝ) α H ⟨hH, le_rfl⟩
  have hco : (quadraticGradientDyn d s a β).coeff (fun _ => ρ) =
      (⟨s, -1, quadV (a • (1 : Matrix (Fin d) (Fin d) ℝ)) 0, β⁻¹⟩ : WholeDyn d).coeff (fun _ => ρ) :=
    HRS.MS.S111X1.x1C_eq d s a β ρ
  obtain ⟨M, T⟩ := s111x2_td_of_thermal hd hs0 hs ha hβ hρ
  obtain ⟨hf, hh⟩ := hex
  refine ⟨?_, ?_⟩
  · rw [hco]; exact hf
  · obtain ⟨h, hh⟩ := hh
    refine ⟨h, ?_⟩
    rw [hco]
    have hcb := (S45.s45_cb_oscTest (d := d) (by omega) 2 (wholeSpaceIndex d : ℝ)).choose_spec.2 α
    obtain ⟨-, hC⟩ := s111x2_cbNorm_bounds hcb.1
    have := s111x2_gen_auto T hC H
    rw [← hco] at hh ⊢
    rw [← this]
    exact hh

/-- The propagator is the orbit of the classical solution. -/
theorem s111x2_prop_orbit (hd : 2 ≤ d) {s a β : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a) (hβ : 0 < β)
    {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) {H : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) H φ f)
    {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) H) :
    propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 τ φ = f (H - τ) := by
  obtain ⟨M, T⟩ := s111x2_td_of_thermal hd hs0 hs ha hβ hρ
  have hsh : IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) (( H - τ) + τ) φ f := by
    rw [sub_add_cancel]; exact hf
  have hg := s111x2_cls_shift T (u := H - τ) (t := τ) (by linarith [hτ.2]) hτ.1 hsh
  rw [s111x2_prop_eq hd hs0 hs ha hβ hρ hτ.1 hg ⟨le_rfl, hτ.1⟩]
  simp only [zero_add]

end HRS.MS.S111X2
