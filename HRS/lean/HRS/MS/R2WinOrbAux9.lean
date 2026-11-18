import HRS.MS.R2WinOrbAux8
import HRS.MS.UlTie2
import HRS.MS.OrbFeatAux1
import HRS.MS.TransOpAux23

/-!
# S10.3 (stationary half), part 9: the orbit family `t ↦ U(0,t) L^a φ_α` and its terminal-time derivatives

Prefix `s103_`, namespace `HRS.MS.R2WinOrb`.  `s103_family`: for the stationary coefficient and a horizon `T0`, there is a family `F a t`
(`a ≤ 3`, `t ∈ [0,T0]`) of values `u 0` of classical adjoint solutions `u` with terminal datum `L^a φ_α` at time `t`, such that the difference quotients
`h⁻¹ (F a (t+h) - F a t) → F (a+1) t` in every `C^j` sup norm, `j ≤ 4d+42` (`ul_adjoint_orbit_bounds_proof`), and `F 0 t = propagatorW Cf 0 t φ_α`
(uniqueness of classical adjoint solutions, `s611_uniq_of_thermal`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2WinOrb

open HRS HRS.Whole HRS.MS.MovAdj HRS.MS.Ul HRS.MS.MovOsc

variable {d : ℕ}

theorem s103_rho_schwartz {s q β : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hq : 0 < q) (hβ : 0 < β)
    {ρβ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s q β ρβ) : IsSchwartzDensity ρβ := by
  obtain ⟨B0, -, hR, -⟩ := HRS.MS.Mov0.mv0_gapref hd hs0 hsd hq hβ hρ
  have hq' : 0 < β * q := mul_pos hβ hq
  obtain ⟨hρsm, cρ, hcρ, hkρ⟩ := HRS.MS.Mov0.mv0_hgauss_gapref hq' hR
  obtain ⟨ψρ, hψρ⟩ := HRS.MS.MovC1.movc1_G_schwartz (⟨hρsm, cρ, hcρ, hkρ⟩ : HRS.MS.MovC1.MovcG ρβ)
  exact ⟨hρ.2.1, ψρ, hψρ⟩

theorem s103_family {s q β : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hq : 0 < q) (hβ : 0 < β)
    {ρβ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s q β ρβ) (α : MultiIndex d) {T0 : ℝ} (hT0 : 0 ≤ T0) :
    ∃ F : Fin 4 → ℝ → Euc d → ℝ,
      (∀ t ∈ Icc (0 : ℝ) T0, F 0 t = propagatorW ((quadraticGradientDyn d s q β).coeff (fun _ => ρβ)) 0 t
          (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α)) ∧
      (∀ a : Fin 4, ∀ t ∈ Icc (0 : ℝ) T0, ∃ u, IsClassicalAdjointW
          ((quadraticGradientDyn d s q β).coeff (fun _ => ρβ)) t
          ((fun g x => generatorW ((quadraticGradientDyn d s q β).coeff (fun _ => ρβ)) 0 g x)^[(a : ℕ)]
            (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α)) u ∧ F a t = u 0) ∧
      (∀ a : Fin 4, ∀ ha : (a : ℕ) < 3, ∀ t ∈ Icc (0 : ℝ) T0, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ h : ℝ, h ≠ 0 → |h| < δ → t + h ∈ Icc (0 : ℝ) T0 → ∀ j ≤ 4 * d + 42, ∀ x : Euc d,
          ‖iteratedFDeriv ℝ j (fun y => h⁻¹ * (F a (t + h) y - F a t y) - F ⟨(a : ℕ) + 1, by omega⟩ t y) x‖ ≤ ε) := by
  have hρS := s103_rho_schwartz hd hs0 hsd hq hβ hρ
  have hσ : ∀ i, ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = fun x => (fun _ : Euc d => (0 : Euc d)) x i :=
    fun i => ⟨0, by ext x; simp⟩
  obtain ⟨θ, hθ⟩ := HRS.MS.S52B.s52b_exists_ulCutoff d
  obtain ⟨k₀, J, H⟩ := ul_adjoint_orbit_bounds_proof hd s hs0 hsd θ hθ (4 * d + 42)
  have hk₁ : ((4 * d + 42 : ℕ) : ℝ) + (d : ℝ) / 2 < ((k₀ + (4 * d + 42) + d + 2 : ℕ) : ℝ) := by
    push_cast
    have : (0 : ℝ) ≤ k₀ := Nat.cast_nonneg k₀
    have : (d : ℝ) / 2 ≤ d := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
    push_cast
    linarith
  obtain ⟨C, hC⟩ := H (k₀ + (4 * d + 42) + d + 2) (by omega) hk₁ T0 β⁻¹
    ((q : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ)) ρβ
    (fun x => (fun _ : Euc d => (0 : Euc d)) x - convGradConvW (rieszKernelGrad d s) ρβ x) hT0
    (inv_pos.2 hβ) hρS ⟨fun _ => 0, hσ, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : SchwartzMap (Euc d) ℝ, ⇑f = oscTestFun ((24 * d + 240 : ℕ) : ℝ) α := by
    have hmem : oscTestFun ((24 * d + 240 : ℕ) : ℝ) α ∈ mo_Hspan d := by
      have : oscTestFun ((24 * d + 240 : ℕ) : ℝ) α =
          (oscEigenvalue d α ^ (-(((24 * d + 240 : ℕ) : ℝ) / 2))) • hermiteFunD α := by
        funext x; simp [oscTestFun]
      rw [this]
      exact Submodule.smul_mem _ _ (mova3_hermite_mem α)
    exact mova3c_hspan_schwartz hmem
  obtain ⟨⟨F, hF⟩, hF2⟩ := hC f
  obtain ⟨-, hderiv⟩ := hF2 F hF
  have hCfeq := s103_coeff_eq s q β ρβ
  refine ⟨F, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨u, hu, hFu⟩ := hF 0 t ht
    have hu' : IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff (fun _ => ρβ)) t
        (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α) u := by
      rw [hCfeq, ← hf]; exact hu.classicalSol
    have := HRS.MS.TransOp.s611_uniq_of_thermal hd hs0 hsd hq hβ hρ T0 t ht _ u hu' 0 ⟨le_rfl, ht.1⟩
    rw [hFu, this]
  · intro a t ht
    obtain ⟨u, hu, hFu⟩ := hF a t ht
    refine ⟨u, ?_, hFu⟩
    rw [hCfeq, ← hf]
    exact hu.classicalSol
  · intro a ha t ht ε hε
    exact hderiv a ha t ht ε hε

end HRS.MS.R2WinOrb

end
