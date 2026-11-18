import HRS.MS.R2WinErrAux18
import HRS.MS.R2WinOrbAux9
import HRS.MS.R2ObsAux1
import HRS.MS.FldRemAux2

/-!
# S10.4 (stationary branch): the terminal-time orbit family `τ ↦ U(0,τ)L^aφ_α` in the form needed for the evolution identity

`s104_stat_orbit` (from `s103_family`): for the stationary coefficient of a thermal equilibrium there are `G0 G1 G2` with
`G0 τ = propagatorW C 0 τ φ_α`, `G1 τ = propagatorW C 0 τ (Lφ_α)`, `C_b^2` bounds, the `S53Diff` difference-quotient property `G0 → G1 → G2`,
and classical adjoint solutions for both terminal data at every time.  `s104_prop_shift`: `U(r,t) = U(0,t-r)` (time homogeneity + uniqueness).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2WinErr

open HRS HRS.Whole HRS.MS.S53

variable {d : ℕ}

/-- The terminal-time orbit data of the stationary coefficient (see the module docstring). -/
structure S104StatOrbit (C : WholeCoeff d) (φ : Euc d → ℝ) (T0 : ℝ) (G0 G1 G2 : ℝ → Euc d → ℝ) : Prop where
  eq0 : ∀ τ ∈ Icc (0 : ℝ) T0, G0 τ = propagatorW C 0 τ φ
  eq1 : ∀ τ ∈ Icc (0 : ℝ) T0, G1 τ = propagatorW C 0 τ (generatorW C 0 φ)
  cb0 : ∀ τ ∈ Icc (0 : ℝ) T0, MemCb 2 (G0 τ)
  cb1 : ∀ τ ∈ Icc (0 : ℝ) T0, MemCb 2 (G1 τ)
  cb2 : ∀ τ ∈ Icc (0 : ℝ) T0, MemCb 2 (G2 τ)
  diff01 : S53Diff T0 G0 G1
  diff12 : S53Diff T0 G1 G2
  ex0 : ∀ τ ∈ Icc (0 : ℝ) T0, ∃ f, IsClassicalAdjointW C τ φ f
  ex1 : ∀ τ ∈ Icc (0 : ℝ) T0, ∃ f, IsClassicalAdjointW C τ (generatorW C 0 φ) f

lemma s104_memCb_of_classical {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {u : ℝ → Euc d → ℝ}
    (hu : IsClassicalAdjointW C t φ u) (ht : 0 ≤ t) : MemCb 2 (u 0) := by
  refine ⟨hu.c2 0 ⟨le_rfl, ht⟩, fun j hj => ?_⟩
  obtain ⟨B, hB⟩ := hu.bdd j hj
  exact ⟨B, by rintro _ ⟨x, rfl⟩; exact hB 0 ⟨le_rfl, ht⟩ x⟩

theorem s104_stat_orbit (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    {ρβ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρβ) (α : MultiIndex d) {T0 : ℝ} (hT0 : 0 ≤ T0) :
    ∃ G0 G1 G2 : ℝ → Euc d → ℝ, S104StatOrbit ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ))
      (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α) T0 G0 G1 G2 := by
  obtain ⟨F, hF0, hF1, hF2⟩ := HRS.MS.R2WinOrb.s103_family hd hs0 hsd ha hβ hρ α hT0
  set C := (quadraticGradientDyn d s a β).coeff (fun _ => ρβ) with hC
  have hk : 2 ≤ 4 * d + 42 := by omega
  have hex : ∀ (b : Fin 4) (t : ℝ), t ∈ Icc (0 : ℝ) T0 → ∃ u, IsClassicalAdjointW C t
      ((fun g x => generatorW C 0 g x)^[(b : ℕ)] (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α)) u ∧ F b t = u 0 :=
    hF1
  have hcb : ∀ (b : Fin 4) (t : ℝ), t ∈ Icc (0 : ℝ) T0 → MemCb 2 (F b t) := by
    intro b t ht
    obtain ⟨u, hu, hFu⟩ := hex b t ht
    rw [hFu]; exact s104_memCb_of_classical hu ht.1
  have hUniq := HRS.MS.TransOp.s611_uniq_of_thermal hd hs0 hsd ha hβ hρ T0
  refine ⟨F 0, F 1, F 2, ⟨hF0, ?_, hcb 0, hcb 1, hcb 2, ?_, ?_, ?_, ?_⟩⟩
  · intro τ hτ
    obtain ⟨u, hu, hFu⟩ := hex 1 τ hτ
    have := hUniq τ hτ _ u hu 0 ⟨le_rfl, hτ.1⟩
    rw [hFu, ← this]; rfl
  · intro τ hτ ε hε
    obtain ⟨δ, hδ, h⟩ := hF2 0 (by decide) τ hτ ε hε
    exact ⟨δ, hδ, fun h' hne hlt hmem j hj x => h h' hne hlt hmem j (hj.trans hk) x⟩
  · intro τ hτ ε hε
    obtain ⟨δ, hδ, h⟩ := hF2 1 (by decide) τ hτ ε hε
    exact ⟨δ, hδ, fun h' hne hlt hmem j hj x => h h' hne hlt hmem j (hj.trans hk) x⟩
  · intro τ hτ
    obtain ⟨u, hu, -⟩ := hex 0 τ hτ
    exact ⟨u, hu⟩
  · intro τ hτ
    obtain ⟨u, hu, -⟩ := hex 1 τ hτ
    exact ⟨u, hu⟩

/-- Time homogeneity: `U(r,t)ψ = U(0,t-r)ψ` for the stationary coefficient, when a classical adjoint solution exists. -/
theorem s104_prop_shift (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    {ρβ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρβ) {t r : ℝ} (hr : r ∈ Icc (0 : ℝ) t)
    {ψ : Euc d → ℝ}
    (hex : ∃ f, IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ)) t ψ f) :
    propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ)) r t ψ =
      propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ)) 0 (t - r) ψ := by
  obtain ⟨f, hf⟩ := hex
  have hU1 := HRS.MS.TransOp.s611_uniq_of_thermal hd hs0 hsd ha hβ hρ t t ⟨hr.1.trans hr.2, le_rfl⟩ ψ f hf r hr
  have hsh := HRS.MS.R2Obs.s910_shift (quadraticGradientDyn d s a β) ρβ (t := t - r) (T := t)
    (by linarith [hr.2]) (by linarith [hr.1]) hf
  have hU2 := HRS.MS.TransOp.s611_uniq_of_thermal hd hs0 hsd ha hβ hρ (t - r) (t - r)
    ⟨by linarith [hr.2], le_rfl⟩ ψ _ hsh 0 ⟨le_rfl, by linarith [hr.2]⟩
  rw [hU1, hU2]
  simp only [zero_add]
  congr 1
  ring

end HRS.MS.R2WinErr
