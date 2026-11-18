/-
# HRS.Equilibrium.Q84bAuxI — packet Q84b: `μ[Jop ψ(·,b)] = -∫ F·∇_xψ(x,b) μ(dx)`
-/
import HRS.Equilibrium.Q84bAuxH

open MeasureTheory Filter Topology

noncomputable section

namespace HRS.Q84b

variable {d : ℕ} {s : ℝ}

theorem q84b_slice_smooth {K : ℝ} {ψ : Torus d → Torus d → ℝ} (hPs : PsiSize s K ψ) (b : Torus d) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift (fun w => ψ w b))
      {u : Euc d | Torus.mk u ≠ b} := by
  have hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : Euc d => (u, Torus.rep b)) :=
    contDiff_id.prodMk contDiff_const
  have h := hPs.smooth.comp hcd.contDiffOn (s := {u : Euc d | Torus.mk u ≠ b}) (fun u hu => by
    show Torus.mk u ≠ Torus.mk (Torus.rep b)
    rw [Torus.mk_rep]; exact hu)
  refine h.congr fun u hu => ?_
  simp only [Torus.lift, Function.comp, lift2, Torus.mk_rep]

theorem q84b_Jop_mean (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {β : ℝ} (hβ : 0 < β)
    {V ρ : Torus d → ℝ} (hV : Torus.IsSmooth V)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (hρs : SmoothPosDensity ρ)
    {K : ℝ} {ψ : Torus d → Torus d → ℝ} (hPs : PsiSize s K ψ) (b : Torus d) :
    Integrable (fun x => ρ x * Jop d s ρ (fun w => ψ w b) x) ∧
    ∫ x, ρ x * Jop d s ρ (fun w => ψ w b) x =
      -∫ x, ρ x * inner ℝ (forceField d s ρ x) (gradFst ψ x b) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ s := by rw [hcrit]; linarith
  have hsd : s < d := by rw [hcrit]; linarith
  have hd0 : 0 < d := by omega
  have hρ1 : Torus.IsCk 1 ρ := Q84a.q84a_contDiff_one hρs.smooth
  have hforce := fun x => q84b_force_eq hd hs0 hsd hβ hV hρ hρs x
  obtain ⟨hI1, hI2, hmean⟩ := q84b_Rk_mean hd hcrit hρ1 hPs b hforce
  have hD := q84b_gradFst_integrable hd hcrit hPs b
  have hae : ∀ᵐ x : Torus d, ρ x * Jop d s ρ (fun w => ψ w b) x =
      ρ x * inner ℝ (forceField d s ρ x) (gradFst ψ x b) + ρ x * ∫ u, q84b_Rk ρ s (fun w => ψ w b) x u := by
    filter_upwards [q84b_ae_ne hd0 b] with x hx
    obtain ⟨-, hJ⟩ := q84b_Jop_eq hd hs0 hsd hβ hV hρ hρs hx (q84b_slice_smooth hPs b) hD.norm
    rw [hJ]
    simp only [gradFst]
    ring
  have hint : Integrable (fun x => ρ x * inner ℝ (forceField d s ρ x) (gradFst ψ x b) +
      ρ x * ∫ u, q84b_Rk ρ s (fun w => ψ w b) x u) := hI2.add hI1
  refine ⟨hint.congr (hae.mono fun x hx => hx.symm), ?_⟩
  rw [integral_congr_ae hae, integral_add hI2 hI1, hmean]
  ring

end HRS.Q84b
