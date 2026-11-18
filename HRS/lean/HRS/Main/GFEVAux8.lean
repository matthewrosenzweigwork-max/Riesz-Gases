import HRS.Main.GFEVAux7

/-!
# Packet GFEVG, part 8: the dual evolution `V` on `E_γ` (and `W` on `E_{γ-4}`), strong continuity
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.GF

open HRS HRS.PDE HRS.PDE.ET HRS.Uniform HRS.Uniform.Q54

variable {d : ℕ} {s : ℝ} {γ : ℕ} {R : Regime} {VB Λ : ℝ} {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ}

theorem GFPde.evolution (h : GFPde d s γ R VB Λ D T ρ) (l₀ l₂ l₄ : ℝ)
    (hq0 : QuasiAt (γ + 2) (UpF D (gfevMu T ρ)) (γ : ℝ) l₀)
    (hq2 : QuasiAt (γ + 2) (UpF D (gfevMu T ρ)) ((γ : ℝ) - 2) l₂)
    (hq4 : QuasiAt (γ + 2) (UpF D (gfevMu T ρ)) ((γ : ℝ) - 4) l₄) :
    ∃ (V : ℝ → ℝ → NegSobolev d (γ : ℝ) →L[ℝ] NegSobolev d (γ : ℝ))
      (W : ℝ → ℝ → NegSobolev d ((γ : ℝ) - 4) →L[ℝ] NegSobolev d ((γ : ℝ) - 4)),
      (∀ u t : ℝ, 0 ≤ u → u ≤ t → ∀ (z : NegSobolev d (γ : ℝ)) (φ : Torus d → ℝ), Dom (γ + 2) φ →
        NegSobolev.eval (V t u z) φ = NegSobolev.eval z (UpF D (gfevMu T ρ) u t φ)) ∧
      (∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖V t u‖ ≤ Real.exp (l₀ * (t - u))) ∧
      (∀ t : ℝ, 0 ≤ t → V t t = 1) ∧
      (∀ s' r' t : ℝ, 0 ≤ s' → s' ≤ r' → r' ≤ t → (V t r').comp (V r' s') = V t s') ∧
      (∀ (T' : ℝ) (x : NegSobolev d (γ : ℝ)),
        ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2 x) {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T'}) ∧
      (∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖W t u‖ ≤ Real.exp (l₄ * (t - u))) ∧
      (∀ u t : ℝ, 0 ≤ u → u ≤ t → ∀ z : NegSobolev d ((γ : ℝ) - 4),
        V t u (NegSobolev.embed (γ : ℝ) z) = NegSobolev.embed (γ : ℝ) (W t u z)) := by
  have hcore := h.core
  have hγ5 : (5 : ℝ) ≤ γ := by have := h.hγ5; exact_mod_cast this
  obtain ⟨A, B, hB, hhold⟩ := h.hold l₀ hq0
  obtain ⟨V, hVd, hVb, hVs, hVc⟩ := exists_evol (γ + 2) _ hcore (γ : ℝ) l₀
    (by push_cast; linarith) hq0
  obtain ⟨W, hWd, hWb, hWs, hWc⟩ := exists_evol (γ + 2) _ hcore ((γ : ℝ) - 4) l₄
    (by push_cast; linarith) hq4
  have hCD : ContData (γ + 2) (UpF D (gfevMu T ρ)) (γ : ℝ) V l₀ l₂ A B :=
    ⟨hcore, by push_cast; linarith, hq0, hq2, hhold, hB, hVd, hVb⟩
  refine ⟨V, W, hVd, hVb, hVs, hVc, fun T' x => strong_cont hCD T' x, hWb, ?_⟩
  intro u t hu hut z
  refine eq_of_eval_smooth fun φ hφ => ?_
  have hD : Dom (γ + 2) φ := dom_smooth hφ
  have h4 : (γ : ℝ) - 4 ≤ γ := by linarith
  rw [hVd u t hu hut _ φ hD, gfev_eval_embed h4, gfev_eval_embed h4, hWd u t hu hut z φ hD]

end HRS.GF
