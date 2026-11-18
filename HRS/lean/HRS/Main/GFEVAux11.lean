import HRS.Main.GFEVAux10

/-!
# Packet GFEVG, part 11: the dual operators `A_t : E_{γ-2} → E_γ` and their operator-norm continuity in `t`
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.GF

open HRS HRS.PDE HRS.PDE.ET HRS.Uniform HRS.Uniform.Q54

variable {d : ℕ} {s : ℝ} {γ : ℕ} {R : Regime} {VB Λ : ℝ} {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ}

/-- Two dual operators of nearby maps are close in operator norm. -/
theorem gfev_dual_diff {P : (Torus d → ℝ) → Prop} {a b : ℝ} {Up₁ Up₂ : (Torus d → ℝ) → Torus d → ℝ}
    {M₁ M₂ MΔ : ℝ} (h1 : GfDualHyp P a b Up₁ M₁) (h2 : GfDualHyp P a b Up₂ M₂) (hMΔ : 0 ≤ MΔ)
    (hbd : ∀ φ, P φ → MemSobolev b (fun x => Up₁ φ x - Up₂ φ x) ∧
      sobolevNorm b (fun x => Up₁ φ x - Up₂ φ x) ≤ MΔ * sobolevNorm a φ)
    (V₁ V₂ : NegSobolev d b →L[ℝ] NegSobolev d a)
    (hV₁ : ∀ (z : NegSobolev d b) (φ : Torus d → ℝ), P φ → NegSobolev.eval (V₁ z) φ = NegSobolev.eval z (Up₁ φ))
    (hV₂ : ∀ (z : NegSobolev d b) (φ : Torus d → ℝ), P φ → NegSobolev.eval (V₂ z) φ = NegSobolev.eval z (Up₂ φ)) :
    ‖V₁ - V₂‖ ≤ MΔ := by
  have hΔ : GfDualHyp P a b (fun φ x => Up₁ φ x - Up₂ φ x) MΔ :=
    ⟨hMΔ, h1.smooth, h1.memS, h1.closed, fun φ ψ hφ hψ α β => by
      funext x
      have e1 := congrFun (h1.lin φ ψ hφ hψ α β) x
      have e2 := congrFun (h2.lin φ ψ hφ hψ α β) x
      simp only [e1, e2]; ring, fun c => by
      funext x
      simp [h1.const c, h2.const c], hbd⟩
  obtain ⟨V, hVn, hVd⟩ := gfev_exists_dual_op2 hΔ
  have hVV : V₁ - V₂ = V := by
    refine ContinuousLinearMap.ext fun z => eq_of_eval_smooth fun φ hφ => ?_
    have hP := h1.smooth φ hφ
    have hMa : MemSobolev a φ := h1.memS φ hP
    rw [ContinuousLinearMap.sub_apply, eval_sub_left _ _ hMa, hV₁ z φ hP, hV₂ z φ hP, hVd z φ hP]
    exact (eval_sub_fun z (hbd φ hP).1 (h1.bd φ hP).1 (h2.bd φ hP).1).symm
  rw [hVV]; exact hVn

theorem GFPde.generatorOp (h : GFPde d s γ R VB Λ D T ρ) :
    ∃ (M : ℝ) (A2 : ℝ → NegSobolev d ((γ : ℝ) - 2) →L[ℝ] NegSobolev d (γ : ℝ)), 0 ≤ M ∧
      (∀ t, ‖A2 t‖ ≤ M) ∧ (∀ t (z : NegSobolev d ((γ : ℝ) - 2)) (φ : Torus d → ℝ), Dom (γ + 2) φ →
        NegSobolev.eval (A2 t z) φ = NegSobolev.eval z (gfevL D (gfevMu T ρ t) φ)) ∧
      (∀ t, GfDualHyp (Dom (γ + 2)) (γ : ℝ) ((γ : ℝ) - 2) (gfevL D (gfevMu T ρ t)) M) := by
  obtain ⟨M, hM, hdual⟩ := h.generator
  have hex := fun t => gfev_exists_dual_op2 (hdual t)
  choose A2 hn hd using hex
  exact ⟨M, A2, hM, hn, hd, hdual⟩

end HRS.GF
