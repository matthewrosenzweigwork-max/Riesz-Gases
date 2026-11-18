import HRS.Main.GFEVAux13

/-!
# Packet GFEVG, part 14: the coefficient path of `U^{s,t} φ` and its integrated equation
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.GF

open HRS HRS.PDE HRS.PDE.ET HRS.Uniform HRS.Uniform.Q54

variable {d : ℕ} {s : ℝ} {γ : ℕ} {R : Regime} {VB Λ : ℝ} {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ}

theorem GFPde.forward_link (h : GFPde d s γ R VB Λ D T ρ) {φ : Torus d → ℝ} (hφ : Dom (γ + 2) φ)
    {t : ℝ} (ht : 0 < t) :
    ∃ F : ℝ → Coeff d, IsForwardSolution D (gfevMu T ρ) t (coeffOf φ) F ∧
      ∀ σ ∈ Set.Icc (0 : ℝ) t, coeffOf (UpF D (gfevMu T ρ) (t - σ) t φ) = F σ := by
  have hJm : mStar d ≤ γ + 2 := by have := h.hm; omega
  have hJ1 : 1 ≤ γ + 2 := by omega
  have hJd : (d : ℝ) / 2 < ((γ + 2 : ℕ) : ℝ) := by
    have := h.dgt; push_cast; linarith
  have hA : AdjointData s (γ + 2) R 1 Λ VB D 0 t (gfevMu T ρ) := h.adjointData (m := γ + 2) (by omega) ht
  have htm : t ∈ Set.Ioc 0 t := ⟨ht, le_rfl⟩
  obtain ⟨C₀, -, hspec⟩ := propagatorCoeff_spec h.hd s h.hs0 h.hsd (γ + 2) hJ1 R 1 Λ VB
  have hφc : MemHs ((γ + 2 : ℕ) : ℝ) (coeffOf φ) := (hsNormSq_coeffOf _ φ hφ.2).1
  obtain ⟨hsol, hw, -⟩ := hspec D 0 t (gfevMu T ρ) hA t htm (coeffOf φ) hφc
  refine ⟨propagatorCoeff D (gfevMu T ρ) ((γ + 2 : ℕ) : ℝ) t (coeffOf φ), hsol, fun σ hσ => ?_⟩
  by_cases h0 : σ = 0
  · subst h0
    simp only [sub_zero, upF_self]
    funext k
    have := hsol.eq k 0 ⟨le_rfl, ht.le⟩
    simpa using this.symm
  · have hlt : t - σ ≠ t := by intro h'; apply h0; linarith
    rw [upF_of_ne D _ hlt]
    have hu : t - σ ∈ Set.Icc (0 : ℝ) t := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
    obtain ⟨hprop, -⟩ := prop_facts h.hd s h.hs0 h.hsd (γ + 2) hJm R 1 Λ VB D 0 t (gfevMu T ρ) hA htm hφ hu
    obtain ⟨hreal, hsum⟩ := pc_data h.hd s h.hs0 h.hsd (γ + 2) hJ1 hJd R 1 Λ VB D 0 t (gfevMu T ρ) hA htm hφ hσ
    rw [hprop]
    have := coeffOf_toFun _ hreal hsum
    simpa using this

/-- The increment formula for a forward solution. -/
theorem gfev_forward_increment {μ : ℝ → Torus d → ℝ} {t : ℝ} {φc : Coeff d} {F : ℝ → Coeff d}
    (hF : IsForwardSolution D μ t φc F) (k : Lattice d) {τ₁ τ₂ : ℝ} (h1 : 0 ≤ τ₁) (h12 : τ₁ ≤ τ₂)
    (h2 : τ₂ ≤ t) :
    F τ₂ k - F τ₁ k = ∫ σ in τ₁..τ₂, forwardGen D (μ (t - σ)) (F σ) k := by
  have hI : IntegrableOn (fun σ => forwardGen D (μ (t - σ)) (F σ) k) (Set.Icc 0 t) := hF.integrable k
  have hint : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ t →
      IntervalIntegrable (fun σ => forwardGen D (μ (t - σ)) (F σ) k) volume a b := by
    intro a b ha hab hb
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact hI.mono_set (Set.Icc_subset_Icc ha hb)
  have e1 := hF.eq k τ₂ ⟨h1.trans h12, h2⟩
  have e2 := hF.eq k τ₁ ⟨h1, h12.trans h2⟩
  rw [e1, e2, add_sub_add_left_eq_sub, intervalIntegral.integral_interval_sub_left
    (hint 0 τ₂ le_rfl (h1.trans h12) h2) (hint 0 τ₁ le_rfl h1 (h12.trans h2))]

end HRS.GF
