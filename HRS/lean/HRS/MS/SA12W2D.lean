import HRS.MS.SA12W2C

/-!
# S.A.12 C5 (SA12W2 worker), part D: the compatible all-order torus path (`R26-T5.T04`)
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ComplexConjugate ContDiff

namespace HRS.PDE.SA12W2

variable {d : ℕ}

theorem sa12w2_torus_path (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (Rg : PDE.Regime)
    (D : DynData d) (ν₀ T : ℝ) (ρ : ℝ → Torus d → ℝ)
    (hA : ∀ N : ℕ, ∃ MB Λ VB : ℝ, PDE.AdjointData s N Rg MB Λ VB D ν₀ T ρ)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T) (φc : PDE.Coeff d)
    (hφ : ∀ N : ℕ, PDE.MemHs (N : ℝ) φc) (hr : PDE.IsRealCoeff φc) :
    ∃ P : ℝ → PDE.Coeff d, P 0 = φc ∧
      (∀ τ ∈ Icc (0 : ℝ) t, PDE.IsRealCoeff (P τ) ∧ ∀ N : ℕ, PDE.MemHs (N : ℝ) (P τ)) ∧
      (∀ τ ∈ Icc (0 : ℝ) t, ContDiff ℝ ∞ (Torus.lift (PDE.toFun (P τ)))) ∧
      (∀ j : ℕ, ContinuousOn (fun p : ℝ × Euc d =>
        iteratedFDeriv ℝ j (Torus.lift (PDE.toFun (P p.1))) p.2) (Icc (0 : ℝ) t ×ˢ univ)) ∧
      (∀ j : ℕ, ∀ y : Euc d, ∀ τ ∈ Icc (0 : ℝ) t,
        HasDerivWithinAt (fun σ => iteratedFDeriv ℝ j (Torus.lift (PDE.toFun (P σ))) y)
          (iteratedFDeriv ℝ j (Torus.lift (PDE.toFun (PDE.forwardGen D (ρ (t - τ)) (P τ)))) y)
          (Icc (0 : ℝ) t) τ) ∧
      (∀ j : ℕ, ContinuousOn (fun p : ℝ × Euc d =>
        iteratedFDeriv ℝ j (Torus.lift (PDE.toFun (PDE.forwardGen D (ρ (t - p.1)) (P p.1)))) p.2)
          (Icc (0 : ℝ) t ×ˢ univ)) ∧
      (∀ τ ∈ Icc (0 : ℝ) t, backwardGenerator D (ρ (t - τ)) (PDE.toFun (P τ)) =
        PDE.toFun (PDE.forwardGen D (ρ (t - τ)) (P τ))) := by
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ → PDE.Coeff d, P = PDE.propagatorCoeff D ρ ((1 : ℕ) : ℝ) t φc := ⟨_, rfl⟩
  -- level compatibility
  have hlev : ∀ N : ℕ, 1 ≤ N → ∀ τ ∈ Icc (0 : ℝ) t, P τ = PDE.propagatorCoeff D ρ (N : ℝ) t φc τ := by
    intro N hN τ hτ
    obtain ⟨MB, Λ, VB, h⟩ := hA N
    rw [hPdef]
    exact ClassicalPart.propagatorCoeff_level hd s hs0 hsd 1 N le_rfl hN Rg MB Λ VB D ν₀ T ρ h t ht φc
      (hφ N) τ hτ
  have hspecN : ∀ N : ℕ, 1 ≤ N → ∀ τ ∈ Icc (0 : ℝ) t,
      PDE.MemHs (N : ℝ) (P τ) ∧ PDE.IsRealCoeff (P τ) := by
    intro N hN τ hτ
    obtain ⟨MB, Λ, VB, h⟩ := hA N
    obtain ⟨C, hC, hspec⟩ := propagatorCoeff_spec hd s hs0 hsd N hN Rg MB Λ VB
    obtain ⟨hsol, hw, -⟩ := hspec D ν₀ T ρ h t ht φc (hφ N)
    rw [hlev N hN τ hτ]
    exact ⟨hw.1 τ hτ, ClassicalPart.propagatorCoeff_real hd s hs0 hsd N hN Rg MB Λ VB D ν₀ T ρ h t ht
      φc (hφ N) hr τ hτ⟩
  refine ⟨P, ?_, fun τ hτ => ⟨(hspecN 1 le_rfl τ hτ).2, fun N => ?_⟩, fun τ hτ => ?_, fun j => ?_,
    fun j y τ hτ => ?_, fun j => ?_, fun τ hτ => ?_⟩
  · -- initial value
    obtain ⟨MB, Λ, VB, h⟩ := hA 1
    obtain ⟨C, hC, hspec⟩ := propagatorCoeff_spec hd s hs0 hsd 1 le_rfl Rg MB Λ VB
    obtain ⟨hsol, -, -⟩ := hspec D ν₀ T ρ h t ht φc (hφ 1)
    funext k
    have := hsol.eq k 0 ⟨le_rfl, ht.1.le⟩
    rw [hPdef]
    simpa using this
  · exact (hspecN (N + 1) (by omega) τ hτ).1.mono (by push_cast; linarith)
  · -- smoothness
    rw [contDiff_infty]
    intro n
    set N : ℕ := ⌊(d : ℝ) / 2⌋₊ + n + 1 with hN
    have hlt : (d : ℝ) / 2 + n < (N : ℝ) := by
      have := Nat.lt_floor_add_one ((d : ℝ) / 2)
      simp only [hN]; push_cast; linarith
    obtain ⟨C, hC⟩ := toFun_isCk_le (d := d) n (N : ℝ) hlt
    exact (hC _ (hspecN N (by omega) τ hτ).1 (hspecN N (by omega) τ hτ).2).1
  · -- jets continuity
    obtain ⟨N, hN, h⟩ := sa12w2_C4 hd s hs0 hsd j Rg
    obtain ⟨MB, Λ, VB, hAN⟩ := hA N
    obtain ⟨h1, -⟩ := h MB Λ VB D ν₀ T ρ hAN t ht φc (hφ N) hr
    exact (h1 j le_rfl).congr fun p hp => by rw [hlev N hN p.1 hp.1]
  · -- time derivative
    obtain ⟨N, hN, h⟩ := sa12w2_C4 hd s hs0 hsd j Rg
    obtain ⟨MB, Λ, VB, hAN⟩ := hA N
    obtain ⟨-, h2⟩ := h MB Λ VB D ν₀ T ρ hAN t ht φc (hφ N) hr
    have := h2 j le_rfl y τ hτ
    refine (this.congr (fun σ hσ => ?_) ?_).congr_deriv ?_
    · rw [hlev N hN σ hσ]
    · rw [hlev N hN τ hτ]
    · rw [hlev N hN τ hτ]
  · -- generator jets
    obtain ⟨N, hN, h⟩ := sa12w2_gen_jets hd s hs0 hsd j Rg
    obtain ⟨MB, Λ, VB, hAN⟩ := hA N
    obtain ⟨-, h2⟩ := h MB Λ VB D ν₀ T ρ hAN t ht φc (hφ N) hr
    exact (h2 j le_rfl).congr fun p hp => by rw [hlev N hN p.1 hp.1]
  · -- backward generator
    obtain ⟨N, hN, h⟩ := sa12w2_gen_jets hd s hs0 hsd 0 Rg
    obtain ⟨MB, Λ, VB, hAN⟩ := hA N
    obtain ⟨h1, -⟩ := h MB Λ VB D ν₀ T ρ hAN t ht φc (hφ N) hr
    obtain ⟨hG, hGr, hc, hu⟩ := h1 τ hτ
    rw [← hlev N hN τ hτ] at hG hGr hc hu
    have hV1 : Torus.IsCk 1 D.V := ClassicalAux.isCk_of_le (by exact_mod_cast (by omega : 1 ≤ N + 3)) hAN.hV.1
    have hρ1 : Torus.IsCk 1 (ρ (t - τ)) :=
      ClassicalAux.isCk_of_le (by exact_mod_cast (by omega : 1 ≤ N + 3))
        (hAN.hμ.smooth (t - τ) ⟨by linarith [hτ.2], by linarith [hτ.1, ht.2]⟩)
    exact ClassicalPart.backwardGenerator_eq_toFun D (ClassicalAux.convKernelFacts hd D) hV1 hρ1
      (hspecN 1 le_rfl τ hτ).2 hc hu hGr hG

end HRS.PDE.SA12W2
