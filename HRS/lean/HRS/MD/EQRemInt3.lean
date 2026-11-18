import HRS.MD.EQRemInt2

/-!
# EQ-REM (b), part 3: Fourier expansion of the stationary remainder
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MD.EQRem

open HRS HRS.MD.EQ29 HRS.Quad

variable {d : ℕ} {s : ℝ}

/-- For each configuration, `φ ↦ 𝓡_{stat}(φ)(X)` is a bounded linear functional on `C²` vanishing on constants, hence it has
the Fourier expansion `𝓡(φ) = ∑_k φ̂_k 𝓡(e_k)` for `φ ∈ C² ∩ H^M`. -/
theorem eqrem_stat_expansion (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ) (hV : Torus.IsSmooth V)
    {β : ℝ} (hβ : 0 < β) {ρβ : Torus d → ℝ} (hρ : IsThermalDensity (periodicRiesz d s) V β ρβ)
    {N : ℕ} (hN : 2 ≤ N) {M : ℝ} (hM : (d : ℝ) / 2 + 2 < M) (X : Config d N)
    {φ : Torus d → ℝ} (hφ : Torus.IsCk 2 φ)
    (hs : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * M) * Torus.funRealCoeff φ k ^ 2) :
    Tendsto (fun F : Finset (NonzeroLattice d) =>
        ∑ k ∈ F, Torus.funRealCoeff φ k * statRemainder d s V β ρβ (N := N) (Torus.realMode k) X)
      atTop (𝓝 (statRemainder d s V β ρβ (N := N) φ X)) := by
  have hN0 : 0 < N := by omega
  obtain ⟨C₀, hC₀, hgood⟩ := eqrem_pairKernel_envGood hd hs0 hsd
  obtain ⟨𝔅, h𝔅0, h𝔅⟩ := eqrem_remA_bound hd hs0 hsd V hV hβ hρ hN
  refine eqrem_expansion hM (fun ψ => statRemainder d s V β ρβ (N := N) ψ X) (C₀ * 𝔅 X) ?_ ?_ ?_ ?_ hφ hs
  · intro ψ₁ ψ₂ h1 h2
    show remA d s V β ρβ (pairKernel d s fun x => ψ₁ x + ψ₂ x) X =
      remA d s V β ρβ (pairKernel d s ψ₁) X + remA d s V β ρβ (pairKernel d s ψ₂) X
    have : pairKernel d s (fun x => ψ₁ x + ψ₂ x) = fun x y => pairKernel d s ψ₁ x y + pairKernel d s ψ₂ x y :=
      funext fun x => funext fun y => eqrem_pairKernel_add h1 h2 x y
    rw [this]
    exact eqrem_remA_add hd hs0 hsd V hV hβ hρ hN (hgood ψ₁ h1) (hgood ψ₂ h2) X
  · intro c ψ h1
    show remA d s V β ρβ (pairKernel d s fun x => c * ψ x) X = c * remA d s V β ρβ (pairKernel d s ψ) X
    have : pairKernel d s (fun x => c * ψ x) = fun x y => c * pairKernel d s ψ x y :=
      funext fun x => funext fun y => eqrem_pairKernel_smul c x y
    rw [this]
    exact eqrem_remA_smul hN0 c _ X V β ρβ
  · intro c
    show remA d s V β ρβ (pairKernel d s fun _ => c) X = 0
    have : pairKernel d s (fun _ : Torus d => c) = fun _ _ => (0 : ℝ) :=
      funext fun x => funext fun y => eqrem_pairKernel_const c x y
    rw [this]
    have h := eqrem_remA_smul hN0 0 (fun _ _ : Torus d => (0 : ℝ)) X V β ρβ (s := s)
    simpa using h
  · intro ψ h1
    have := h𝔅 _ _ (hgood ψ h1) X
    show |remA d s V β ρβ (pairKernel d s ψ) X| ≤ C₀ * 𝔅 X * Torus.cbNorm 2 ψ
    calc _ ≤ (C₀ * Torus.cbNorm 2 ψ) * 𝔅 X := this
      _ = _ := by ring

end HRS.MD.EQRem

end
