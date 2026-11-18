import HRS.MH.ScreenedS4Aux1

/-!
# Packet S4, part 2: Parseval pairings
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate FourierTransform ContDiff

namespace HRS.MH.Screened

open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

/-- `h = 𝓕⁻ M` (pointwise) with `M ∈ L¹ ∩ L²` is real `L²` and `∫ v̂ conj(M) = ∫ v h`. -/
lemma s4_pair_h {v h : Euc d → ℝ} (hv : MemLp v 2 volume) {M : Euc d → ℂ} (h1 : Integrable M)
    (h2 : MemLp M 2 volume)
    (hh : ∀ y : Euc d, ((h y : ℝ) : ℂ) =
      ∫ ξ : Euc d, M ξ * Complex.exp (2 * Real.pi * Complex.I * (inner ℝ y ξ : ℝ))) :
    MemLp h 2 volume ∧
      ∫ ξ, fourierL2 v ξ * conj (M ξ) = ((∫ x, v x * h x : ℝ) : ℂ) := by
  set H : Lp (α := Euc d) ℂ 2 := (FT d).symm (h2.toLp M) with hH
  have hae : ∀ᵐ y : Euc d ∂volume, (H : Euc d → ℂ) y = ((h y : ℝ) : ℂ) := by
    filter_upwards [s4_bridge h1 h2] with y hy
    rw [hy, hh y]
  have hmemC : MemLp (fun y : Euc d => ((h y : ℝ) : ℂ)) 2 volume := (Lp.memLp H).ae_eq hae
  have hmem : MemLp h 2 volume := by
    have := hmemC.re
    simpa using this
  refine ⟨hmem, ?_⟩
  have hof : ofRealLp hmem = H := by
    apply Lp.ext
    filter_upwards [ofRealLp_coe hmem, hae] with y a b
    rw [a, b]
  have hF : fourierL2 h =ᵐ[volume] M := by
    rw [fourierL2_eq hmem, hof]
    have : FT d H = h2.toLp M := (FT d).apply_symm_apply _
    rw [this]
    exact h2.coeFn_toLp
  rw [← integral_fourierL2_mul_conj hv hmem]
  refine integral_congr_ae ?_
  filter_upwards [hF] with ξ hξ
  rw [hξ]

/-- Parseval for `W = 𝓕⁻ N`, `N ∈ L²`, against a real `L²` function `φ`. -/
lemma s4_pair_w {φ : Euc d → ℝ} (hφ : MemLp φ 2 volume) {N : Euc d → ℂ} (hN : MemLp N 2 volume) :
    ∫ x, ((FT d).symm (hN.toLp N) : Euc d → ℂ) x * ((φ x : ℝ) : ℂ) =
      ∫ ξ, N ξ * conj (fourierL2 φ ξ) := by
  set H : Lp (α := Euc d) ℂ 2 := (FT d).symm (hN.toLp N) with hH
  have e : inner ℂ (ofRealLp hφ) H = inner ℂ (FT d (ofRealLp hφ)) (hN.toLp N) := by
    rw [← inner_FT (ofRealLp hφ) H]
    have : FT d H = hN.toLp N := (FT d).apply_symm_apply _
    rw [this]
  have e1 : inner ℂ (ofRealLp hφ) H = ∫ x, (H : Euc d → ℂ) x * ((φ x : ℝ) : ℂ) := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [ofRealLp_coe hφ] with x hx
    rw [hx]
    simp
  have e2 : inner ℂ (FT d (ofRealLp hφ)) (hN.toLp N) = ∫ ξ, N ξ * conj (fourierL2 φ ξ) := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hN.coeFn_toLp] with ξ hξ
    rw [hξ, fourierL2_eq hφ]
    simp
  rw [← e1, e, e2]

end HRS.MH.Screened
