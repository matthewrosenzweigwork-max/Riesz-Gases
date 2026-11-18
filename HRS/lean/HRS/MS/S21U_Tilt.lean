import HRS.MS.TiltAux14
import HRS.MS.MovThermAux1
import HRS.MS.WsPrepI7

/-!
# S21U packet 1: `S21iTiltClass` (perturbation-uniform static preparation) from the merged ED15 uniform chain

`s21u_tiltClass`: for `d ≥ 2`, `0 ≤ s < d`, `a, β, β₀ > 0`, `J > d/2 + 2` and `ε_* ≤ 1/2`, the class `S21iTiltClass d s a β β₀ J ε_*` holds:
two constants `C_st, C_s ≥ 0`, chosen before `ρ_β`, `ε`, `ψ`, `N`, such that for every thermal equilibrium `ρ_β` and every
`IsAdmissiblePerturbation ρ_β ε_* ε ψ` and `N ≥ 2` the static bundle `S21iStatic` holds at `μ₀ = (1+εψ)ρ_β dx`.
Inputs: `s47_conclusion_unif` (static field clause and the bias), `s47_setup_unif` (probability, exchangeability and linear variance
at `N`), `mv0_rho_eq` (every `IsThermalEquilibrium` density is `thermalDensity` pointwise, via `thermalDensity_spec_proof` / `logThermalDensity_spec_proof`),
`s48_cbu_bound` (`|ε ψ| ≤ ε_* ≤ 1/2` from the `C_b^{100d+1001}` part of the smallness; the oscillator part is only used through its nonnegativity).
Parameters of the use: `a_m = a_p = a`, `β_m = β_p = β`, `γ_m = γ_p = β₀`.

`s21u_init`: `s21i_init` (WsPrepI7) with the tilt hypothesis discharged: INIT from the orbit input alone (`ε_* ≤ 1/2`).
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S21

open HRS.Whole HRS.MS.GenPath
open HRS (Euc cbNorm MemCb smoothDist)

variable {d : ℕ}

/-- `StaticFieldConclusion` is monotone in the constant. -/
theorem s21u_sfc_mono {s : ℝ} {N : ℕ} {P : Measure (EucConfig d N)} {ν : Measure (Euc d)} {J : ℕ}
    {φ : ℕ → Euc d → ℝ} {γ : Measure SeqL2} {C C' : ℝ} (hC : C ≤ C')
    (h : StaticFieldConclusion d s N P ν J φ γ C) : StaticFieldConclusion d s N P ν J φ γ C' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hS0 : 0 ≤ featureSum J φ := tsum_nonneg fun i => HRS.MS.Tc5.tc5_cb_nonneg J (φ i)
  refine ⟨h1, h2, h3.trans ?_, fun F hF D₁ D₂ hD₁ hD₂ => ?_⟩
  · refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (by positivity)) (Real.sqrt_nonneg _)
  · obtain ⟨i1, i2, i3⟩ := h4 F hF D₁ D₂ hD₁ hD₂
    refine ⟨i1, i2, i3.trans ?_⟩
    have hD₁0 : 0 ≤ D₁ := (norm_nonneg _).trans (hD₁ 0)
    have hD₂0 : 0 ≤ D₂ := (norm_nonneg _).trans (hD₂ 0)
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (Real.sqrt_nonneg _)) (by positivity)

/-- **`S21iTiltClass`**: the static preparation bundle with constants uniform over the frozen admissible class. -/
theorem s21u_tiltClass (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β β₀ : ℝ} (ha : 0 < a) (hβ : 0 < β)
    (hβ₀ : 0 < β₀) {J : ℕ} (hJ : (d : ℝ) / 2 + 2 < J) {εstar : ℝ} (hε : εstar ≤ 1 / 2) :
    S21iTiltClass d s a β β₀ J εstar := by
  obtain ⟨C, Cs1, hCs1, h⟩ := S47.s47_conclusion_unif hd hs0 hsd J hJ a a β β β₀ β₀ ha hβ hβ₀ εstar
  obtain ⟨Cs2, C2, c2, BU, BB, KR, KT, hCs2, -, -, hsu⟩ :=
    S47.s47_setup_unif hd hs0 hsd (am := a) (ap := a) (βm := β) (βp := β) (γm := β₀) (γp := β₀) ha hβ hβ₀
      le_rfl le_rfl le_rfl εstar
  have hmem : ∀ x : ℝ, x ∈ Set.Icc x x := fun x => ⟨le_rfl, le_rfl⟩
  refine ⟨max C 0, max Cs1 Cs2, le_max_right _ _, hCs1.trans (le_max_left _ _), ?_⟩
  intro ρβ hρβ ε ψ hψ N hN
  have hρeq : ρβ = thermalDensity d s a β := HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρβ
  subst hρeq
  have hN1 : 1 ≤ N := by omega
  have hosc : 0 ≤ oscNorm (102 * (d : ℝ) + 1020) (fun x => ε * Real.sqrt (thermalDensity d s a β x) * ψ x) :=
    Real.sqrt_nonneg _
  have hcb : cbNorm (100 * d + 1001) (fun x => ε * ψ x) ≤ εstar := by
    have := hψ.small
    linarith
  have hcb0 := S48.s48_cbu_bound hψ.smooth hψ.compactSupport ε εstar (100 * d + 1001) hcb 0 (Nat.zero_le _)
  have htilt : IsTiltData d s a β ψ ε :=
    ⟨hψ.smooth, hψ.compactSupport, hψ.meanZero, fun x => by
      have := hcb0 x
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
      linarith⟩
  obtain ⟨Bd, hS⟩ := hsu a (hmem a) β (hmem β) β₀ (hmem β₀) ε ψ htilt hcb
  have hβ₀' : 0 < β₀ := hβ₀
  set ρ : Euc d → ℝ := perturbedDensity (thermalDensity d s a β) ε ψ with hρdef
  have hPeq : S47.s47_P d s ρ β₀ N = HRS.Whole.modulatedGibbs (rieszKernel d s) N β₀ (HRS.Whole.withDensityReal ρ) :=
    S47.s47_P_eq (by omega) hs0 hsd hS.hT.hc hS.hT.C0 hS.hT.prob hS.hT.smooth.continuous hS.hT.pos
      hS.hT.h0 hβ₀ N
  have hνeq : S47.s47_nu d s ρ β₀ N = HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs (rieszKernel d s) N β₀ (HRS.Whole.withDensityReal ρ)) := by
    rw [← hPeq]
  have hSt := hS.hS N hN
  have hδ0 : 0 ≤ HRS.deltaN d s N := HRS.deltaN_nonneg s hN1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← hPeq]; exact hSt.prob
  · rw [← hPeq]; exact hSt.exch
  · intro f hf
    have h1 := hSt.linear f hf
    rw [hPeq] at h1
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    have hI : 0 ≤ ∫ x, f x ^ 2 ∂(HRS.Whole.withDensityReal ρ) := integral_nonneg fun x => sq_nonneg _
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (le_max_right _ _) hN0.le) hI
  · intro f hf Bf hBf
    have h1 := S47.s47_bias hS.hT.prob hSt hf hBf
    rw [hνeq] at h1
    have hBf0 : 0 ≤ Bf := (abs_nonneg _).trans (hBf 0)
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hBf0)
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hδ0
  · intro φ hφ γ hγ
    obtain ⟨h1, -⟩ := h a (hmem a) β (hmem β) β₀ (hmem β₀) ε ψ htilt hcb φ hφ N hN γ hγ
    have h1' : StaticFieldConclusion d s N (S47.s47_P d s ρ β₀ N) (S47.s47_nu d s ρ β₀ N) J φ γ C := h1
    rw [hνeq, hPeq] at h1'
    exact s21u_sfc_mono (le_max_left _ _) h1'

/-- **INIT from the orbit input alone**: `s21i_init` with the tilt hypothesis discharged (`ε_* ≤ 1/2`). -/
theorem s21u_init (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β β₀ : ℝ} (ha : 0 < a) (hβ : 0 < β)
    (hβ₀ : 0 ≤ β₀) {T : ℝ} (hT : 0 < T) {εstar c₁ C₁ Corb : ℝ} (hε : εstar ≤ 1 / 2)
    (horb : S21iOrbClass d s a β T εstar c₁ C₁ Corb) :
    ∃ Cinit : ℝ, 0 ≤ Cinit ∧ S21InitWin d s a β β₀ T εstar c₁ C₁ Cinit := by
  refine s21i_init hd hs0 hsd ha hβ hβ₀ hT horb fun hpos => ?_
  refine s21u_tiltClass hd hs0 hsd ha hβ hpos ?_ hε
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have : ((4 * d + 42 : ℕ) : ℝ) = 4 * d + 42 := by push_cast; ring
  rw [this]
  linarith

end HRS.MS.S21

end
