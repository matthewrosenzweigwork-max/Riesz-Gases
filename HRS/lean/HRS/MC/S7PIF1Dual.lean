import HRS.MC.S7PIF1Ito
import HRS.Stochastic.DualityProof
import HRS.Sections.Sec7Setting
import HRS.Main.GFSpec1
import HRS.MC.RegSet

/-!
# Packet piF1 (F1): the duality identity for every `N ≥ 1`

`S7PIF1_duality_identity_all` is `HRS.duality_identity_all` (Stochastic/DualityProof.lean:164) with `2 ≤ N` replaced by
`0 < N` (the proof is verbatim, using `S7PIF1_empirical_ito_of_contact`); `s7_PIF_duality_proof` derives the hypotheses
from the regime `R` and the prepared realisation (`Regime.mf`, `RegSet.reg_proof`, `IsStrongSolution.toContact`,
`nullContactOccupation_of_strong`).
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIF1

open HRS HRS.Sec7 HRS.MC.Sec7

variable {d N : ℕ}

theorem S7PIF1_duality_identity_all
    (hd : 1 ≤ d) (hN : 0 < N) [NeZero N] {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {D : DynData d} (hV : Torus.IsCk 2 D.V)
    {T Λ : ℝ} {ρ : ℝ → Torus d → ℝ}
    (hρ : IsMeanFieldSolution D T ρ) (hreg : IsRegularMF 3 Λ T ρ)
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : IsContactStrongSolution P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X)
    (hocc : D.M = 0 ∨ NullContactOccupation P T X)
    {t : ℝ} (ht : t ∈ Ioc 0 T) {φ : Torus d → ℝ} (hφ : Torus.IsCk 2 φ)
    {f : ℝ → Torus d → ℝ} (hf : IsClassicalAdjointSolution D ρ t φ f) :
    IsProgressiveL2 P ℱ (empiricalNoiseIntegrand D t f X) ∧
    ∀ᵐ ω ∂P, ∀ τ ∈ Icc 0 t,
      IntegrableOn (fun r => flucInteraction D (f r) (X (Real.toNNReal r) ω) (ρ r)) (Icc 0 τ) ∧
      flucPair (X (Real.toNNReal τ) ω) (ρ τ) (f τ)
        = flucPair (X 0 ω) (ρ 0) (f 0)
          + empiricalMartingale P ℱ W' D t f X (Real.toNNReal τ) ω
          + ∫ r in (0 : ℝ)..τ, flucInteraction D (f r) (X (Real.toNNReal r) ω) (ρ r) := by
  have ht' : t ∈ Icc 0 T := ⟨ht.1.le, ht.2⟩
  have hNpos : 0 < N := hN
  have hC := hf.isC12Test
  have hRg := MFReg.of_regular hρ hreg
  obtain ⟨hprog, hae⟩ := S7PIF1_empirical_ito_of_contact hN hV hX hF hocc ht' hC
  refine ⟨hprog, ?_⟩
  filter_upwards [hae] with ω hω
  intro τ hτ
  have hτT : τ ∈ Icc 0 T := ⟨hτ.1, hτ.2.trans ht'.2⟩
  obtain ⟨hint1, heq1⟩ := hω τ hτ
  obtain ⟨hint2, heq2⟩ := meanField_pairing_timeDependent hd hV hρ hreg hτT (hC.restrict hτ)
  -- the pointwise identity on `[0,τ]`
  have hpt : ∀ r ∈ Icc 0 τ,
      (pair (empirical (X (Real.toNNReal r) ω))
          (fun x => -(backwardGenerator D (ρ r) (f r) x) + D.invβ * Torus.laplacian (f r) x
            - inner ℝ (Torus.grad D.V x) (Torus.grad (f r) x))
        + interactionPairing D (f r) (empirical (X (Real.toNNReal r) ω))
            (empirical (X (Real.toNNReal r) ω)))
      - pair (withDensityReal (ρ r))
          (fun x => -(backwardGenerator D (ρ r) (f r) x) + D.invβ * Torus.laplacian (f r) x
            + inner ℝ (meanFieldDrift D (ρ r) x) (Torus.grad (f r) x))
      = flucInteraction D (f r) (X (Real.toNNReal r) ω) (ρ r) := by
    intro r hr
    have hrt : r ∈ Icc 0 t := ⟨hr.1, hr.2.trans hτ.2⟩
    have hrT : r ∈ Icc 0 T := ⟨hr.1, hr.2.trans (hτ.2.trans ht'.2)⟩
    exact fluc_pointwise hd hNpos (hRg.dens r hrT) (hRg.c1 r hrT) (hRg.lip r hrT)
      (hC.c2 r hrt) (X (Real.toNNReal r) ω)
  have hint : IntegrableOn (fun r => flucInteraction D (f r) (X (Real.toNNReal r) ω) (ρ r))
      (Icc 0 τ) := by
    refine (hint1.sub hint2).congr_fun (fun r hr => ?_) measurableSet_Icc
    exact hpt r hr
  refine ⟨hint, ?_⟩
  have hii1 : IntervalIntegrable (fun r => pair (empirical (X (Real.toNNReal r) ω))
          (fun x => -(backwardGenerator D (ρ r) (f r) x) + D.invβ * Torus.laplacian (f r) x
            - inner ℝ (Torus.grad D.V x) (Torus.grad (f r) x))
        + interactionPairing D (f r) (empirical (X (Real.toNNReal r) ω))
            (empirical (X (Real.toNNReal r) ω))) volume 0 τ := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hτ.1]
    exact hint1
  have hii2 : IntervalIntegrable (fun r => pair (withDensityReal (ρ r))
          (fun x => -(backwardGenerator D (ρ r) (f r) x) + D.invβ * Torus.laplacian (f r) x
            + inner ℝ (meanFieldDrift D (ρ r) x) (Torus.grad (f r) x))) volume 0 τ := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hτ.1]
    exact hint2
  have hsplit : ∫ r in (0 : ℝ)..τ, flucInteraction D (f r) (X (Real.toNNReal r) ω) (ρ r)
      = (∫ r in (0 : ℝ)..τ, (pair (empirical (X (Real.toNNReal r) ω))
          (fun x => -(backwardGenerator D (ρ r) (f r) x) + D.invβ * Torus.laplacian (f r) x
            - inner ℝ (Torus.grad D.V x) (Torus.grad (f r) x))
        + interactionPairing D (f r) (empirical (X (Real.toNNReal r) ω))
            (empirical (X (Real.toNNReal r) ω))))
        - ∫ r in (0 : ℝ)..τ, pair (withDensityReal (ρ r))
          (fun x => -(backwardGenerator D (ρ r) (f r) x) + D.invβ * Torus.laplacian (f r) x
            + inner ℝ (meanFieldDrift D (ρ r) x) (Torus.grad (f r) x)) := by
    rw [← intervalIntegral.integral_sub hii1 hii2]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [Set.uIcc_of_le hτ.1] at hr
    exact (hpt r hr).symm
  rw [hsplit]
  unfold flucPair
  linarith

/-! ### F1: the statement of `HRS.MC.Sec7.PIPlan.s7_PIF_duality`, proved -/

section Prob

variable (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) (N : ℕ) (hN : 1 ≤ N)
  {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
  (hreal : PreparedRealization R.D P
    (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) X₀ W X)

include hm hT hN hreal

omit hm in
theorem s7_PIF_duality_proof {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hF : IsFilteredSolution P ℱ W' W X) {t : ℝ} (ht : t ∈ Set.Ioc 0 T) {φ : Torus d → ℝ} (hφ : Torus.IsCk 2 φ)
    {f : ℝ → Torus d → ℝ} (hf : IsClassicalAdjointSolution R.D R.ρ t φ f) :
    IsProgressiveL2 P ℱ (empiricalNoiseIntegrand R.D t f X) ∧
    ∀ᵐ ω ∂P, ∀ τ ∈ Set.Icc 0 t,
      IntegrableOn (fun r => flucInteraction R.D (f r) (X (Real.toNNReal r) ω) (R.ρ r)) (Set.Icc 0 τ) ∧
      flucPair (X (Real.toNNReal τ) ω) (R.ρ τ) (f τ) = flucPair (X 0 ω) (R.ρ 0) (f 0) +
        empiricalMartingale P ℱ W' R.D t f X (Real.toNNReal τ) ω +
        ∫ r in (0 : ℝ)..τ, flucInteraction R.D (f r) (X (Real.toNNReal r) ω) (R.ρ r) := by
  have hd : 1 ≤ d := le_trans (by norm_num) R.hd
  have hN0 : 0 < N := hN
  have : NeZero N := ⟨by omega⟩
  have hsol := hreal.solution T
  obtain ⟨Λ, hΛ⟩ := HRS.MC.RegSet.reg_proof R 3
  exact S7PIF1_duality_identity_all hd hN0 (D := R.D) (ℱ := ℱ) (W' := W') (by
      exact ContDiff.of_le (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift R.D.V) from R.hV)
        (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))
    (R.mf T hT) (hΛ T) hsol.toContact hF (Or.inr (HRS.GF.nullContactOccupation_of_strong hsol)) ht hφ hf

end Prob

end HRS.MC.Sec7.S7PIF1

end
