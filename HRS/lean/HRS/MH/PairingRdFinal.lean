import HRS.MH.PairingRdP1
import HRS.MH.PairingRdP5
import HRS.MH.PairingRdP8
import HRS.MH.PairingRdP9
import HRS.MH.PairingRdP11
import HRS.MH.PairingRdP12
import HRS.MH.PairingRdP13

/-!
# PairingRd packet PR14 (`pairing_expansion_rd_proof`): assembly of Lemma 3.1 on `ℝ^d`

Mirrors the torus proof `HRS.Duality.pairing_expansion` (`HRS/Duality/PairingExpansion.lean:600-763`), using only the
proved packets `HRS.MH.PairingRdP.*`.  The data (Hölder, convolution integrability/bounds, boundedness of `φ₁, φ₂`)
are collected in `pr14_psi_facts` and `pr14_conv_data`; the statement is the frozen `HRS.Duality.pairing_expansion_rd`
through `type_of%`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MH.PairingRdP

open HRS HRS.Duality
open HRS.MH.PairingRd (convInt psiRd)

variable {d N : ℕ}

/-- Measurability, integrability and near-field Hölder bound (exponent `β ≤ 1`) of `ψ_a = ρ (Mᵀ ∇f)_a`. -/
theorem pr14_psi_facts (M : Matrix (Fin d) (Fin d) ℝ) {f : Euc d → ℝ} (hf : MemCb 2 f) {ρ : Euc d → ℝ}
    (hρm : Measurable ρ) (hρint : Integrable ρ) {Bρ Cρ β : ℝ} (hBρ : ∀ x, |ρ x| ≤ Bρ) (hCρ : 0 ≤ Cρ)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hρH : ∀ x z : Euc d, ‖z‖ ≤ 1 / 4 → |ρ (x - z) - ρ x| ≤ Cρ * ‖z‖ ^ β) (a : Fin d) :
    Measurable (psiRd f M ρ a) ∧ Integrable (psiRd f M ρ a) ∧
      ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ x z : Euc d, ‖z‖ ≤ 1 / 4 →
        |psiRd f M ρ a (x - z) - psiRd f M ρ a x| ≤ Λ * ‖z‖ ^ β := by
  obtain ⟨Bv, Lv, hBv0, hLv0, hvc, hBv, hLv⟩ := vcomp_facts_rd M hf a
  have hBρ0 : 0 ≤ Bρ := (abs_nonneg _).trans (hBρ 0)
  have hmeas : Measurable (psiRd f M ρ a) := hρm.mul hvc.measurable
  refine ⟨hmeas, ?_, Cρ * Bv + Bρ * Lv, by positivity, fun x z hz => ?_⟩
  · refine (hρint.norm.const_mul Bv).mono' hmeas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun y => ?_
    simp only [psiRd, norm_mul, Real.norm_eq_abs]
    nlinarith [hBv y, abs_nonneg (ρ y)]
  · exact holder_mul_near_rd hβ0 hβ1 hCρ hLv0 hBρ hBv hρH hLv x z hz

/-- Claims 4, 5 (integrability of the cancellation integrands) and the measurable, uniformly bounded
test functions `φ₁`, `φ₂`. -/
theorem pr14_conv_data (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (M : Matrix (Fin d) (Fin d) ℝ) {f : Euc d → ℝ} (hf : MemCb 2 f) {ρ : Euc d → ℝ}
    (hρ : Whole.IsProbDensity ρ) {Bρ Cρ β : ℝ} (hBρ : ∀ x, |ρ x| ≤ Bρ) (hCρ : 0 ≤ Cρ)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hβ : s + 1 - d < β)
    (hρH : ∀ x z : Euc d, ‖z‖ ≤ 1 / 4 → |ρ (x - z) - ρ x| ≤ Cρ * ‖z‖ ^ β) :
    (∀ x, Integrable (convInt (Whole.rieszKernelGrad d s) ρ x)) ∧
      (∀ (a : Fin d) x, Integrable (convInt (Whole.rieszKernelGrad d s) (psiRd f M ρ a) x)) ∧
      Measurable (fun x => inner ℝ (gradient f x)
        (Torus.matVec M (Whole.convGradConvW (Whole.rieszKernelGrad d s) ρ x))) ∧
      Measurable (divConvBRd f M s ρ) ∧
      ∃ K : ℝ, ∀ x, |inner ℝ (gradient f x)
          (Torus.matVec M (Whole.convGradConvW (Whole.rieszKernelGrad d s) ρ x))| ≤ K ∧
        |divConvBRd f M s ρ x| ≤ K := by
  have hρint : Integrable ρ := HRS.MH.DualityRd.db1_prob_integrable hρ
  obtain ⟨hρ4, hρK⟩ := integrable_conv_rd hd hs0 hsd hρ.measurable hρint hCρ hβ hρH
  have hψ := fun a => pr14_psi_facts M hf hρ.measurable hρint hBρ hCρ hβ0 hβ1 hρH a
  have hψ5 : ∀ a : Fin d, (∀ x, Integrable (convInt (Whole.rieszKernelGrad d s) (psiRd f M ρ a) x)) ∧
      ∃ K : ℝ, ∀ x, ‖Whole.convGradConvW (Whole.rieszKernelGrad d s) (psiRd f M ρ a) x‖ ≤ K := by
    intro a
    obtain ⟨hm, hi, Λ, hΛ0, hΛ⟩ := hψ a
    exact integrable_conv_rd hd hs0 hsd hm hi hΛ0 hβ hΛ
  exact ⟨hρ4, fun a => (hψ5 a).1, phi_bounded_rd M hf hρ.measurable hρK (fun a => (hψ5 a).2)⟩

/-- **PR14**: assembly of `HRS.Duality.pairing_expansion_rd`. -/
theorem pairing_expansion_rd_proof : type_of% @HRS.Duality.pairing_expansion_rd := by
  intro d N hd s hs0 hsd M f hf ρ hρ hρb C α hα0 hα1 hα hHol hmom hN X hX μ μN φ₁ φ₂
  have hN' : 0 < N := hN
  have hC0 : (0 : ℝ) ≤ C := C.2
  obtain ⟨hρc, hρH⟩ := holder_near_rd hα0 hHol
  obtain ⟨Bρ, hBρ⟩ := hρb
  have hρle : ∀ x, ρ x ≤ Bρ := fun x => (le_abs_self _).trans (hBρ x)
  have : IsProbabilityMeasure μ := Whole.Q09A.measure_isProb hρ
  have : IsProbabilityMeasure μN := Whole.empirical_isProbabilityMeasure hN' X
  obtain ⟨hc4, hc5, hφ1m, hφ2m, K, hK⟩ :=
    pr14_conv_data hd hs0 hsd M hf hρ hBρ hC0 hα0.le hα1 hα hρH
  have hφ1i : ∀ ν : Measure (Euc d), IsFiniteMeasure ν → Integrable φ₁ ν := fun ν _ =>
    Integrable.of_bound hφ1m.aestronglyMeasurable K
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact (hK x).1)
  have hφ2i : ∀ ν : Measure (Euc d), IsFiniteMeasure ν → Integrable φ₂ ν := fun ν _ =>
    Integrable.of_bound hφ2m.aestronglyMeasurable K
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact (hK x).2)
  have hsymm : ∀ x y, pairKernelRdB f M s y x = pairKernelRdB f M s x y :=
    fun x y => pairKernelRdB_symm_rd M f x y
  have K1 : Integrable (fun p : Euc d × Euc d => pairKernelRdB f M s p.1 p.2) (μ.prod μ) :=
    pairKernelRdB_integrable_prod_rd hd hs0 hsd M hf hρ hρle μ
  have K2 : Integrable (fun p : Euc d × Euc d => pairKernelRdB f M s p.1 p.2) (μN.prod μ) :=
    pairKernelRdB_integrable_prod_rd hd hs0 hsd M hf hρ hρle μN
  have K3 : Integrable (fun p : Euc d × Euc d => pairKernelRdB f M s p.1 p.2) (μ.prod μN) :=
    (K2.swap).congr (Filter.Eventually.of_forall fun p => hsymm p.1 p.2)
  have hint : ∀ x, ∫ y, pairKernelRdB f M s x y ∂μ = (1 / 2 : ℝ) * (φ₁ x - φ₂ x) := fun x =>
    integral_pairKernel_eq_rd M hρ x (hc4 x) (fun a => hc5 a x)
  exact ⟨⟨K1, K2, K3, hc4, hc5, hφ1i μ inferInstance, hφ2i μ inferInstance⟩,
    pairing_identity_rd M f hρ hN' X φ₁ φ₂ K1 K2 hsymm hint (hφ1i μ inferInstance) (hφ2i μ inferInstance)
      (hφ1i μN inferInstance) (hφ2i μN inferInstance)⟩

end HRS.MH.PairingRdP
