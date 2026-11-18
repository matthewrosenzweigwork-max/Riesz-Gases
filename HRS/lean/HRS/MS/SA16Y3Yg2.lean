import HRS.MS.SA16Y3Yg1
import HRS.MS.SA16StrongSL4

/-!
# S.A.16 (SA16Y3) Yg2: jets of a mollified smooth compactly supported function (for SA16S item (iii))

`sa16y3_conv_fderiv`: for `η` integrable and `g ∈ C_c^∞`, `∂_v (∫ η(y) g(· - y)) = ∫ η(y) (∂_v g)(· - y)`.
`sa16y3_conv_pd`: the same for every multi-index derivative `partialDeriv κ`.
`sa16y3_conv_jet_le`: `‖∂^κ (η ⋆ g)‖_{L^p} ≤ (∫⁻|η|) ‖∂^κ g‖_{L^p}` (Young, `sa16y3_young_eLp`).
Consequence: for `∫⁻|η| ≤ 1` (a mollifier) every derivative of `η ⋆ g` is bounded in `L^p` by that of `g`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff Convolution

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16

section Yg2
variable {d : ℕ}

lemma sa16y3_conv_eq (η g : EuclideanSpace ℝ (Fin d) → ℝ) :
    (fun x => ∫ y, η y * g (x - y)) = η ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g := by
  funext x
  simp [convolution, smul_eq_mul]

lemma sa16y3_conv_contDiff {η g : EuclideanSpace ℝ (Fin d) → ℝ} (hη : LocallyIntegrable η volume)
    (hg : IsCcInfty g) : ContDiff ℝ ∞ (fun x => ∫ y, η y * g (x - y)) := by
  rw [sa16y3_conv_eq]
  exact hg.2.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hη hg.1

lemma sa16y3_conv_fderiv {η g : EuclideanSpace ℝ (Fin d) → ℝ} (hη : Integrable η volume) (hg : IsCcInfty g)
    (x v : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (fun x => ∫ y, η y * g (x - y)) x v = ∫ y, η y * fderiv ℝ g (x - y) v := by
  have hdiff := HasCompactSupport.hasFDerivAt_convolution_right (μ := volume)
    (L := ContinuousLinearMap.lsmul ℝ ℝ) hg.2 hη.locallyIntegrable (hg.1.of_le (by simp)) x
  have hcg' : HasCompactSupport (fderiv ℝ g) := hg.2.fderiv ℝ
  have hcont' : Continuous (fderiv ℝ g) := hg.1.continuous_fderiv (by simp)
  have hconv := hcg'.convolutionExists_right ((ContinuousLinearMap.lsmul ℝ ℝ).precompR
    (EuclideanSpace ℝ (Fin d))) hη.locallyIntegrable hcont'
  rw [sa16y3_conv_eq, hdiff.fderiv]
  simp only [convolution]
  rw [ContinuousLinearMap.integral_apply (hconv x)]
  congr 1

lemma sa16y3_conv_pd {η : EuclideanSpace ℝ (Fin d) → ℝ} (hη : Integrable η volume) {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hψ : IsCcInfty ψ) {j : ℕ} (κ : Fin j → Fin d) :
    partialDeriv κ (fun x => ∫ y, η y * ψ (x - y)) = fun x => ∫ y, η y * partialDeriv κ ψ (x - y) := by
  induction j generalizing ψ with
  | zero =>
    funext x
    simp only [partialDeriv, iteratedFDeriv_zero_apply]
  | succ j ih =>
    obtain ⟨i, κ', rfl⟩ : ∃ (i : Fin d) (κ' : Fin j → Fin d), κ = Fin.cons i κ' :=
      ⟨κ 0, Fin.tail κ, (Fin.cons_self_tail κ).symm⟩
    funext x
    rw [sa16s_pd_cons (sa16y3_conv_contDiff hη.locallyIntegrable hψ) i κ' x, ih hψ κ']
    rw [sa16y3_conv_fderiv hη (sa16s_cc_partialDeriv hψ κ') x]
    congr 1
    funext y
    rw [sa16s_pd_cons hψ.1 i κ' (x - y)]

lemma sa16y3_conv_jet_le {p : ℝ} (hp : 1 ≤ p) {η : EuclideanSpace ℝ (Fin d) → ℝ} (hη : Integrable η volume)
    (hηm : Measurable η) {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ) {j : ℕ} (κ : Fin j → Fin d) :
    eLpNorm (partialDeriv κ (fun x => ∫ y, η y * ψ (x - y))) (ENNReal.ofReal p) volume ≤
      (∫⁻ y, ‖η y‖ₑ) * eLpNorm (partialDeriv κ ψ) (ENNReal.ofReal p) volume := by
  rw [sa16y3_conv_pd hη hψ κ]
  exact sa16y3_young_eLp hp η (partialDeriv κ ψ) hηm (sa16s_cc_partialDeriv hψ κ).1.continuous.measurable

lemma sa16y3_conv_jet_le_one {p : ℝ} (hp : 1 ≤ p) {η : EuclideanSpace ℝ (Fin d) → ℝ} (hη : Integrable η volume)
    (hηm : Measurable η) (hη1 : ∫⁻ y, ‖η y‖ₑ ≤ 1) {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ)
    {j : ℕ} (κ : Fin j → Fin d) :
    eLpNorm (partialDeriv κ (fun x => ∫ y, η y * ψ (x - y))) (ENNReal.ofReal p) volume ≤
      eLpNorm (partialDeriv κ ψ) (ENNReal.ofReal p) volume := by
  refine (sa16y3_conv_jet_le hp hη hηm hψ κ).trans ?_
  calc (∫⁻ y, ‖η y‖ₑ) * eLpNorm (partialDeriv κ ψ) (ENNReal.ofReal p) volume
      ≤ 1 * eLpNorm (partialDeriv κ ψ) (ENNReal.ofReal p) volume := mul_le_mul' hη1 le_rfl
    _ = eLpNorm (partialDeriv κ ψ) (ENNReal.ofReal p) volume := one_mul _

end Yg2

end HRS.Whole.AppendixA.Phase2SA16R
