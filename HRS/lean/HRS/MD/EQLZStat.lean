import HRS.MD.EQLZVocab
import HRS.MD.EQLZDet

/-!
# EQ-LZ packet STAT: marginals and increments of a stationary `HasFDD` process (`eqlz_stat`), proof

`HasFDD` with `g₀ = 1` and the lists `[]`, `[(t, g)]`, `[(a, φ), (δ, φ)]` gives the total mass of `π`, the identity
`E g(Z_t) = ∫ g dπ` for smooth `g` (invariance `hinv`), and `E φ(Z_a) φ(Z_{a+δ}) = ∫ φ P_δ φ dπ`; smooth test
functions determine finite measures on the torus (`lzdet_ext_single`).  The hypotheses `hsm`, `hinv` are
explicit hypotheses of the statement (the types of the SG packet theorems).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal
open HRS HRS.MD.EQLZ HRS.MD.EQLZDet

namespace HRS.MD.EQLZStat

variable {n : ℕ}

theorem eqlz_stat_proof (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
    (hsm : ∀ t : ℝ, 0 ≤ t → ∀ φ : Torus n → ℝ, Torus.IsSmooth φ → Torus.IsSmooth (d1_P hn hκ hU t φ))
    (hinv : ∀ t : ℝ, 0 ≤ t → ∀ φ : Torus n → ℝ, Torus.IsSmooth φ →
      ∫ x, d1_P hn hκ hU t φ x ∂(d1_gibbsMeasure κ U) = ∫ x, φ x ∂(d1_gibbsMeasure κ U))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℝ → Ω → Torus n)
    (hZ : ∀ t : ℝ, 0 ≤ t → Measurable (Z t)) (hfdd : HasFDD hn hκ hU P Z (d1_gibbsMeasure κ U)) :
    (∀ t : ℝ, 0 ≤ t → P.map (Z t) = d1_gibbsMeasure κ U) ∧
      ∀ a δ : ℝ, 0 ≤ a → 0 ≤ δ → ∀ φ : Torus n → ℝ, Torus.IsSmooth φ →
        ∫ ω, (φ (Z (a + δ) ω) - φ (Z a ω)) ^ 2 ∂P =
          2 * ∫ x, φ x * (φ x - d1_P hn hκ hU δ φ x) ∂(d1_gibbsMeasure κ U) := by
  set π := d1_gibbsMeasure κ U with hπ
  have hmass : IsProbabilityMeasure π := by
    have h := hfdd [] (by simp) (fun _ => 1) measurable_const ⟨1, fun _ => by simp⟩
    simp only [fddProd, fddKer, mul_one] at h
    rw [integral_const, integral_const] at h
    simp only [smul_eq_mul, mul_one, probReal_univ] at h
    refine ⟨?_⟩
    have h2 : π.real Set.univ = 1 := h.symm
    rw [measureReal_def] at h2
    have h3 : π Set.univ ≠ ∞ := by
      intro h4; rw [h4] at h2; simp at h2
    exact (ENNReal.toReal_eq_one_iff _).mp h2
  have hmarg_int : ∀ t, 0 ≤ t → ∀ g : Torus n → ℝ, Torus.IsSmooth g → ∫ ω, g (Z t ω) ∂P = ∫ x, g x ∂π := by
    intro t ht g hg
    have h := hfdd [(t, g)] (by simpa using ⟨ht, hg⟩) (fun _ => 1) measurable_const ⟨1, fun _ => by simp⟩
    simp only [fddProd, fddKer, one_mul, mul_one, zero_add] at h
    exact h.trans (hinv t ht g hg)
  have hlaw : ∀ t, 0 ≤ t → P.map (Z t) = π := by
    intro t ht
    apply lzdet_ext_single
    intro g hg
    rw [integral_map (hZ t ht).aemeasurable (lzdet_continuous hg).aestronglyMeasurable]
    exact hmarg_int t ht g hg
  refine ⟨hlaw, ?_⟩
  intro a δ ha hδ φ hφ
  have hφc := lzdet_continuous hφ
  have hPφ : Torus.IsSmooth (d1_P hn hκ hU δ φ) := hsm δ hδ φ hφ
  have hPφc := lzdet_continuous hPφ
  have hmc : ∀ t, 0 ≤ t → ∀ f : Torus n → ℝ, Continuous f → ∫ ω, f (Z t ω) ∂P = ∫ x, f x ∂π := by
    intro t ht f hf
    rw [← integral_map (hZ t ht).aemeasurable hf.aestronglyMeasurable, hlaw t ht]
  have hcross : ∫ ω, φ (Z a ω) * φ (Z (a + δ) ω) ∂P = ∫ x, φ x * d1_P hn hκ hU δ φ x ∂π := by
    have h := hfdd [(a, φ), (δ, φ)] (by simpa using ⟨⟨ha, hφ⟩, hδ, hφ⟩) (fun _ => 1) measurable_const
      ⟨1, fun _ => by simp⟩
    simp only [fddProd, fddKer, one_mul, mul_one, zero_add] at h
    exact h.trans (hinv a ha _ (lzdet_smooth_mul hφ hPφ))
  have hδa : 0 ≤ a + δ := by linarith
  have e1 : (fun ω => (φ (Z (a + δ) ω) - φ (Z a ω)) ^ 2) =
      fun ω => φ (Z (a + δ) ω) ^ 2 + φ (Z a ω) ^ 2 - 2 * (φ (Z a ω) * φ (Z (a + δ) ω)) := by
    funext ω; ring
  rw [e1]
  have i1 : Integrable (fun ω => φ (Z (a + δ) ω) ^ 2) P :=
    lzdet_integrable_comp P (f := fun x => φ x ^ 2) (hφc.pow 2) (hZ _ hδa)
  have i2 : Integrable (fun ω => φ (Z a ω) ^ 2) P :=
    lzdet_integrable_comp P (f := fun x => φ x ^ 2) (hφc.pow 2) (hZ _ ha)
  have i3 : Integrable (fun ω => φ (Z a ω) * φ (Z (a + δ) ω)) P :=
    lzdet_integrable_comp P (f := fun q : Torus n × Torus n => φ q.1 * φ q.2)
      ((hφc.comp continuous_fst).mul (hφc.comp continuous_snd))
      (Z := fun ω => (Z a ω, Z (a + δ) ω)) ((hZ _ ha).prodMk (hZ _ hδa))
  have j1 : Integrable (fun x => φ x ^ 2) π := lzdet_integrable_cont (hφc.pow 2) π
  have j2 : Integrable (fun x => φ x * d1_P hn hκ hU δ φ x) π :=
    lzdet_integrable_cont (hφc.mul hPφc) π
  have i12 : Integrable (fun ω => φ (Z (a + δ) ω) ^ 2 + φ (Z a ω) ^ 2) P := i1.add i2
  rw [integral_sub i12 (i3.const_mul 2), integral_add i1 i2, integral_const_mul, hcross,
    hmc _ hδa (fun x => φ x ^ 2) (hφc.pow 2), hmc _ ha (fun x => φ x ^ 2) (hφc.pow 2)]
  have e2 : ∫ x, φ x * (φ x - d1_P hn hκ hU δ φ x) ∂π =
      ∫ x, φ x ^ 2 ∂π - ∫ x, φ x * d1_P hn hκ hU δ φ x ∂π := by
    rw [← integral_sub j1 j2]
    congr 1; funext x; ring
  rw [e2]
  ring

end HRS.MD.EQLZStat

end
