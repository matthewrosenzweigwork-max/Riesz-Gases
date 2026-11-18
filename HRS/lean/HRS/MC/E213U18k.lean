import HRS.MC.E213U18j
import HRS.MC.S7S7e
import HRS.MC.S7S7a
import HRS.MC.S7FCD3BLaw
import HRS.MC.E213L

/-!
# Packet e213u18 (part k): `ℓ_x(ψ) = (R P ψ)(x)` and interchange of `Kop` with uniformly convergent series

For the field `ℓ_x = ellPt` of the initial fluctuation and a smooth test function `ψ`: `⟨ℓ_x, ψ⟩ = responseRep ψ x`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U18

open HRS HRS.Sec7 HRS.Main

variable {d : ℕ}

section KopSeries

variable {g ρ : Torus d → ℝ}

theorem u18_mu_le {Λ : ℝ} (hΛ : ∀ x, ρ x ≤ Λ) :
    withDensityReal ρ ≤ ENNReal.ofReal Λ • (volume : Measure (Torus d)) := by
  unfold withDensityReal
  rw [← withDensity_const]
  exact withDensity_mono (Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal (hΛ x))

theorem u18_slice_int (hgi : Integrable g) {Λ : ℝ} (hΛ : ∀ x, ρ x ≤ Λ) (x : Torus d) :
    Integrable (fun z => g (x - z)) (withDensityReal ρ) :=
  ((hgi.comp_sub_left x).smul_measure ENNReal.ofReal_ne_top).mono_measure (u18_mu_le hΛ)

theorem u18_slice_L1 (hgi : Integrable g) {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : ∀ x, ρ x ≤ Λ) (x : Torus d) :
    ∫ z, |g (x - z)| ∂(withDensityReal ρ) ≤ Λ * ∫ z, |g z| := by
  have h1 : ∫ z, |g (x - z)| ∂(withDensityReal ρ) ≤
      ∫ z, |g (x - z)| ∂(ENNReal.ofReal Λ • (volume : Measure (Torus d))) :=
    integral_mono_measure (u18_mu_le hΛ) (Eventually.of_forall fun z => abs_nonneg _)
      ((hgi.comp_sub_left x).abs.smul_measure ENNReal.ofReal_ne_top)
  rw [integral_smul_measure, ENNReal.toReal_ofReal hΛ0, smul_eq_mul,
    integral_sub_left_eq_self (fun z => |g z|) volume x] at h1
  exact h1

theorem u18_phi_hasSum {ι : Type*} [Countable ι] (hgi : Integrable g) {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ x, ρ x ≤ Λ) (f : ι → Torus d → ℝ) (hf : ∀ k, Continuous (f k)) {w : ι → ℝ}
    (hw : Summable w) (hb : ∀ k z, |f k z| ≤ w k) (x : Torus d) :
    HasSum (fun k => HRS.PDE.MFLinear.Phi g ρ (f k) x)
      (HRS.PDE.MFLinear.Phi g ρ (fun z => ∑' k, f k z) x) := by
  have hw0 : ∀ k, 0 ≤ w k := fun k => (abs_nonneg _).trans (hb k (Classical.arbitrary _))
  have hsl := u18_slice_int hgi hΛ x
  have hint : ∀ k, Integrable (fun z => g (x - z) * f k z) (withDensityReal ρ) := fun k => by
    refine Integrable.mono' (hsl.norm.mul_const (w k))
      (hsl.aestronglyMeasurable.mul (hf k).aestronglyMeasurable) (Eventually.of_forall fun z => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (by simpa using hb k z) (norm_nonneg _)
  have hsum : Summable fun k => ∫ z, ‖g (x - z) * f k z‖ ∂(withDensityReal ρ) := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun z => norm_nonneg _) (fun k => ?_)
      (hw.mul_left (Λ * ∫ z, |g z|))
    calc ∫ z, ‖g (x - z) * f k z‖ ∂(withDensityReal ρ)
        ≤ ∫ z, ‖g (x - z)‖ * w k ∂(withDensityReal ρ) := by
          refine integral_mono (hint k).norm (hsl.norm.mul_const _) fun z => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (by simpa using hb k z) (norm_nonneg _)
      _ = (∫ z, |g (x - z)| ∂(withDensityReal ρ)) * w k := by
          rw [integral_mul_const]
          simp only [Real.norm_eq_abs]
      _ ≤ (Λ * ∫ z, |g z|) * w k := mul_le_mul_of_nonneg_right (u18_slice_L1 hgi hΛ0 hΛ x) (hw0 k)
  have := hasSum_integral_of_summable_integral_norm hint hsum
  simp_rw [tsum_mul_left] at this
  exact this

theorem u18_kop_hasSum {ι : Type*} [Countable ι] {Λ : ℝ} (hKS : HRS.PDE.MFLinear.KS g ρ Λ) (hΛ0 : 0 ≤ Λ)
    (f : ι → Torus d → ℝ) (hf : ∀ k, Continuous (f k)) {w : ι → ℝ} (hw : Summable w)
    (hb : ∀ k z, |f k z| ≤ w k) (y : Torus d) :
    HasSum (fun k => Kop g (withDensityReal ρ) (f k) y)
      (Kop g (withDensityReal ρ) (fun z => ∑' k, f k z) y) := by
  haveI := hKS.isProb
  have hw0 : ∀ k, 0 ≤ w k := fun k => (abs_nonneg _).trans (hb k (Classical.arbitrary _))
  have h1 := fun x => u18_phi_hasSum hKS.int hΛ0 hKS.bd f hf hw hb x
  have hfi : ∀ k, Integrable (f k) (withDensityReal ρ) := fun k =>
    HRS.MC.E213L.e213l_integrable (μ := withDensityReal ρ) (hf k)
  have hPint : ∀ k, Integrable (HRS.PDE.MFLinear.Phi g ρ (f k)) (withDensityReal ρ) := fun k =>
    HRS.PDE.MFLinear.integrable_Phi hKS (hfi k)
  have hPb : ∀ k x, ‖HRS.PDE.MFLinear.Phi g ρ (f k) x‖ ≤ (Λ * ∫ z, |g z|) * w k := by
    intro k x
    have hsl := u18_slice_int hKS.int hKS.bd x
    have hint : Integrable (fun z => g (x - z) * f k z) (withDensityReal ρ) := by
      refine Integrable.mono' (hsl.norm.mul_const (w k))
        (hsl.aestronglyMeasurable.mul (hf k).aestronglyMeasurable) (Eventually.of_forall fun z => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (by simpa using hb k z) (norm_nonneg _)
    unfold HRS.PDE.MFLinear.Phi
    calc ‖∫ z, g (x - z) * f k z ∂(withDensityReal ρ)‖ ≤ ∫ z, ‖g (x - z) * f k z‖ ∂(withDensityReal ρ) :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ z, ‖g (x - z)‖ * w k ∂(withDensityReal ρ) := by
          refine integral_mono hint.norm (hsl.norm.mul_const _) fun z => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (by simpa using hb k z) (norm_nonneg _)
      _ = (∫ z, |g (x - z)| ∂(withDensityReal ρ)) * w k := by
          rw [integral_mul_const]
          simp only [Real.norm_eq_abs]
      _ ≤ (Λ * ∫ z, |g z|) * w k :=
          mul_le_mul_of_nonneg_right (u18_slice_L1 hKS.int hΛ0 hKS.bd x) (hw0 k)
  have hPsum : Summable fun k => ∫ x, ‖HRS.PDE.MFLinear.Phi g ρ (f k) x‖ ∂(withDensityReal ρ) := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun z => norm_nonneg _) (fun k => ?_)
      (hw.mul_left (Λ * ∫ z, |g z|))
    calc ∫ x, ‖HRS.PDE.MFLinear.Phi g ρ (f k) x‖ ∂(withDensityReal ρ)
        ≤ ∫ x, (Λ * ∫ z, |g z|) * w k ∂(withDensityReal ρ) :=
          integral_mono (hPint k).norm (integrable_const _) (hPb k)
      _ = (Λ * ∫ z, |g z|) * w k := by simp
  have h2 := hasSum_integral_of_summable_integral_norm hPint hPsum
  have e : (fun x => ∑' k, HRS.PDE.MFLinear.Phi g ρ (f k) x) =
      HRS.PDE.MFLinear.Phi g ρ (fun z => ∑' k, f k z) := funext fun x => (h1 x).tsum_eq
  rw [e] at h2
  have h3 := (h1 y).sub h2
  simp only [HRS.PDE.MFLinear.kop_eq_Phi]
  exact h3

end KopSeries

end HRS.MC.E213U18

end
