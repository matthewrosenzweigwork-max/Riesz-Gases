/-
# HRS.Equilibrium.Q84eAuxI — packet Q84e: the centred identity of `normal_form`

From the pointwise identity `q84e_pointwise`, stationarity `E 𝓛F_N(ψ) = 0` (`q84d_stationarity`) and
integrability of every term, the identity with the actual stationary centring of every term.
-/
import HRS.Equilibrium.Q84eAuxH

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.Q84e

open HRS.Q84d

variable {d : ℕ} {s : ℝ} {N : ℕ}

/-- Abstract centring: an a.e. identity with a constant, valid pointwise at `X`, centres. -/
theorem q84e_center {α : Type*} [MeasurableSpace α] (P : Measure α) [IsProbabilityMeasure P]
    {Q G E A : α → ℝ} (hQ : Integrable Q P) (hG : Integrable G P) (hE : Integrable E P)
    (hA : Integrable A P) (hG0 : ∫ x, G x ∂P = 0) {r k c : ℝ}
    (hae : ∀ᵐ x ∂P, r * Q x = -G x + E x - k * A x + c) (X : α)
    (hX : r * Q X = -G X + E X - k * A X + c) :
    r * (Q X - ∫ x, Q x ∂P) = -G X + (E X - ∫ x, E x ∂P) - k * (A X - ∫ x, A x ∂P) := by
  have h1 : ∫ x, r * Q x ∂P = ∫ x, (-G x + E x - k * A x + c) ∂P := integral_congr_ae hae
  rw [integral_const_mul] at h1
  have h2 : ∫ x, (-G x + E x - k * A x + c) ∂P = -∫ x, G x ∂P + ∫ x, E x ∂P - k * ∫ x, A x ∂P + c := by
    have i1 : Integrable (fun x => -G x + E x) P := hG.neg.add hE
    have i2 : Integrable (fun x => -G x + E x - k * A x) P := i1.sub (hA.const_mul k)
    rw [integral_add i2 (integrable_const c), integral_sub i1 (hA.const_mul k),
      integral_add (f := fun x => -G x) hG.neg hE, integral_neg, integral_const_mul]
    simp
  rw [h2, hG0] at h1
  linarith

theorem q84e_integrable_avg (hsd : s < d) {ρ : Torus d → ℝ} (hρs : SmoothPosDensity ρ)
    {f : Torus d → ℝ} (hf : Torus.IsSmooth f) (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {P : Measure (Config d N)}
    [IsProbabilityMeasure P] :
    Integrable (fun Y : Config d N => (1 / (N : ℝ)) * ∑ i, aCoef d s ρ f (Y i)) P := by
  obtain ⟨Ca, hCa0, hCa⟩ := q84d_aCoef_bound hd hcrit hρs
  have hm := q84d_measurable_aCoef hsd hρs.density hf
  have hFm : Measurable (fun Y : Config d N => (1 / (N : ℝ)) * ∑ i, aCoef d s ρ f (Y i)) :=
    measurable_const.mul (Finset.measurable_sum _ fun i _ => hm.comp (measurable_pi_apply i))
  refine Integrable.of_bound (C := |(1 / (N : ℝ))| * (N * (Ca * posSeminorm (8 * d + 80) f)))
    hFm.aestronglyMeasurable (Filter.Eventually.of_forall fun Y => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  calc |∑ i, aCoef d s ρ f (Y i)| ≤ ∑ i, |aCoef d s ρ f (Y i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, Ca * posSeminorm (8 * d + 80) f := Finset.sum_le_sum fun i _ => hCa hf _
    _ = N * (Ca * posSeminorm (8 * d + 80) f) := by simp

theorem q84e_identity_centered (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {V : Torus d → ℝ} {β : ℝ}
    {ρ : Torus d → ℝ} (hβ : 0 < β) (hV : Torus.IsSmooth V)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (hρs : SmoothPosDensity ρ)
    {f : Torus d → ℝ} {K₁ : ℝ} {ψ : Torus d → Torus d → ℝ} (hf : Torus.IsSmooth f)
    (hψ : IsPairCorrector d s V β ρ f K₁ ψ) (hN : 2 ≤ N) :
    ∀ X : Config d N, X ∉ collisionSet d N →
      Real.sqrt N / 2 * centeredUnder (canonicalGibbs (periodicRiesz d s) V N β)
          (quadStat (hTransport d s f) (withDensityReal ρ)) X =
        -particleGen d s V β (Fstat ψ) X +
          centeredUnder (canonicalGibbs (periodicRiesz d s) V N β) (errStat d s ρ ψ) X -
          (2 / (N : ℝ)) * (Real.sqrt N * centeredUnder (canonicalGibbs (periodicRiesz d s) V N β)
            (fun Y : Config d N => (1 / (N : ℝ)) * ∑ i, aCoef d s ρ f (Y i)) X) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by rw [hcrit]; linarith
  have hN1 : 1 ≤ N := by omega
  haveI := q84d_isProb hd hcrit hV hβ hN1 (N := N)
  set P := canonicalGibbs (periodicRiesz d s) V N β with hP
  have hQ := q84d_quadStat_integrable hd hcrit β hβ V hV ρ hρ hρs f hf N hN
  have hE := q84d_errStat_integrable hd hcrit β hβ V hV ρ hρ hρs f K₁ ψ hf hψ N hN
  obtain ⟨hG, hG0⟩ := q84d_stationarity hd hcrit β hβ V hV ρ hρ hρs f K₁ ψ hf hψ N hN
  have hA := q84e_integrable_avg (N := N) (P := P) hsd hρs hf hd hcrit
  have hcoll : ∀ᵐ X ∂P, X ∉ collisionSet d N :=
    q84d_gibbs_ac.ae_le (q84d_ae_not_collision (N := N) (d := d) (by omega))
  set c₀ := ∫ x', ∫ y', hTransport d s f x' y' ∂(withDensityReal ρ) ∂(withDensityReal ρ) with hc₀
  intro X hX
  have hpt := fun Y (hY : Y ∉ collisionSet d N) => q84e_pointwise hd hcrit hβ hV hρ hρs hψ hN Y hY
  have key := q84e_center P hQ hG hE hA hG0 (r := Real.sqrt N / 2)
    (k := (2 / (N : ℝ)) * Real.sqrt N) (c := (1 / (2 * Real.sqrt N)) * c₀)
    (hcoll.mono fun Y hY => by have := hpt Y hY; linarith) X (by have := hpt X hX; linarith)
  unfold centeredUnder
  linarith

end HRS.Q84e

end
