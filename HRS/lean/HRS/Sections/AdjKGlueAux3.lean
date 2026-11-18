import HRS.Sections.AdjKGlueAux2

/-!
# ADJK-GLUE, part 3: assembly of `moving_integrated_forcing` (Lemma 5.8, third assertion)
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

universe u

namespace HRS.AdjK

open HRS.Uniform

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem adjkg_enorm_sq (x : ℝ) : ‖x‖ₑ ^ 2 = ENNReal.ofReal (x ^ 2) := by
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]

/-- Per-mode second moment of the forcing, from the `L²` pair moment of `N F`. -/
theorem adjkg_Y_L2 {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) {N : ℕ} (hN : 0 < N)
    (X : ℝ≥0 → Ω → Config d N) (j : NonzeroLattice d) {r : ℝ} (hr : 0 ≤ r)
    (hmeasY : Measurable (fun ω => adjkgY s ρ X j r ω)) {a : ℝ} (ha : 0 ≤ a)
    (hLp : eLpNorm (fun ω => (N : ℝ) * modulatedEnergy
      (commKernel (periodicRieszGrad d s) (Torus.grad (Torus.realMode j))) (X r.toNNReal ω)
      (withDensityReal (ρ r))) (ENNReal.ofReal 2) P ≤ ENNReal.ofReal a) :
    ∫⁻ ω, ‖adjkgY s ρ X j r ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal ((a / Real.sqrt N) ^ 2) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.2 hNr
  set f : Ω → ℝ := fun ω => (N : ℝ) * modulatedEnergy
      (commKernel (periodicRieszGrad d s) (Torus.grad (Torus.realMode j))) (X r.toNNReal ω)
      (withDensityReal (ρ r)) with hf
  have hyf : ∀ ω, adjkgY s ρ X j r ω = -(1 / Real.sqrt N) * f ω := by
    intro ω
    simp only [adjkgY, if_pos hr, hf]
    field_simp
    rw [Real.sq_sqrt hNr.le]
    ring
  have hfm : Measurable f := by
    have : f = fun ω => -Real.sqrt N * adjkgY s ρ X j r ω := by
      funext ω
      rw [hyf ω]
      field_simp
    rw [this]
    exact hmeasY.const_mul _
  have h1 : ∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂P = (eLpNorm f (ENNReal.ofReal 2) P) ^ 2 := by
    have h2 : ENNReal.ofReal 2 = ((2 : ℝ≥0) : ℝ≥0∞) := by norm_num
    have := eLpNorm_nnreal_pow_eq_lintegral (μ := P) (f := f) (p := 2) (by norm_num)
      hfm.aestronglyMeasurable
    rw [h2]
    simp only [NNReal.coe_ofNat, ENNReal.rpow_two] at this
    exact this.symm
  have h3 : ∀ ω, ‖adjkgY s ρ X j r ω‖ₑ ^ 2 = ENNReal.ofReal ((1 / Real.sqrt N) ^ 2) * ‖f ω‖ₑ ^ 2 := by
    intro ω
    rw [adjkg_enorm_sq, adjkg_enorm_sq, ← ENNReal.ofReal_mul (by positivity), hyf ω]
    congr 1
    ring
  simp_rw [h3]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, h1]
  calc ENNReal.ofReal ((1 / Real.sqrt N) ^ 2) * (eLpNorm f (ENNReal.ofReal 2) P) ^ 2
      ≤ ENNReal.ofReal ((1 / Real.sqrt N) ^ 2) * ENNReal.ofReal (a ^ 2) := by
        refine mul_le_mul' le_rfl ?_
        rw [ENNReal.ofReal_pow ha]
        exact pow_le_pow_left' hLp 2
    _ = ENNReal.ofReal ((a / Real.sqrt N) ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp

end HRS.AdjK
