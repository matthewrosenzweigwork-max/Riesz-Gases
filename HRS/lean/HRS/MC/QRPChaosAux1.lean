import Mathlib

/-!
# Packet CHAOS-LP (aux 1): scalar Gaussian `L^p` moments

For a centred real Gaussian variable `Z` with `E Z² ≤ s²`: `‖Z‖_{L^p} ≤ s · ‖id‖_{L^p(N(0,1))}`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MC.QRPChaos

/-- The `L^p` norm of the identity under the standard real Gaussian law. -/
def qpcG (p : ℝ) : ℝ≥0∞ := eLpNorm id (ENNReal.ofReal p) (gaussianReal 0 1)

lemma qpcG_lt_top (p : ℝ) : qpcG p < ∞ :=
  ((memLp_id_gaussianReal' (μ := 0) (v := 1) (ENNReal.ofReal p) ENNReal.ofReal_ne_top)).eLpNorm_lt_top

lemma qpc_scalar {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → ℝ}
    (hZ : HasGaussianLaw Z P) (h0 : ∫ ω, Z ω ∂P = 0) {s : ℝ} (hs : 0 ≤ s)
    (hv : ∫ ω, Z ω ^ 2 ∂P ≤ s ^ 2) (p : ℝ) :
    eLpNorm Z (ENNReal.ofReal p) P ≤ ENNReal.ofReal s * qpcG p := by
  have hmap := hZ.map_eq_gaussianReal
  have hvar : Var[Z; P] = ∫ ω, Z ω ^ 2 ∂P := variance_of_integral_eq_zero hZ.aemeasurable h0
  set v : ℝ≥0 := Var[Z; P].toNNReal with hvdef
  have hvle : (v : ℝ) ≤ s ^ 2 := by
    have : (v : ℝ) = max Var[Z; P] 0 := by simp [hvdef]
    rw [this, hvar]
    exact max_le hv (sq_nonneg s)
  have h1 : eLpNorm Z (ENNReal.ofReal p) P = eLpNorm id (ENNReal.ofReal p) (P.map Z) := by
    rw [eLpNorm_map_measure (by exact aestronglyMeasurable_id) hZ.aemeasurable]; rfl
  have hm0 : P[Z] = 0 := h0
  have h2 : P.map Z = (gaussianReal 0 1).map (fun x => Real.sqrt v * x) := by
    rw [hmap, hm0, gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext; simp
  have h3 : eLpNorm id (ENNReal.ofReal p) ((gaussianReal 0 1).map (fun x => Real.sqrt v * x)) =
      eLpNorm (fun x => Real.sqrt v * x) (ENNReal.ofReal p) (gaussianReal 0 1) := by
    rw [eLpNorm_map_measure (by exact aestronglyMeasurable_id) (by fun_prop)]; rfl
  have h4 : eLpNorm (fun x : ℝ => Real.sqrt v * x) (ENNReal.ofReal p) (gaussianReal 0 1) =
      ‖Real.sqrt v‖ₑ * qpcG p := by
    have := eLpNorm_const_smul (μ := gaussianReal 0 1) (Real.sqrt v) (id : ℝ → ℝ) (ENNReal.ofReal p)
    rw [qpcG, ← this]
    congr 1
  rw [h1, h2, h3, h4]
  gcongr
  rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  exact Real.sqrt_le_iff.2 ⟨hs, hvle⟩

end HRS.MC.QRPChaos

end
