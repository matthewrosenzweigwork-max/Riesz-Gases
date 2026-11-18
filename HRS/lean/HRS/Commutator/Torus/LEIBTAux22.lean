import HRS.Commutator.Torus.LEIBTAux21

/-!
# LEIB-T helpers, part 22: `L^p` bounds for the Bessel derivative of the cut-off lifts
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma leibt_err_norm_le (hd : 1 ≤ d) {η : ℝ} (α : ℝ) {N : ℝ} (hN : 1 ≤ N) {e : ℕ} (he : 1 ≤ e)
    (W : SchwartzMap 𝔼 ℂ) {G₀ : Torus d → ℝ} (hG₀ : Continuous G₀) {S : ℝ} (hS : 0 ≤ S) (K : ℕ)
    (hE : ∀ x : 𝔼, ‖HRS.Commutator.Whole.XLI.Fm α W x -
        ((G₀ (Torus.mk (η • x)) : ℝ) : ℂ) * leibt_chi hd he (N⁻¹ • x)‖ ≤
        S * N⁻¹ * ((1 + ‖N⁻¹ • x‖) ^ K)⁻¹) (p : ℝ≥0∞) :
    eLpNorm (fun x : 𝔼 => HRS.Commutator.Whole.XLI.Fm α W x -
        ((G₀ (Torus.mk (η • x)) : ℝ) : ℂ) * leibt_chi hd he (N⁻¹ • x)) p volume ≤
      ENNReal.ofReal (S * N⁻¹) * (leibt_Lam d N p * eLpNorm (leibt_wt d K) p volume) := by
  have hN0 : 0 < N := by linarith
  have hcont : Continuous fun x : 𝔼 => HRS.Commutator.Whole.XLI.Fm α W x -
      ((G₀ (Torus.mk (η • x)) : ℝ) : ℂ) * leibt_chi hd he (N⁻¹ • x) :=
    (HRS.Commutator.Whole.XLI.Fm α W).continuous.sub (leibt_cut_cont hd he hG₀ N)
  have h1 : eLpNorm (fun x : 𝔼 => HRS.Commutator.Whole.XLI.Fm α W x -
        ((G₀ (Torus.mk (η • x)) : ℝ) : ℂ) * leibt_chi hd he (N⁻¹ • x)) p volume ≤
      eLpNorm ((S * N⁻¹) • (fun x : 𝔼 => leibt_wt d K (N⁻¹ • x))) p volume := by
    refine eLpNorm_mono hcont.aestronglyMeasurable fun x => ?_
    refine (hE x).trans ?_
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs, leibt_wt]
    rw [abs_of_nonneg hS, abs_of_nonneg (inv_nonneg.2 hN0.le), abs_of_nonneg (by positivity)]
  refine h1.trans ?_
  rw [eLpNorm_const_smul, leibt_wt_dilate_le K hN0, Real.enorm_eq_ofReal (by positivity)]
  gcongr
  exact leibt_ofReal_pow_le_Lam hN0 p

end HRS.Commutator.TorusNote
