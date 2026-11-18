import HRS.Commutator.Torus.LEIBTAux13
import HRS.Commutator.Torus.TEXTAux2

/-!
# LEIB-T helpers, part 14: the Fourier series of a smooth function and of its Bessel derivative
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma leibt_mode_eq (η : ℝ) (k : Lattice d) (y : 𝔼) :
    Torus.mode k (Torus.mk (η • y)) = leibt_e (leibt_lam η k) y := by
  rw [Torus.mode_mk]
  unfold leibt_e leibt_lam
  rw [real_inner_smul_left, ← Torus.dot_eq_inner, Torus.dot_smul]

lemma leibt_f_series {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) {f : Torus d → ℝ} (hf : Torus.IsSmooth f)
    (y : 𝔼) :
    HasSum (fun k : Lattice d => Torus.fcoef f k * leibt_e (leibt_lam η k) y)
      ((f (Torus.mk (η • y)) : ℝ) : ℂ) := by
  have hc : Continuous f := Torus.continuous_of_continuous_lift (by
    have := hf
    unfold Torus.IsSmooth Torus.IsCk at this
    exact this.continuous)
  have hs : Summable fun k : Lattice d => ‖Torus.fcoef f k‖ := by
    simpa using leibt_coef_summable hη hη1 hf 0
  have := Torus.hasSum_fcoef_series hc hs (Torus.mk (η • y))
  simpa only [leibt_mode_eq] using this

/-- The Bessel coefficients `m(η k) f̂(k)`. -/
def leibt_bc (α η : ℝ) (f : Torus d → ℝ) (k : Lattice d) : ℂ :=
  leibt_m α (leibt_lam η k) * Torus.fcoef f k

lemma leibt_bc_summable {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (α : ℝ) {f : Torus d → ℝ}
    (hf : Torus.IsSmooth f) : Summable fun k : Lattice d => ‖leibt_bc α η f k‖ := by
  obtain ⟨C₀, k₀, hC₀, hm⟩ := leibt_m_bound (d := d) α
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
    ((leibt_coef_summable hη hη1 hf k₀).mul_left C₀)
  unfold leibt_bc
  rw [norm_mul]
  calc ‖leibt_m α (leibt_lam η k)‖ * ‖Torus.fcoef f k‖
      ≤ (C₀ * (1 + ‖leibt_lam η k‖) ^ k₀) * ‖Torus.fcoef f k‖ := by gcongr; exact hm _
    _ = C₀ * (‖Torus.fcoef f k‖ * (1 + ‖leibt_lam η k‖) ^ k₀) := by ring

/-- The complex-valued Fourier series of the Bessel derivative. -/
def leibt_Fc (α η : ℝ) (f : Torus d → ℝ) (x : Torus d) : ℂ := ∑' k, leibt_bc α η f k * Torus.mode k x

lemma leibt_Fc_hasSum {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (α : ℝ) {f : Torus d → ℝ}
    (hf : Torus.IsSmooth f) (x : Torus d) :
    HasSum (fun k : Lattice d => leibt_bc α η f k * Torus.mode k x) (leibt_Fc α η f x) := by
  have hs := leibt_bc_summable hη hη1 α hf
  refine (Summable.of_norm ?_).hasSum
  simpa [norm_mul, Torus.norm_mode] using hs

lemma leibt_Fc_continuous {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (α : ℝ) {f : Torus d → ℝ}
    (hf : Torus.IsSmooth f) : Continuous (leibt_Fc α η f) := by
  unfold leibt_Fc
  refine continuous_tsum (u := fun k => ‖leibt_bc α η f k‖)
    (fun k => continuous_const.mul (Torus.continuous_mode k)) (leibt_bc_summable hη hη1 α hf) ?_
  intro k x
  simp [norm_mul, Torus.norm_mode]

end HRS.Commutator.TorusNote
