import HRS.Commutator.Torus.LEIBTAux15

/-!
# LEIB-T helpers, part 16: the real continuous representative `F₀` of the Bessel derivative
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- The continuous real function with Fourier series `∑ m(ηk) f̂(k) e_k`. -/
def leibt_F0 (α η : ℝ) (f : Torus d → ℝ) (x : Torus d) : ℝ := (leibt_Fc α η f x).re

lemma leibt_F0_cast {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (α : ℝ) {f : Torus d → ℝ}
    (hf : Torus.IsSmooth f) (x : Torus d) : ((leibt_F0 α η f x : ℝ) : ℂ) = leibt_Fc α η f x := by
  apply Complex.ext
  · simp [leibt_F0]
  · simp [leibt_Fc_real hη hη1 α hf x]

lemma leibt_F0_continuous {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (α : ℝ) {f : Torus d → ℝ}
    (hf : Torus.IsSmooth f) : Continuous (leibt_F0 α η f) :=
  Complex.continuous_re.comp (leibt_Fc_continuous hη hη1 α hf)

lemma leibt_F0_fcoef {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (α : ℝ) {f : Torus d → ℝ}
    (hf : Torus.IsSmooth f) (k : Lattice d) :
    Torus.fcoef (leibt_F0 α η f) k = leibt_bc α η f k := by
  classical
  unfold Torus.fcoef
  simp_rw [leibt_F0_cast hη hη1 α hf]
  set Fj : Lattice d → Torus d → ℂ := fun j x => Torus.mode (-k) x * (leibt_bc α η f j * Torus.mode j x) with hFj
  have hint : ∀ j, Integrable (Fj j) := fun j =>
    leibt_integrable_of_continuous ((Torus.continuous_mode (-k)).mul
      (continuous_const.mul (Torus.continuous_mode j)))
  have hnorm : ∀ j x, ‖Fj j x‖ = ‖leibt_bc α η f j‖ := by
    intro j x
    simp [hFj, norm_mul, Torus.norm_mode]
  have hsum : Summable fun j => ∫ x, ‖Fj j x‖ := by
    simp_rw [hnorm]
    simpa using leibt_bc_summable hη hη1 α hf
  have h1 := hasSum_integral_of_summable_integral_norm hint hsum
  have h2 : ∀ x, ∑' j, Fj j x = Torus.mode (-k) x * leibt_Fc α η f x := by
    intro x
    have := (leibt_Fc_hasSum hη hη1 α hf x).mul_left (Torus.mode (-k) x)
    simp only [hFj]
    convert this.tsum_eq using 2
  have h3 : ∀ j, ∫ x, Fj j x = if j = k then leibt_bc α η f k else 0 := by
    intro j
    have e : ∀ x, Fj j x = leibt_bc α η f j * (Torus.mode (-k) x * Torus.mode j x) := fun x => by
      simp only [hFj]; ring
    simp_rw [e]
    rw [integral_const_mul, Torus.integral_mode_mul]
    by_cases hj : j = k
    · subst hj; simp
    · have : ¬ (-k + j = 0) := fun h => hj (neg_add_eq_zero.1 h).symm
      simp [hj, this]
  simp_rw [h2] at h1
  simp_rw [h3] at h1
  exact h1.unique (hasSum_ite_eq k (leibt_bc α η f k))

lemma leibt_bessel_ae {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (α : ℝ) {f F : Torus d → ℝ}
    (hf : Torus.IsSmooth f) (hF : Integrable F) (hrep : IsBesselRepT η α f F) :
    F =ᵐ[volume] leibt_F0 α η f := by
  have hF0 : Integrable (leibt_F0 α η f) :=
    leibt_integrable_of_continuous (leibt_F0_continuous hη hη1 α hf)
  have hmode : ∀ (u : Torus d → ℝ), Integrable u → ∀ k : Lattice d,
      Integrable (fun x => Torus.mode (-k) x * (u x : ℂ)) := fun u hu k =>
    hu.ofReal.bdd_mul (Torus.continuous_mode (-k)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => (Torus.norm_mode (-k) x).le)
  have hg : ∀ k, Torus.fcoef (fun x => F x - leibt_F0 α η f x) k = 0 := by
    intro k
    have e : Torus.fcoef (fun x => F x - leibt_F0 α η f x) k =
        Torus.fcoef F k - Torus.fcoef (leibt_F0 α η f) k := by
      unfold Torus.fcoef
      rw [← integral_sub (hmode F hF k) (hmode _ hF0 k)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      push_cast; ring
    rw [e, leibt_F0_fcoef hη hη1 α hf, hrep k, leibt_bc, leibt_m_lam α η hη, sub_self]
  have := text_ae_eq_zero_of_fcoef (hF.sub hF0) hg
  filter_upwards [this] with x hx
  simpa [sub_eq_zero] using hx

end HRS.Commutator.TorusNote
