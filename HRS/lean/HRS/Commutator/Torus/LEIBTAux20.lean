import HRS.Commutator.Torus.LEIBTAux19

/-!
# LEIB-T helpers, part 20: `L^p` norms of cut-off lifts versus torus norms
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma leibt_eLpNorm_ofReal {α : Type*} [MeasurableSpace α] {μ : Measure α} {G₀ : α → ℝ}
    (hG : AEStronglyMeasurable G₀ μ) (p : ℝ≥0∞) :
    eLpNorm (fun x => ((G₀ x : ℝ) : ℂ)) p μ = eLpNorm G₀ p μ :=
  eLpNorm_congr_norm_ae (Complex.continuous_ofReal.comp_aestronglyMeasurable hG) hG
    (Filter.Eventually.of_forall fun x => by simp)

lemma leibt_eLpNorm_box_Lam_le {η : ℝ} (hη : 0 < η) (M : ℕ) {N : ℝ} (hN : N = ((M : ℝ) + 1 / 2) / η)
    {G₀ : Torus d → ℝ} (hG₀ : Continuous G₀) {p : ℝ≥0∞} (hp : p ≠ 0) :
    eLpNorm ((leibt_boxN d N).indicator (fun y : 𝔼 => ((G₀ (Torus.mk (η • y)) : ℝ) : ℂ))) p volume ≤
      leibt_Lam d N p * eLpNorm G₀ p volume := by
  have hG : Continuous fun x : Torus d => ((G₀ x : ℝ) : ℂ) := Complex.continuous_ofReal.comp hG₀
  by_cases hpt : p = ⊤
  · subst hpt
    have := leibt_eLpNorm_box_top_le hη M hN hG
    rw [leibt_eLpNorm_ofReal hG₀.aestronglyMeasurable] at this
    unfold leibt_Lam
    simpa using this
  · have := (leibt_eLpNorm_box_eq hη M hN hG hp hpt).le
    rw [leibt_eLpNorm_ofReal hG₀.aestronglyMeasurable] at this
    unfold leibt_Lam
    rw [ENNReal.toReal_inv]
    simpa [one_div] using this

lemma leibt_eLpNorm_box_Lam_eq {η : ℝ} (hη : 0 < η) (M : ℕ) {N : ℝ} (hN : N = ((M : ℝ) + 1 / 2) / η)
    {G₀ : Torus d → ℝ} (hG₀ : Continuous G₀) {p : ℝ≥0∞} (hp : p ≠ 0) (hpt : p ≠ ⊤) :
    eLpNorm ((leibt_boxN d N).indicator (fun y : 𝔼 => ((G₀ (Torus.mk (η • y)) : ℝ) : ℂ))) p volume =
      leibt_Lam d N p * eLpNorm G₀ p volume := by
  have hG : Continuous fun x : Torus d => ((G₀ x : ℝ) : ℂ) := Complex.continuous_ofReal.comp hG₀
  have := leibt_eLpNorm_box_eq hη M hN hG hp hpt
  rw [leibt_eLpNorm_ofReal hG₀.aestronglyMeasurable] at this
  unfold leibt_Lam
  rw [ENNReal.toReal_inv]
  simpa [one_div] using this

lemma leibt_chi_zero_off_box (hd : 1 ≤ d) {e : ℕ} (he : 1 ≤ e) {N N' : ℝ} (hN : 0 < N)
    (hNN : 2 * d * N ≤ N') {y : 𝔼} (hy : y ∉ leibt_boxN d N') : leibt_chi hd he (N⁻¹ • y) = 0 := by
  rw [leibt_chi_apply]
  by_contra hne
  apply hy
  have hφ : leibt_bump hd (N⁻¹ • y) ≠ 0 := by
    intro h0
    apply hne
    rw [h0]; simp [zero_pow (by omega : e ≠ 0)]
  intro i
  have h1 := leibt_bump_support hd hφ i
  simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hN] at h1
  have h2 : |y i| < 2 * d * N := by
    have := mul_lt_mul_of_pos_left h1 hN
    rw [← mul_assoc, mul_inv_cancel₀ hN.ne', one_mul] at this
    linarith
  rw [abs_lt] at h2
  constructor <;> linarith [h2.1, h2.2]

lemma leibt_chi_one_on_box (hd : 1 ≤ d) {e : ℕ} (he : 1 ≤ e) {N : ℝ} (hN : 0 < N) {y : 𝔼}
    (hy : y ∈ leibt_boxN d N) : leibt_chi hd he (N⁻¹ • y) = 1 := by
  rw [leibt_chi_apply]
  have : leibt_bump hd (N⁻¹ • y) = 1 := by
    apply leibt_bump_eq_one
    intro i
    simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hN]
    have h := hy i
    rw [inv_mul_le_iff₀ hN, mul_one, abs_le]
    exact ⟨by linarith [h.1], h.2⟩
  rw [this]; simp

lemma leibt_chi_norm_le_one (hd : 1 ≤ d) {e : ℕ} (he : 1 ≤ e) (v : 𝔼) : ‖leibt_chi hd he v‖ ≤ 1 := by
  rw [leibt_chi_apply, Complex.norm_real, Real.norm_eq_abs, abs_pow]
  have h0 : 0 ≤ leibt_bump hd v := (leibt_bump hd).nonneg
  have h1 : leibt_bump hd v ≤ 1 := (leibt_bump hd).le_one
  rw [abs_of_nonneg h0]
  exact pow_le_one₀ h0 h1

end HRS.Commutator.TorusNote
