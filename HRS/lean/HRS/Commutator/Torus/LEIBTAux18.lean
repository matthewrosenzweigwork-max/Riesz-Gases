import HRS.Commutator.Torus.LEIBTAux17

/-!
# LEIB-T helpers, part 18: `L^p` norms of weights, dilations, and the scale factors `Λ(N,p)`
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- The weight `(1 + ‖x‖)^{-K}`. -/
def leibt_wt (d K : ℕ) (x : EuclideanSpace ℝ (Fin d)) : ℝ := ((1 + ‖x‖) ^ K)⁻¹

lemma leibt_wt_continuous (K : ℕ) : Continuous (leibt_wt d K) := by
  unfold leibt_wt
  refine Continuous.inv₀ (by fun_prop) (fun x => by positivity)

lemma leibt_wt_nonneg (K : ℕ) (x : 𝔼) : 0 ≤ leibt_wt d K x := by
  unfold leibt_wt; positivity

lemma leibt_wt_anti {K K' : ℕ} (h : K ≤ K') (x : 𝔼) : leibt_wt d K' x ≤ leibt_wt d K x := by
  unfold leibt_wt
  have h1 : (1 : ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ h1 h)

lemma leibt_wt_finite (p : ℝ≥0∞) : ∃ K : ℕ, ∀ K' : ℕ, K ≤ K' →
    eLpNorm (fun x : 𝔼 => leibt_wt d K' x) p volume < ⊤ := by
  obtain ⟨K, hK⟩ := MeasureTheory.Measure.HasTemperateGrowth.exists_eLpNorm_lt_top (E := 𝔼) p
    (μ := (volume : Measure 𝔼)) inferInstance
  refine ⟨K, fun K' hK' => lt_of_le_of_lt ?_ hK⟩
  refine eLpNorm_mono (leibt_wt_continuous K').aestronglyMeasurable fun x => ?_
  have h1 : (1 : ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  have e : (1 + ‖x‖) ^ (-(K : ℝ)) = leibt_wt d K x := by
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast]; rfl
  rw [e, Real.norm_of_nonneg (leibt_wt_nonneg K' x), Real.norm_of_nonneg (leibt_wt_nonneg K x)]
  exact leibt_wt_anti hK' x

lemma leibt_dilate {E : Type*} [NormedAddCommGroup E] {G : 𝔼 → E} (hG : Continuous G) {N : ℝ}
    (hN : 0 < N) (p : ℝ≥0∞) :
    eLpNorm (fun x : 𝔼 => G (N⁻¹ • x)) p volume =
      ENNReal.ofReal (N ^ d) ^ (p⁻¹).toReal * eLpNorm G p volume := by
  have hT : AEMeasurable (fun x : 𝔼 => N⁻¹ • x) (volume : Measure 𝔼) :=
    (measurable_const_smul N⁻¹).aemeasurable
  have hmap : Measure.map (fun x : 𝔼 => N⁻¹ • x) (volume : Measure 𝔼) =
      ENNReal.ofReal (N ^ d) • (volume : Measure 𝔼) := by
    rw [Measure.map_addHaar_smul volume (inv_ne_zero hN.ne'), finrank_euclideanSpace_fin,
      inv_pow, inv_inv, abs_of_pos (by positivity)]
  have h1 := eLpNorm_map_measure (p := p) (μ := (volume : Measure 𝔼)) (g := G)
    (f := fun x : 𝔼 => N⁻¹ • x) (by rw [hmap]; exact hG.aestronglyMeasurable.smul_measure _) hT
  rw [← Function.comp_def G (fun x : 𝔼 => N⁻¹ • x), ← h1, hmap,
    eLpNorm_smul_measure_of_ne_zero (by simp; positivity), one_div, smul_eq_mul]

lemma leibt_wt_dilate_le (K : ℕ) {N : ℝ} (hN : 0 < N) (p : ℝ≥0∞) :
    eLpNorm (fun x : 𝔼 => leibt_wt d K (N⁻¹ • x)) p volume =
      ENNReal.ofReal (N ^ d) ^ (p⁻¹).toReal * eLpNorm (leibt_wt d K) p volume :=
  leibt_dilate (leibt_wt_continuous K) hN p

/-- The scale factor `Λ(N,p) = (2N)^{d/p}`. -/
def leibt_Lam (d : ℕ) (N : ℝ) (p : ℝ≥0∞) : ℝ≥0∞ := ENNReal.ofReal ((2 * N) ^ d) ^ (p⁻¹).toReal

lemma leibt_Lam_pos {N : ℝ} (hN : 0 < N) (p : ℝ≥0∞) : 0 < leibt_Lam d N p := by
  unfold leibt_Lam
  exact ENNReal.rpow_pos (by simpa using (by positivity : (0 : ℝ) < (2 * N) ^ d)) ENNReal.ofReal_ne_top

lemma leibt_Lam_ne_top (N : ℝ) (p : ℝ≥0∞) : leibt_Lam d N p ≠ ⊤ := by
  unfold leibt_Lam
  exact ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top

lemma leibt_Lam_mul {N : ℝ} (p q r : ℝ≥0∞) (hp : p ≠ 0) (hq : q ≠ 0)
    (h : p⁻¹ + q⁻¹ = r⁻¹) (hr : r ≠ 0) (hpr : p⁻¹ ≠ ⊤) (hqr : q⁻¹ ≠ ⊤) :
    leibt_Lam d N p * leibt_Lam d N q = leibt_Lam d N r := by
  unfold leibt_Lam
  rw [← ENNReal.rpow_add_of_nonneg _ _ ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
    ← ENNReal.toReal_add hpr hqr, h]

lemma leibt_Lam_mono {N N' : ℝ} (hN : 0 < N) (hNN : N ≤ N') (p : ℝ≥0∞) :
    leibt_Lam d N p ≤ leibt_Lam d N' p := by
  unfold leibt_Lam
  refine ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) ENNReal.toReal_nonneg
  gcongr

lemma leibt_Lam_scale {N : ℝ} (hN : 0 < N) {c : ℝ} (hc : 1 ≤ c) (p : ℝ≥0∞) :
    leibt_Lam d (c * N) p ≤ ENNReal.ofReal (c ^ d) ^ (p⁻¹).toReal * leibt_Lam d N p := by
  unfold leibt_Lam
  rw [← ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg, ← ENNReal.ofReal_mul (by positivity)]
  refine le_of_eq ?_
  congr 2
  rw [← mul_pow]; ring_nf

lemma leibt_ofReal_pow_le_Lam {N : ℝ} (hN : 0 < N) (p : ℝ≥0∞) :
    ENNReal.ofReal (N ^ d) ^ (p⁻¹).toReal ≤ leibt_Lam d N p := by
  unfold leibt_Lam
  refine ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) ENNReal.toReal_nonneg
  gcongr
  linarith

end HRS.Commutator.TorusNote
