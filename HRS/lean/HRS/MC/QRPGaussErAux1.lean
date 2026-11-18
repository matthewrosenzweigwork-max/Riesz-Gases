import HRS.MC.QRVocab

/-!
# QRPGaussEr, auxiliary file 1: scalar Gaussian `L^p` norms and Minkowski/Fatou for squares
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace HRS.MC.QRSpec.GaussEr

section Scalar

variable {Ω : Type} [MeasurableSpace Ω]

/-- A centred real Gaussian variable is `σ` times a standard Gaussian in every `L^p`. -/
lemma qrpg_scalar {P : Measure Ω} [IsProbabilityMeasure P] {Z : Ω → ℝ} (hZ : HasGaussianLaw Z P)
    (h0 : ∫ ω, Z ω ∂P = 0) (p : ℝ≥0∞) :
    eLpNorm Z p P = ENNReal.ofReal (Real.sqrt (∫ ω, Z ω ^ 2 ∂P)) *
      eLpNorm (fun x : ℝ => x) p (gaussianReal 0 1) := by
  have h2 : MemLp Z 2 P := hZ.memLp_two
  have hmap := hZ.map_eq_gaussianReal
  have hm : P[Z] = 0 := h0
  rw [hm] at hmap
  have hvar : ProbabilityTheory.variance Z P = ∫ ω, Z ω ^ 2 ∂P := by
    rw [variance_eq_sub h2, h0]; simp
  have hv : 0 ≤ ∫ ω, Z ω ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
  set σ : ℝ := Real.sqrt (∫ ω, Z ω ^ 2 ∂P) with hσ
  have hg : gaussianReal 0 (ProbabilityTheory.variance Z P).toNNReal =
      (gaussianReal 0 1).map (σ * ·) := by
    rw [gaussianReal_map_const_mul]
    have : (NNReal.mk (σ ^ 2) (sq_nonneg _)) * 1 = (ProbabilityTheory.variance Z P).toNNReal := by
      ext; simp [hσ, hvar, Real.sq_sqrt hv, hv]
    simp [this]
  have e1 : eLpNorm Z p P = eLpNorm (fun x : ℝ => x) p (P.map Z) := by
    rw [eLpNorm_map_measure (by fun_prop) hZ.aemeasurable]; rfl
  rw [e1, hmap, hg, eLpNorm_map_measure (by fun_prop) (by fun_prop)]
  have e2 : ((fun x : ℝ => x) ∘ fun x => σ * x) = σ • (fun x : ℝ => x) := by
    funext x; simp
  rw [e2, eLpNorm_const_smul]
  simp [hσ, Real.enorm_eq_ofReal (Real.sqrt_nonneg _)]

lemma qrpg_gauss_finite (p : ℝ≥0∞) (hp : p ≠ ∞) :
    eLpNorm (fun x : ℝ => x) p (gaussianReal 0 1) < ∞ :=
  (IsGaussian.memLp_id (gaussianReal 0 1) p hp).eLpNorm_lt_top

lemma qrpg_sq_eLpNorm {P : Measure Ω} {Z : Ω → ℝ} (hZ : AEStronglyMeasurable Z P) {s : ℝ}
    (hs : 0 < s) :
    eLpNorm (fun ω => Z ω ^ 2) (ENNReal.ofReal s) P = eLpNorm Z (ENNReal.ofReal (2 * s)) P ^ 2 := by
  have h := eLpNorm_norm_rpow Z hZ (q := 2) (p := ENNReal.ofReal s) (by norm_num)
  have e1 : (fun ω => ‖Z ω‖ ^ (2 : ℝ)) = fun ω => Z ω ^ 2 := by
    funext ω; rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [e1] at h
  rw [h, mul_comm, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
  norm_cast

end Scalar

section Mink

variable {Ω : Type} [MeasurableSpace Ω] {ι : Type} [Countable ι]

/-- Minkowski (finite sections) + Fatou: `‖∑_k w_k Z_k²‖_{L^{q/2}} ≤ c_q² ∑_k w_k E Z_k²` for centred Gaussian
`Z_k` and `q ≥ 2`, where `c_q = ‖id‖_{L^q(γ)}` for the standard Gaussian `γ`. -/
lemma qrpg_minkowski {P : Measure Ω} [IsProbabilityMeasure P] (Z : ι → Ω → ℝ)
    (hZ : ∀ k, HasGaussianLaw (Z k) P) (h0 : ∀ k, ∫ ω, Z k ω ∂P = 0) (w : ι → ℝ)
    (hw : ∀ k, 0 ≤ w k) (T : Ω → ℝ) (hT : ∀ ω, HasSum (fun k => w k * Z k ω ^ 2) (T ω))
    (hTm : AEStronglyMeasurable T P) (hsum : Summable fun k => w k * ∫ ω, Z k ω ^ 2 ∂P)
    (q : ℝ) (hq : 2 ≤ q) :
    eLpNorm T (ENNReal.ofReal (q / 2)) P ≤
      ENNReal.ofReal ((eLpNorm (fun x : ℝ => x) (ENNReal.ofReal q) (gaussianReal 0 1)).toReal ^ 2 *
        ∑' k, w k * ∫ ω, Z k ω ^ 2 ∂P) := by
  set c : ℝ := (eLpNorm (fun x : ℝ => x) (ENNReal.ofReal q) (gaussianReal 0 1)).toReal with hc
  have hcfin := qrpg_gauss_finite (ENNReal.ofReal q) ENNReal.ofReal_ne_top
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  have hs1 : 1 ≤ ENNReal.ofReal (q / 2) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hspos : 0 < q / 2 := by linarith
  have hσ : ∀ k, 0 ≤ ∫ ω, Z k ω ^ 2 ∂P := fun k => integral_nonneg fun ω => sq_nonneg _
  refine Lp.eLpNorm_le_of_ae_tendsto (u := Filter.atTop) (f := fun F : Finset ι => fun ω =>
      ∑ k ∈ F, w k * Z k ω ^ 2) (Filter.Eventually.of_forall fun F => ?_) (fun F => ?_) hTm
    (Filter.Eventually.of_forall fun ω => hT ω)
  · have e : (fun ω => ∑ k ∈ F, w k * Z k ω ^ 2) =
        ∑ k ∈ F, (w k • fun ω => Z k ω ^ 2) := by
      funext ω; simp [Finset.sum_apply]
    rw [e]
    refine (eLpNorm_sum_le hs1).trans ?_
    have hterm : ∀ k ∈ F, eLpNorm (w k • fun ω => Z k ω ^ 2) (ENNReal.ofReal (q / 2)) P =
        ENNReal.ofReal (c ^ 2 * (w k * ∫ ω, Z k ω ^ 2 ∂P)) := by
      intro k _
      rw [eLpNorm_const_smul, qrpg_sq_eLpNorm (hZ k).aemeasurable.aestronglyMeasurable hspos,
        show 2 * (q / 2) = q by ring, qrpg_scalar (hZ k) (h0 k), Real.enorm_eq_ofReal (hw k)]
      rw [← ENNReal.ofReal_toReal hcfin.ne, ← hc]
      rw [mul_pow, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), ← ENNReal.ofReal_pow hc0,
        Real.sq_sqrt (hσ k), ← ENNReal.ofReal_mul (hσ k), ← ENNReal.ofReal_mul (hw k)]
      congr 1; ring
    rw [Finset.sum_congr rfl hterm, ← ENNReal.ofReal_sum_of_nonneg
      (fun k _ => mul_nonneg (sq_nonneg c) (mul_nonneg (hw k) (hσ k))), ← Finset.mul_sum]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (sq_nonneg c))
    exact hsum.sum_le_tsum F (fun k _ => mul_nonneg (hw k) (hσ k))
  · have e : (fun ω => ∑ k ∈ F, w k * Z k ω ^ 2) = ∑ k ∈ F, (fun ω => w k * Z k ω ^ 2) := by
      funext ω; simp [Finset.sum_apply]
    rw [e]
    exact Finset.aestronglyMeasurable_sum F fun k _ =>
      ((hZ k).aemeasurable.pow_const 2).const_mul (w k) |>.aestronglyMeasurable

end Mink

end HRS.MC.QRSpec.GaussEr

end
