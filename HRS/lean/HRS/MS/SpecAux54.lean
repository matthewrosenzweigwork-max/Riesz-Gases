import HRS.MS.SpecAux53
import HRS.MS.SpecAux10

/-!
# S8R: pointwise Hilbert-Schmidt bound for the difference of square roots, and the `L²` size of `∇e_i·∇e_j`
(S8.7, packets C3, C4)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.

* `s8p_sq_le_of_eLpNorm`: `‖f‖_{L²} ≤ B` gives `f ∈ L²` and `∫ f² ≤ B²`.
* `s8p_f_L2`: from the `L⁴` bounds of the gradients, `∫ (∇e_i·∇e_j)² dμ ≤ B_i² B_j²`.
* `s8p_hs_pointwise`: for `S` the square root of `hsCovForm Φ` (finite family `Φ`) and `Sb` the square root of `Cdet`,
  `∑_j ‖(S - Sb) b_j‖² ≤ 4 ∑_{i,j} (Σ_{ij} - δ_{ij} dv_i)² / (dv_i + dv_j)` in `ℝ≥0∞` (the PSD-root bound
  `s8p_psd_root_relative` applied to the diagonal `Sb = diag √dv`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace ContDiff

namespace HRS.MS.Spec

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s8p_sq_le_of_eLpNorm {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    {B : ℝ} (hB : 0 ≤ B) (h : eLpNorm f 2 μ ≤ ENNReal.ofReal B) :
    MemLp f 2 μ ∧ ∫ x, f x ^ 2 ∂μ ≤ B ^ 2 := by
  have hmem : MemLp f 2 μ := lt_of_le_of_lt h ENNReal.ofReal_lt_top
  refine ⟨hmem, ?_⟩
  have hf : AEStronglyMeasurable f μ := hmem.aestronglyMeasurable
  have h2 : eLpNorm f ((2 : ℝ≥0) : ℝ≥0∞) μ ^ (((2 : ℝ≥0) : ℝ)) =
      ∫⁻ x, ‖f x‖ₑ ^ (((2 : ℝ≥0) : ℝ)) ∂μ :=
    eLpNorm_nnreal_pow_eq_lintegral (by norm_num) hf
  have e1 : ((2 : ℝ≥0) : ℝ≥0∞) = 2 := by norm_num
  have e2 : (((2 : ℝ≥0) : ℝ)) = 2 := by norm_num
  rw [e1, e2] at h2
  have hint : Integrable (fun x => f x ^ 2) μ := hmem.integrable_sq
  have h3 : ENNReal.ofReal (∫ x, f x ^ 2 ∂μ) = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => sq_nonneg _)]
    refine lintegral_congr fun x => ?_
    rw [ENNReal.rpow_two, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs,
      sq_abs]
  have h4 : ENNReal.ofReal (∫ x, f x ^ 2 ∂μ) ≤ ENNReal.ofReal (B ^ 2) := by
    rw [h3, ← h2, ENNReal.rpow_two, ENNReal.ofReal_pow hB]
    exact pow_le_pow_left' h 2
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h4

theorem s8p_continuous_gradient {e : Euc d → ℝ} (he : ContDiff ℝ ∞ e) : Continuous (gradient e) := by
  unfold gradient
  have : Continuous (fderiv ℝ e) := he.continuous_fderiv (by simp)
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp this

theorem s8p_continuous_f {e : ℕ → Euc d → ℝ} (he : ∀ l, ContDiff ℝ ∞ (e l)) (i j : ℕ) :
    Continuous (s8p_f e i j) := by
  unfold s8p_f
  exact (s8p_continuous_gradient (he i)).inner (s8p_continuous_gradient (he j))

theorem s8p_f_L2 {μ : Measure (Euc d)} {e : ℕ → Euc d → ℝ} (he : ∀ l, ContDiff ℝ ∞ (e l))
    {om : ℕ → ℝ} {t₀ C4 : ℝ} (hC4 : 0 ≤ C4)
    (hL4 : ∀ l, eLpNorm (fun x => ‖gradient (e l) x‖) 4 μ ≤ ENNReal.ofReal (C4 * Real.exp (t₀ * om l)))
    (i j : ℕ) :
    MemLp (s8p_f e i j) 2 μ ∧
      ∫ x, s8p_f e i j x ^ 2 ∂μ ≤
        ((C4 * Real.exp (t₀ * om i)) * (C4 * Real.exp (t₀ * om j))) ^ 2 := by
  haveI : ENNReal.HolderTriple (4 : ℝ≥0∞) 4 2 := ⟨by
    have h4 : (4 : ℝ≥0∞) = 2 * 2 := by norm_num
    rw [h4, ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)), ← two_mul,
      ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]⟩
  set u : ℕ → Euc d → ℝ := fun l x => ‖gradient (e l) x‖ with hu
  have hum : ∀ l, AEStronglyMeasurable (u l) μ := fun l =>
    (s8p_continuous_gradient (he l)).norm.aestronglyMeasurable
  have hB : 0 ≤ (C4 * Real.exp (t₀ * om i)) * (C4 * Real.exp (t₀ * om j)) := by positivity
  refine s8p_sq_le_of_eLpNorm hB ?_
  have hmono : eLpNorm (s8p_f e i j) 2 μ ≤ eLpNorm (u i • u j) 2 μ := by
    refine eLpNorm_mono (s8p_continuous_f he i j).aestronglyMeasurable fun x => ?_
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, hu, s8p_f, Real.norm_eq_abs]
    rw [abs_mul, abs_norm, abs_norm]
    exact abs_real_inner_le_norm _ _
  refine hmono.trans ?_
  refine (eLpNorm_smul_le_mul_eLpNorm (p := 4) (q := 4) (r := 2) (hum i) (hum j)).trans ?_
  calc eLpNorm (u i) 4 μ * eLpNorm (u j) 4 μ
      ≤ ENNReal.ofReal (C4 * Real.exp (t₀ * om i)) * ENNReal.ofReal (C4 * Real.exp (t₀ * om j)) :=
        mul_le_mul' (hL4 i) (hL4 j)
    _ = ENNReal.ofReal ((C4 * Real.exp (t₀ * om i)) * (C4 * Real.exp (t₀ * om j))) :=
        (ENNReal.ofReal_mul (by positivity)).symm

/-- The pointwise Hilbert-Schmidt bound. -/
theorem s8p_hs_pointwise {β : ℝ} (hβ : 0 < β) {om : ℕ → ℝ} (hom : ∀ l, 0 < om l) {τ : ℝ}
    (hτ : 0 < τ) (hsum : Summable (s8p_dv β om τ)) {κ : Type*} [Fintype κ] (Φ : κ → SeqL2)
    {S Sb : SeqL2 →L[ℝ] SeqL2} (hS : IsSqrtOfForm S (hsCovForm Φ))
    (hSb : IsSqrtOfForm Sb (s8p_Cdet hβ hom hτ)) :
    ∑' j, ‖(S - Sb) (S45.s45_seqBasis j)‖ₑ ^ 2 ≤
      4 * ∑' p : ℕ × ℕ, ENNReal.ofReal
        ((hsCovForm Φ (S45.s45_seqBasis p.1) (S45.s45_seqBasis p.2) -
            (if p.1 = p.2 then s8p_dv β om τ p.1 else 0)) ^ 2 /
          (s8p_dv β om τ p.1 + s8p_dv β om τ p.2)) := by
  classical
  set b := S45.s45_seqBasis with hb
  set dv := s8p_dv β om τ with hdv
  have hdv0 : ∀ j, 0 < dv j := fun j => s8p_dv_pos hβ hom τ j
  set ee : ℕ → ℝ := fun j => Real.sqrt (dv j) with hee
  have hee0 : ∀ j, 0 < ee j := fun j => Real.sqrt_pos.2 (hdv0 j)
  have hee2 : ∀ j, ee j ^ 2 = dv j := fun j => Real.sq_sqrt (hdv0 j).le
  have hSbj : ∀ j, Sb (b j) = ee j • b j := fun j => s8p_sqrt_basis hβ hom hτ hSb j
  have hsq : ∀ i j, ⟪S (b i), S (b j)⟫ = hsCovForm Φ (b i) (b j) := fun i j => hS.sq _ _
  have hSHS : Summable fun j => ‖S (b j)‖ ^ 2 := by
    have e1 : ∀ j, ‖S (b j)‖ ^ 2 = ∑ k, SeqL2.coord (Φ k) j ^ 2 := by
      intro j
      rw [← real_inner_self_eq_norm_sq, hsq, s8p_hsCov_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hb, s8p_inner_basis]; ring
    simp_rw [e1]
    exact summable_sum fun k _ => s8p_coord_sq_summable (Φ k)
  have heHS : Summable fun j => ee j ^ 2 := by
    simp_rw [hee2]; exact hsum
  have key := s8p_psd_root_relative S hS.symm hS.nonneg ee hee0 b hSHS heHS
  have lhs : ∀ j, ‖(S - Sb) (b j)‖ₑ ^ 2 = ENNReal.ofReal (‖S (b j) - ee j • b j‖ ^ 2) := by
    intro j
    rw [ContinuousLinearMap.sub_apply, hSbj, ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  simp_rw [lhs]
  refine key.trans (le_of_eq ?_)
  congr 1
  refine tsum_congr fun p => ?_
  rw [hsq, hee2, hee2]

end HRS.MS.Spec
