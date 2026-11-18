import HRS.Commutator.Torus.LEIBTAux10

/-!
# LEIB-T helpers, part 11: Bessel derivative of a cut-off almost periodic function
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- The shifted-symbol integral `Φ(a, x) = ∫ e_{N⁻¹x}(ζ) m(a + N⁻¹ζ) ψ(ζ) dζ`. -/
def leibt_Phi (α : ℝ) (ψ : SchwartzMap 𝔼 ℂ) (N : ℝ) (a x : 𝔼) : ℂ :=
  ∫ ζ : 𝔼, leibt_e (N⁻¹ • x) ζ * (leibt_m α (a + N⁻¹ • ζ) * ψ ζ)

lemma leibt_Fm_eq (α : ℝ) (W : SchwartzMap 𝔼 ℂ) (x : 𝔼) :
    HRS.Commutator.Whole.XLI.Fm α W x =
      ∫ ξ : 𝔼, leibt_e x ξ * (leibt_m α ξ * 𝓕 (⇑W) ξ) := by
  unfold HRS.Commutator.Whole.XLI.Fm
  rw [HRS.Commutator.Whole.XLI.mulS_apply, Real.fourierInv_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [smul_eq_mul]
  rw [leibt_e_comm x ξ]
  rfl

lemma leibt_series_bessel (α : ℝ) (χ : SchwartzMap 𝔼 ℂ) {N : ℝ} (hN : 1 ≤ N) {ι : Type*} [Countable ι]
    (c : ι → ℂ) (lam : ι → 𝔼) (hc : ∀ k : ℕ, Summable fun i => ‖c i‖ * (1 + ‖lam i‖) ^ k)
    (W : SchwartzMap 𝔼 ℂ) (hW : ∀ y, HasSum (fun i => c i * (leibt_e (lam i) y * χ (N⁻¹ • y))) (W y))
    (x : 𝔼) :
    HasSum (fun i => c i * (leibt_e (lam i) x * leibt_Phi α (𝓕 χ) N (lam i) x))
      (HRS.Commutator.Whole.XLI.Fm α W x) := by
  have hN0 : 0 < N := by linarith
  set ψ : SchwartzMap 𝔼 ℂ := 𝓕 χ with hψ
  have hc0 : Summable fun i => ‖c i‖ := by simpa using hc 0
  obtain ⟨B, k₀, hB, hsh⟩ := leibt_shift_bound (d := d) α ψ
  have hFT := leibt_series_fourier χ hN0 c lam hc0 W hW
  set F : ι → 𝔼 → ℂ := fun i ξ => leibt_e x ξ * (leibt_m α ξ * (c i * (((N ^ d : ℝ) : ℂ) *
    ψ (N • (ξ - lam i))))) with hF
  have hNd : (0 : ℝ) < N ^ d := by positivity
  have hmcont : Continuous (leibt_m α : 𝔼 → ℂ) := (HRS.Commutator.Whole.XLI.bsymX_temperate (d := d) α).1.continuous
  have hcontF : ∀ i, Continuous (F i) := by
    intro i
    have := leibt_continuous_e x
    simp only [hF]
    have h2 : Continuous fun ξ : 𝔼 => ψ (N • (ξ - lam i)) :=
      ψ.continuous.comp (continuous_const_smul N |>.comp (continuous_id.sub continuous_const))
    exact this.mul (hmcont.mul (continuous_const.mul (continuous_const.mul h2)))
  -- the change of variables for each term
  have hcov : ∀ i, ∫ ξ, F i ξ = c i * (leibt_e (lam i) x * leibt_Phi α ψ N (lam i) x) := by
    intro i
    have e : ∀ ξ : 𝔼, F i ξ = c i * (leibt_e x ξ * (leibt_m α ξ * (((N ^ d : ℝ) : ℂ) * ψ (N • (ξ - lam i))))) := by
      intro ξ; simp only [hF]; ring
    simp_rw [e]
    rw [integral_const_mul, leibt_cov (leibt_m α) (fun ζ => ψ ζ) hN0 (lam i) x, leibt_e_comm x (lam i)]
    rfl
  have hnormF : ∀ i ξ, ‖F i ξ‖ = ‖c i‖ * (N ^ d) * ‖leibt_m α ξ * ψ (N • (ξ - lam i))‖ := by
    intro i ξ
    simp only [hF, norm_mul, leibt_norm_e, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hNd]
    ring
  have hint : ∀ i, Integrable (F i) := by
    intro i
    have h1 := (hsh N hN (lam i)).1
    have h2 : Integrable (fun ξ : 𝔼 => leibt_m α ξ * ψ (N • (ξ - lam i))) := by
      refine leibt_integrable_cov _ hN0 (lam i) ?_
      have e : ∀ ζ : 𝔼, leibt_m α (lam i + N⁻¹ • ζ) * ψ (N • (lam i + N⁻¹ • ζ - lam i)) =
          leibt_m α (lam i + N⁻¹ • ζ) * ψ ζ := by
        intro ζ
        rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hN0.ne', one_smul]
      simp_rw [e]
      exact h1
    refine (h2.norm.const_mul (‖c i‖ * N ^ d)).mono' (hcontF i).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => (hnormF i ξ).le)
  have hintnorm : ∀ i, ∫ ξ, ‖F i ξ‖ = ‖c i‖ * ∫ ζ : 𝔼, ‖leibt_m α (lam i + N⁻¹ • ζ) * ψ ζ‖ := by
    intro i
    simp_rw [hnormF]
    rw [integral_const_mul]
    rw [leibt_cov0 (fun ξ : 𝔼 => ‖leibt_m α ξ * ψ (N • (ξ - lam i))‖) hN0 (lam i)]
    have e : ∀ ζ : 𝔼, ‖leibt_m α (lam i + N⁻¹ • ζ) * ψ (N • (lam i + N⁻¹ • ζ - lam i))‖ =
        ‖leibt_m α (lam i + N⁻¹ • ζ) * ψ ζ‖ := by
      intro ζ
      rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hN0.ne', one_smul]
    simp_rw [e]
    rw [smul_eq_mul, ← mul_assoc, mul_assoc (‖c i‖), mul_inv_cancel₀ hNd.ne', mul_one]
  have hsum : Summable fun i => ∫ ξ, ‖F i ξ‖ := by
    refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun ξ => norm_nonneg _) (fun i => ?_)
      ((hc k₀).mul_left B)
    rw [hintnorm]
    have := (hsh N hN (lam i)).2
    calc ‖c i‖ * ∫ ζ : 𝔼, ‖leibt_m α (lam i + N⁻¹ • ζ) * ψ ζ‖
        ≤ ‖c i‖ * (B * (1 + ‖lam i‖) ^ k₀) := by gcongr
      _ = B * (‖c i‖ * (1 + ‖lam i‖) ^ k₀) := by ring
  have h1 := hasSum_integral_of_summable_integral_norm hint hsum
  have h2 : ∀ ξ, ∑' i, F i ξ = leibt_e x ξ * (leibt_m α ξ * 𝓕 (⇑W) ξ) := by
    intro ξ
    have := (hFT ξ).mul_left (leibt_m α ξ)
    have := this.mul_left (leibt_e x ξ)
    exact this.tsum_eq
  have h3 : ∫ ξ, ∑' i, F i ξ = HRS.Commutator.Whole.XLI.Fm α W x := by
    simp_rw [h2]
    rw [leibt_Fm_eq]
  rw [h3] at h1
  simpa only [hcov] using h1

end HRS.Commutator.TorusNote
