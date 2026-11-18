import HRS.Commutator.Whole.XBBAux7

/-!
# Packet XBB, part 8: the low-frequency part `K_{j₀} ⋆ W` (T1)

The spatial cutoff `W_n = W · cutC(·/(n+1))` makes `W` a Schwartz function; the Fourier-low factor
`K_{j₀} ⋆ W_n` satisfies the Kato–Ponce pair estimate of `XBBAux4` uniformly in `n`, and Fatou passes
to the limit.
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv Convolution

noncomputable section
namespace HRS.Commutator.Whole.XBB
open HRS.Commutator.Whole HRS.Commutator.Whole.XLI HRS.Commutator.Whole.XNRS
variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma xbb_cutC_scale_cs {c : ℝ} (hc : c ≠ 0) : HasCompactSupport (fun z : 𝔼 => cutC (c • z)) :=
  cutC_cs.comp_isClosedEmbedding (Homeomorph.smulOfNeZero c hc).isClosedEmbedding

lemma xbb_norm_cutC_le (η : 𝔼) : ‖cutC η‖ ≤ 1 := by
  unfold cutC
  rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith [cut_nonneg η, cut_le_one η]

/-- the spatial cutoff `W (z) cutC(z/(n+1))` -/
def xbbWn (W : 𝔼 → ℂ) (n : ℕ) (z : 𝔼) : ℂ := W z * cutC ((((n : ℝ) + 1))⁻¹ • z)

lemma xbbWn_norm {W : 𝔼 → ℂ} {L : ℝ} (hb : ∀ z, ‖W z‖ ≤ L) (n : ℕ) (z : 𝔼) :
    ‖xbbWn W n z‖ ≤ L := by
  unfold xbbWn
  rw [norm_mul]
  calc ‖W z‖ * ‖cutC ((((n : ℝ) + 1))⁻¹ • z)‖ ≤ L * 1 :=
        mul_le_mul (hb z) (xbb_norm_cutC_le _) (norm_nonneg _) ((norm_nonneg _).trans (hb z))
    _ = L := mul_one L

lemma xbbWn_smooth {W : 𝔼 → ℂ} (hW : ContDiff ℝ ∞ W) (n : ℕ) : ContDiff ℝ ∞ (xbbWn W n) :=
  hW.mul (cutC_contDiff.comp (contDiff_const_smul _))

lemma xbbWn_cs {W : 𝔼 → ℂ} (n : ℕ) : HasCompactSupport (xbbWn W n) :=
  (xbb_cutC_scale_cs (by positivity : (((n : ℝ) + 1))⁻¹ ≠ 0)).mul_left

/-- the cut-off `W_n` as a Schwartz function -/
def xbbSn {W : 𝔼 → ℂ} (hW : ContDiff ℝ ∞ W) (n : ℕ) : 𝓢(𝔼, ℂ) :=
  (xbbWn_cs (W := W) n).toSchwartzMap (xbbWn_smooth hW n)

lemma xbbSn_apply {W : 𝔼 → ℂ} (hW : ContDiff ℝ ∞ W) (n : ℕ) (z : 𝔼) :
    xbbSn hW n z = xbbWn W n z := rfl

lemma xbb_cutoff_tendsto {K W : 𝔼 → ℂ} (hK : Integrable K) (hWm : Continuous W) {L : ℝ}
    (hb : ∀ z, ‖W z‖ ≤ L) (x : 𝔼) :
    Tendsto (fun n : ℕ => cv K (xbbWn W n) x) atTop (𝓝 (cv K W x)) := by
  simp only [cv_apply]
  refine tendsto_integral_of_dominated_convergence (fun y => ‖K y‖ * L) ?_ (hK.norm.mul_const L) ?_ ?_
  · intro n
    have h1 : Continuous (fun y : 𝔼 => xbbWn W n (x - y)) := by
      unfold xbbWn
      exact (hWm.comp (by fun_prop)).mul (cutC_contDiff.continuous.comp (by fun_prop))
    exact hK.aestronglyMeasurable.mul h1.aestronglyMeasurable
  · intro n
    refine Eventually.of_forall fun y => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (xbbWn_norm hb n _) (norm_nonneg _)
  · refine Eventually.of_forall fun y => ?_
    refine Tendsto.const_mul _ ?_
    unfold xbbWn
    have h1 : Tendsto (fun n : ℕ => cutC ((((n : ℝ) + 1))⁻¹ • (x - y))) atTop (𝓝 (cutC ((0 : ℝ) • (x - y)))) := by
      refine (cutC_contDiff.continuous.tendsto _).comp ?_
      refine Tendsto.smul_const ?_ _
      exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    rw [zero_smul, cutC_eq_one_of_le (by simp)] at h1
    simpa using (tendsto_const_nhds (x := W (x - y))).mul h1


/-- **T1**: the low-frequency part `K_{j₀} ⋆ W` of a bounded smooth `W` satisfies the product bound
against a Schwartz function `Γ` with `𝓕Γ = 0` on `|ξ| < 2^{j₀}`. -/
lemma xbb_T1 (hd : 1 ≤ d) {β : ℝ} (hβ : 0 < β) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (W : 𝔼 → ℂ), ContDiff ℝ ∞ W → ∀ {L : ℝ}, 0 ≤ L → (∀ z, ‖W z‖ ≤ L) →
      ∀ (j₀ : ℤ) (Γ : 𝓢(𝔼, ℂ)), (∀ ξ : 𝔼, ‖ξ‖ < (2 : ℝ) ^ j₀ → 𝓕 (⇑Γ) ξ = 0) →
        xbbN β (fun x => cv ⇑(xbbK j₀) W x * Γ x) ≤ C * ENNReal.ofReal L * xbbN β ⇑Γ := by
  obtain ⟨CP, hCP, hP⟩ := xbb_pair_low_scaled hd hβ
  obtain ⟨A, hA, hAK⟩ := xbbK_lintegral_le d
  refine ⟨CP * A, ENNReal.mul_ne_top hCP hA, fun W hW L hL hb j₀ Γ hΓ => ?_⟩
  have hμ : 0 < (2 : ℝ) ^ j₀ := zpow_pos (by norm_num) j₀
  have hAr : ENNReal.ofReal A.toReal = A := ENNReal.ofReal_toReal hA
  -- the approximants
  set f : ℕ → 𝓢(𝔼, ℂ) := fun n => mulS (fun ξ => cutC (((2 : ℝ) ^ j₀)⁻¹ • ξ))
    (temperate_symbol cutC_contDiff cutC_cs j₀) (xbbSn hW n) with hf
  have hfcv : ∀ n x, f n x = cv ⇑(xbbK j₀) (xbbWn W n) x := by
    intro n x
    rw [xbbK_coe]
    have := cv_symK_eq_mulS cutC_contDiff cutC_cs (xbbSn hW n) j₀
    exact (congrFun this x).symm
  have hfb : ∀ n x, ‖f n x‖ ≤ A.toReal * L := by
    intro n x
    rw [hfcv]
    exact xbb_norm_cv_le (xbbK j₀).continuous.measurable hL ENNReal.toReal_nonneg
      (by rw [hAr]; exact hAK j₀) (xbbWn_norm hb n) x
  have hff : ∀ n, ∀ ξ : 𝔼, 4 * (2 : ℝ) ^ j₀ < ‖ξ‖ → 𝓕 (⇑(f n)) ξ = 0 := by
    intro n ξ hξ
    rw [hf]
    simp only []
    rw [fourier_mulS]
    have : cutC (((2 : ℝ) ^ j₀)⁻¹ • ξ) = 0 := by
      refine cutC_eq_zero_of_ge ?_
      rw [norm_smul, norm_inv, Real.norm_of_nonneg hμ.le, inv_mul_eq_div, le_div_iff₀ hμ]
      linarith
    rw [this, zero_mul]
  have hbound : ∀ n, xbbN β (fun x => f n x * Γ x) ≤ CP * ENNReal.ofReal (A.toReal * L) * xbbN β ⇑Γ :=
    fun n => hP _ hμ (f n) Γ (hff n) hΓ _ (by positivity) (hfb n)
  have hWc : Continuous W := hW.continuous
  have hlim : ∀ ξ : 𝔼, Tendsto (fun n : ℕ => 𝓕 (fun x => f n x * Γ x) ξ) atTop
      (𝓝 (𝓕 (fun x => cv ⇑(xbbK j₀) W x * Γ x) ξ)) := by
    intro ξ
    refine xbb_fourier_tendsto (M := A.toReal * L) (fun n => (f n).continuous.aestronglyMeasurable) hfb ?_ ξ
    intro x
    simp_rw [hfcv]
    exact xbb_cutoff_tendsto (xbbK j₀).integrable hWc hb x
  have hmain := xbbN_fatou β (fun n => (prodS (f n) Γ).integrable) hlim (M := fun _ => CP * ENNReal.ofReal (A.toReal * L) * xbbN β ⇑Γ)
    (M0 := CP * ENNReal.ofReal (A.toReal * L) * xbbN β ⇑Γ) hbound tendsto_const_nhds
  refine hmain.trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, hAr]
  ring

end HRS.Commutator.Whole.XBB
