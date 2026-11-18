import HRS.Commutator.Whole.XLIAux13

/-!
# X-LI part 14: the telescoping paraproduct decomposition of a product of Schwartz functions
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution Topology SchwartzMap

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma sch_bdd (f : SchwartzMap 𝔼 ℂ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨B, hB0, hB⟩ := f.decay 0 0
  exact ⟨B, hB0.le, fun x => by simpa using hB x⟩

/-- dominated convergence on the Fourier side -/
lemma tendsto_fourierInv_mul (f : SchwartzMap 𝔼 ℂ) (y : 𝔼) (σ : ℕ → 𝔼 → ℂ) (σ' : 𝔼 → ℂ)
    (hc : ∀ n, Continuous (σ n)) (hσ : ∀ n ξ, ‖σ n ξ‖ ≤ 1)
    (hlim : ∀ᵐ ξ ∂(volume : Measure 𝔼), Tendsto (fun n => σ n ξ) atTop (𝓝 (σ' ξ))) :
    Tendsto (fun n => 𝓕⁻ (fun ξ => σ n ξ * 𝓕 (⇑f) ξ) y) atTop
      (𝓝 (𝓕⁻ (fun ξ => σ' ξ * 𝓕 (⇑f) ξ) y)) := by
  simp only [Real.fourierInv_eq']
  have hFi : Integrable (𝓕 (⇑f)) := by
    rw [← SchwartzMap.fourier_coe]; exact (𝓕 f).integrable
  have hFc : Continuous (𝓕 (⇑f)) := by
    rw [← SchwartzMap.fourier_coe]; exact (𝓕 f).continuous
  refine tendsto_integral_of_dominated_convergence (fun ξ => ‖𝓕 (⇑f) ξ‖) ?_ hFi.norm ?_ ?_
  · intro n
    refine Continuous.aestronglyMeasurable ?_
    have h1 : Continuous (fun ξ : 𝔼 => Complex.exp (↑(2 * Real.pi * inner ℝ ξ y) * Complex.I)) := by
      refine Complex.continuous_exp.comp ?_
      refine Continuous.mul (Complex.continuous_ofReal.comp ?_) continuous_const
      exact continuous_const.mul (Continuous.inner continuous_id continuous_const)
    exact h1.smul ((hc n).mul hFc)
  · intro n
    refine Eventually.of_forall fun ξ => ?_
    rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hσ n ξ)
  · filter_upwards [hlim] with ξ hξ
    exact (tendsto_const_nhds.smul (hξ.mul_const _))

lemma tendsto_inv_two_zpow_nat : Tendsto (fun N : ℕ => ((2 : ℝ) ^ (N : ℤ))⁻¹) atTop (𝓝 0) := by
  have : (fun N : ℕ => ((2 : ℝ) ^ (N : ℤ))⁻¹) = fun N : ℕ => ((1 / 2 : ℝ)) ^ N := by
    funext N; simp
  rw [this]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

lemma tendsto_Pm_top (f : SchwartzMap 𝔼 ℂ) (y : 𝔼) :
    Tendsto (fun N : ℕ => Pm (N : ℤ) f y) atTop (𝓝 (f y)) := by
  have h := tendsto_fourierInv_mul f y (fun N ξ => cutC (((2 : ℝ) ^ (N : ℤ))⁻¹ • ξ)) (fun _ => 1)
    (fun N => cutC_contDiff.continuous.comp (continuous_const_smul _))
    (fun N ξ => norm_cutC_le_one _) (Eventually.of_forall fun ξ => ?_)
  · have e : ∀ N : ℕ, Pm (N : ℤ) f y = 𝓕⁻ (fun ξ => cutC (((2 : ℝ) ^ (N : ℤ))⁻¹ • ξ) * 𝓕 (⇑f) ξ) y :=
      fun N => mulS_apply _ _ f y
    simp_rw [e]
    have e2 : 𝓕⁻ (fun ξ => (1 : ℂ) * 𝓕 (⇑f) ξ) y = f y := by
      simp only [one_mul]
      have h1 : (𝓕⁻ (𝓕 f) : SchwartzMap 𝔼 ℂ) = f := FourierTransform.fourierInv_fourier_eq f
      have h2 := SchwartzMap.fourierInv_coe (𝓕 f)
      rw [h1, SchwartzMap.fourier_coe] at h2
      exact (congrFun h2 y).symm
    rwa [e2] at h
  · -- pointwise convergence of the symbol
    have h0 := tendsto_inv_two_zpow_nat.mul_const ‖ξ‖
    rw [zero_mul] at h0
    have hev : ∀ᶠ N : ℕ in atTop, ((2 : ℝ) ^ (N : ℤ))⁻¹ * ‖ξ‖ ≤ 1 :=
      h0.eventually (Iic_mem_nhds (by norm_num))
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with N hN
    rw [cutC_eq_one_of_le (by rw [norm_smul_inv_zpow]; exact hN)]

lemma tendsto_Pm_bot [Nontrivial 𝔼] (f : SchwartzMap 𝔼 ℂ) (y : 𝔼) :
    Tendsto (fun N : ℕ => Pm (-(N : ℤ) - 1) f y) atTop (𝓝 0) := by
  have h := tendsto_fourierInv_mul f y (fun N ξ => cutC (((2 : ℝ) ^ (-(N : ℤ) - 1))⁻¹ • ξ))
    (fun _ => 0)
    (fun N => cutC_contDiff.continuous.comp (continuous_const_smul _))
    (fun N ξ => norm_cutC_le_one _) ?_
  · have e : ∀ N : ℕ, Pm (-(N : ℤ) - 1) f y =
        𝓕⁻ (fun ξ => cutC (((2 : ℝ) ^ (-(N : ℤ) - 1))⁻¹ • ξ) * 𝓕 (⇑f) ξ) y :=
      fun N => mulS_apply _ _ f y
    simp_rw [e]
    have e2 : 𝓕⁻ (fun ξ => (0 : ℂ) * 𝓕 (⇑f) ξ) y = 0 := by
      simp [Real.fourierInv_eq']
    rwa [e2] at h
  · have hne : ∀ᵐ ξ ∂(volume : Measure 𝔼), ξ ≠ 0 := by
      have : (volume : Measure 𝔼) {0} = 0 := measure_singleton 0
      exact measure_eq_zero_iff_ae_notMem.1 this
    filter_upwards [hne] with ξ hξ
    have hpos : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    -- `2^{N+1} ‖ξ‖ → ∞`
    have h1 : Tendsto (fun N : ℕ => (2 : ℝ) ^ (N + 1) * ‖ξ‖) atTop atTop := by
      refine Tendsto.atTop_mul_const hpos ?_
      exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp (tendsto_add_atTop_nat 1)
    have hev : ∀ᶠ N : ℕ in atTop, 2 ≤ (2 : ℝ) ^ (N + 1) * ‖ξ‖ := h1.eventually_ge_atTop 2
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with N hN
    symm
    apply cutC_eq_zero_of_ge
    have : ((2 : ℝ) ^ (-(N : ℤ) - 1))⁻¹ = (2 : ℝ) ^ (N + 1) := by
      rw [← zpow_neg]; simp [← zpow_natCast]; ring_nf
    rw [norm_smul, this, Real.norm_of_nonneg (by positivity)]
    exact hN

/-- the paraproduct terms `Δ_m f · P_m g + P_{m-1} f · Δ_m g` -/
def aterm (f g : SchwartzMap 𝔼 ℂ) (m : ℤ) (y : 𝔼) : ℂ :=
  Dm m f y * Pm m g y + Pm (m - 1) f y * Dm m g y

lemma aterm_eq (f g : SchwartzMap 𝔼 ℂ) (m : ℤ) (y : 𝔼) :
    aterm f g m y = Pm m f y * Pm m g y - Pm (m - 1) f y * Pm (m - 1) g y := by
  have hf : Pm m f y = Pm (m - 1) f y + Dm m f y := by
    rw [Pm_succ m f]; rfl
  have hg : Pm m g y = Pm (m - 1) g y + Dm m g y := by
    rw [Pm_succ m g]; rfl
  unfold aterm
  rw [hf, hg]; ring

lemma sum_aterm (f g : SchwartzMap 𝔼 ℂ) (L : ℤ) (n : ℕ) (y : 𝔼) :
    ∑ i ∈ Finset.range n, aterm f g (L + i) y =
      Pm (L + n - 1) f y * Pm (L + n - 1) g y - Pm (L - 1) f y * Pm (L - 1) g y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, aterm_eq]
    have e : L + ((n + 1 : ℕ) : ℤ) - 1 = L + n := by push_cast; ring
    have e2 : L + (n : ℤ) - 1 = L + n - 1 := rfl
    rw [e]
    have e3 : L + (n : ℤ) - 1 = L + (n : ℤ) - 1 := rfl
    ring

lemma Pm_bdd (f : SchwartzMap 𝔼 ℂ) : ∃ C : ℝ, ∀ m y, ‖Pm m f y‖ ≤ C := by
  obtain ⟨A, hA, hdec⟩ := symK_dec (d := d) cutC_contDiff cutC_cs
  obtain ⟨Cf, hCf0, hCf⟩ := sch_bdd f
  set B : ℝ≥0∞ := (A * KP d) * ENNReal.ofReal Cf with hB
  have hBne : B ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top hA KP_ne_top) ENNReal.ofReal_ne_top
  refine ⟨B.toReal, fun m y => ?_⟩
  have h1 : ‖Pm m f y‖ₑ ≤ B := by
    have e := congrFun (cv_cut_eq_Pm m f) y
    rw [← e]
    calc ‖cv (symK cutC m) ⇑f y‖ₑ ≤ ∫⁻ z, ‖symK cutC m z‖ₑ * ‖f (y - z)‖ₑ := enorm_cv_le _ _ _
      _ ≤ ∫⁻ z, ‖symK cutC m z‖ₑ * ENNReal.ofReal Cf := by
          refine lintegral_mono fun z => mul_le_mul_right ?_ _
          rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hCf _)
      _ = (∫⁻ z, ‖symK cutC m z‖ₑ) * ENNReal.ofReal Cf := lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ ≤ (A * KP d) * ENNReal.ofReal Cf := mul_le_mul_left (lintegral_enorm_le_of_dec (hdec m)) _
  rw [← ofReal_norm] at h1
  exact (ENNReal.ofReal_le_iff_le_toReal hBne).1 h1

lemma aterm_cont (f g : SchwartzMap 𝔼 ℂ) (m : ℤ) : Continuous (aterm f g m) :=
  ((Dm m f).continuous.mul (Pm m g).continuous).add ((Pm (m - 1) f).continuous.mul (Dm m g).continuous)

lemma aterm_bdd (f g : SchwartzMap 𝔼 ℂ) (m : ℤ) : ∃ Ca : ℝ, ∀ y, ‖aterm f g m y‖ ≤ Ca := by
  obtain ⟨C1, hC1, h1⟩ := sch_bdd (Dm m f)
  obtain ⟨C2, hC2, h2⟩ := sch_bdd (Pm m g)
  obtain ⟨C3, hC3, h3⟩ := sch_bdd (Pm (m - 1) f)
  obtain ⟨C4, hC4, h4⟩ := sch_bdd (Dm m g)
  refine ⟨C1 * C2 + C3 * C4, fun y => ?_⟩
  unfold aterm
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  exact add_le_add (mul_le_mul (h1 y) (h2 y) (norm_nonneg _) hC1)
    (mul_le_mul (h3 y) (h4 y) (norm_nonneg _) hC3)

/-- **the telescoping decomposition**: `|K ⋆ (f g)| ≤ ∑_m |K ⋆ a_m|` -/
lemma cv_fg_le_tsum [Nontrivial 𝔼] {K : 𝔼 → ℂ} (hK : Integrable K) (hKm : Measurable K)
    (f g : SchwartzMap 𝔼 ℂ) (x : 𝔼) :
    ‖cv K (fun y => f y * g y) x‖ₑ ≤ ∑' m : ℤ, ‖cv K (aterm f g m) x‖ₑ := by
  obtain ⟨Cf, hCf⟩ := Pm_bdd f
  obtain ⟨Cg, hCg⟩ := Pm_bdd g
  set S : ℕ → 𝔼 → ℂ := fun N y => ∑ i ∈ Finset.range (2 * N + 1), aterm f g (-(N : ℤ) + i) y with hS
  have hSeq : ∀ N y, S N y = Pm (N : ℤ) f y * Pm (N : ℤ) g y -
      Pm (-(N : ℤ) - 1) f y * Pm (-(N : ℤ) - 1) g y := by
    intro N y
    simp only [hS]
    rw [sum_aterm]
    have e : -(N : ℤ) + ((2 * N + 1 : ℕ) : ℤ) - 1 = (N : ℤ) := by push_cast; ring
    rw [e]
  have hCfg : 0 ≤ Cf * Cg := by
    have h0 : 0 ≤ Cf := (norm_nonneg _).trans (hCf 0 0)
    have h1 : 0 ≤ Cg := (norm_nonneg _).trans (hCg 0 0)
    positivity
  have hSb : ∀ N y, ‖S N y‖ ≤ 2 * (Cf * Cg) := by
    intro N y
    rw [hSeq]
    have h0 : 0 ≤ Cf := (norm_nonneg _).trans (hCf 0 0)
    have h1 : ‖Pm (N : ℤ) f y * Pm (N : ℤ) g y‖ ≤ Cf * Cg := by
      rw [norm_mul]
      exact mul_le_mul (hCf _ _) (hCg _ _) (norm_nonneg _) h0
    have h2 : ‖Pm (-(N : ℤ) - 1) f y * Pm (-(N : ℤ) - 1) g y‖ ≤ Cf * Cg := by
      rw [norm_mul]
      exact mul_le_mul (hCf _ _) (hCg _ _) (norm_nonneg _) h0
    calc _ ≤ ‖Pm (N : ℤ) f y * Pm (N : ℤ) g y‖ +
          ‖Pm (-(N : ℤ) - 1) f y * Pm (-(N : ℤ) - 1) g y‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  have hSlim : ∀ y, Tendsto (fun N => S N y) atTop (𝓝 (f y * g y)) := by
    intro y
    have h1 := (tendsto_Pm_top f y).mul (tendsto_Pm_top g y)
    have h2 := (tendsto_Pm_bot f y).mul (tendsto_Pm_bot g y)
    have := h1.sub h2
    simp only [mul_zero, sub_zero] at this
    exact this.congr (fun N => (hSeq N y).symm)
  have hSc : ∀ N, Continuous (S N) := fun N =>
    continuous_finsetSum _ (fun i _ => aterm_cont f g _)
  have hint : ∀ m : ℤ, Integrable (fun y => K y * aterm f g m (x - y)) := by
    intro m
    obtain ⟨Ca, hCa⟩ := aterm_bdd f g m
    refine Integrable.mul_bdd (c := Ca) hK ?_ (Eventually.of_forall fun y => hCa (x - y))
    exact ((aterm_cont f g m).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hcvS : ∀ N, cv K (S N) x =
      ∑ i ∈ Finset.range (2 * N + 1), cv K (aterm f g (-(N : ℤ) + i)) x := by
    intro N
    simp only [cv_apply, hS]
    simp_rw [Finset.mul_sum]
    exact integral_finsetSum _ (fun i _ => hint _)
  have hlim : Tendsto (fun N => cv K (S N) x) atTop (𝓝 (cv K (fun y => f y * g y) x)) := by
    simp only [cv_apply]
    refine tendsto_integral_of_dominated_convergence (fun y => ‖K y‖ * (2 * (Cf * Cg))) ?_ ?_ ?_ ?_
    · intro N
      exact hKm.aestronglyMeasurable.mul
        (((hSc N).comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    · exact hK.norm.mul_const _
    · intro N
      refine Eventually.of_forall fun y => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hSb N (x - y)) (norm_nonneg _)
    · exact Eventually.of_forall fun y => tendsto_const_nhds.mul (hSlim (x - y))
  have hle : ∀ N, ‖cv K (S N) x‖ₑ ≤ ∑' m : ℤ, ‖cv K (aterm f g m) x‖ₑ := by
    intro N
    rw [hcvS]
    refine (enorm_sum_le _ _).trans ?_
    have hinj : Function.Injective (fun i : ℕ => -(N : ℤ) + (i : ℤ)) := fun a b h => by
      simpa using h
    calc ∑ i ∈ Finset.range (2 * N + 1), ‖cv K (aterm f g (-(N : ℤ) + i)) x‖ₑ
        = ∑ m ∈ (Finset.range (2 * N + 1)).image (fun i : ℕ => -(N : ℤ) + (i : ℤ)),
            ‖cv K (aterm f g m) x‖ₑ := (Finset.sum_image (f := fun m => ‖cv K (aterm f g m) x‖ₑ) (fun a _ b _ h => hinj h)).symm
      _ ≤ _ := ENNReal.sum_le_tsum _
  exact le_of_tendsto' hlim.enorm hle

end HRS.Commutator.Whole.XLI
