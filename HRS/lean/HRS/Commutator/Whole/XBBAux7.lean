import HRS.Commutator.Whole.XBBAux6

/-!
# Packet XBB, part 7: dyadic low-pass kernels, approximate identity, Fourier convergence and Fatou

* `xbbK j`: the Schwartz kernel `𝓕⁻[cutC(2^{-j}·)]`; `xbb_approx`: `K_{j₀+k} ⋆ W → W` pointwise for
  bounded continuous `W`;
* `xbb_fourier_tendsto`: dominated pointwise convergence of `h_k` gives pointwise convergence of
  `𝓕(h_k Γ)`; `xbbN_fatou`: lower semicontinuity of the Sobolev seminorm.
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv Convolution

noncomputable section
namespace HRS.Commutator.Whole.XBB
open HRS.Commutator.Whole HRS.Commutator.Whole.XLI HRS.Commutator.Whole.XNRS
variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- the symbol `cutC(2^{-j}·)` as a Schwartz function -/
def xbbSC (j : ℤ) : 𝓢(𝔼, ℂ) :=
  (symbol_cs cutC_cs j).toSchwartzMap (symbol_contDiff cutC_contDiff j)

lemma xbbSC_apply (j : ℤ) (ξ : 𝔼) : xbbSC j ξ = cutC (((2 : ℝ) ^ j)⁻¹ • ξ) := rfl

/-- the dyadic low-pass kernel `κ_j = 𝓕⁻[cutC(2^{-j}·)]` as a Schwartz function -/
def xbbK (j : ℤ) : 𝓢(𝔼, ℂ) := 𝓕⁻ (xbbSC j)

lemma xbbK_coe (j : ℤ) : ⇑(xbbK j) = symK (cutC : 𝔼 → ℂ) j := by
  funext x
  unfold xbbK symK
  rw [SchwartzMap.fourierInv_coe]
  rfl

lemma fourier_xbbK (j : ℤ) (ξ : 𝔼) : 𝓕 (⇑(xbbK j)) ξ = cutC (((2 : ℝ) ^ j)⁻¹ • ξ) := by
  rw [xbbK_coe]; exact symK_fourier cutC_contDiff cutC_cs j ξ

lemma xbbK_lintegral_le (d : ℕ) : ∃ A : ℝ≥0∞, A ≠ ⊤ ∧ ∀ j : ℤ, ∫⁻ y : EuclideanSpace ℝ (Fin d), ‖xbbK j y‖ₑ ≤ A := by
  obtain ⟨A, hA, hdec⟩ := symK_dec (cutC_contDiff (d := d)) cutC_cs
  refine ⟨A * KP d, ENNReal.mul_ne_top hA KP_ne_top, fun j => ?_⟩
  rw [show (fun y : EuclideanSpace ℝ (Fin d) => ‖xbbK j y‖ₑ) =
      fun y => ‖symK (cutC : EuclideanSpace ℝ (Fin d) → ℂ) j y‖ₑ from by rw [xbbK_coe]]
  exact lintegral_enorm_le_of_dec (hdec j)


lemma xbb_int_kappa : ∫ u : 𝔼, 𝓕⁻ (cutC : 𝔼 → ℂ) u = 1 := by
  obtain ⟨-, -, h3⟩ := schwartz_of_cs (cutC_contDiff (d := d)) cutC_cs
  have h := congrFun h3 0
  rw [Real.fourier_eq'] at h
  simp only [inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    one_smul] at h
  rw [h]
  exact cutC_eq_one_of_le (by simp)

lemma xbb_cv_xbbK_eq (j : ℤ) (W : 𝔼 → ℂ) (x : 𝔼) :
    cv ⇑(xbbK j) W x = ∫ u : 𝔼, 𝓕⁻ (cutC : 𝔼 → ℂ) u * W (x - ((2 : ℝ) ^ j)⁻¹ • u) := by
  have hc : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = (2 : ℝ) ^ j := ⟨_, rfl⟩
  rw [← hcdef] at hc ⊢
  have e1 : ∀ y : 𝔼, xbbK j y * W (x - y) =
      ((c ^ d : ℝ) : ℂ) * ((fun u : 𝔼 => 𝓕⁻ (cutC : 𝔼 → ℂ) u * W (x - c⁻¹ • u)) (c • y)) := by
    intro y
    have h1 : c⁻¹ • (c • y) = y := inv_smul_smul₀ hc.ne' y
    have h2 : xbbK j y = ((c ^ d : ℝ) : ℂ) * 𝓕⁻ (cutC : 𝔼 → ℂ) (c • y) := by
      rw [xbbK_coe, symK_eq, ← hcdef, Complex.real_smul]
    simp only []
    rw [h1, h2]
    ring
  rw [cv_apply]
  simp_rw [e1]
  rw [integral_const_mul, Measure.integral_comp_smul (volume : Measure 𝔼)
    (fun u : 𝔼 => 𝓕⁻ (cutC : 𝔼 → ℂ) u * W (x - c⁻¹ • u)) c]
  simp only [finrank_euclideanSpace, Fintype.card_fin, Complex.real_smul,
    abs_of_pos (inv_pos.2 (pow_pos hc d))]
  rw [← mul_assoc]
  have : ((c ^ d : ℝ) : ℂ) * (((c ^ d)⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (pow_pos hc d).ne']; simp
  rw [this, one_mul]

lemma xbb_inv_pow_tendsto (j₀ : ℤ) :
    Tendsto (fun k : ℕ => ((2 : ℝ) ^ (j₀ + (k : ℤ)))⁻¹) atTop (𝓝 0) := by
  have h1 : Tendsto (fun k : ℕ => (2 : ℝ) ^ (j₀ + (k : ℤ))) atTop atTop := by
    have : (fun k : ℕ => (2 : ℝ) ^ (j₀ + (k : ℤ))) = fun k : ℕ => (2 : ℝ) ^ j₀ * (2 : ℝ) ^ k := by
      funext k; rw [zpow_add₀ (by norm_num), zpow_natCast]
    rw [this]
    exact Tendsto.const_mul_atTop (zpow_pos (by norm_num) j₀) (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  exact tendsto_inv_atTop_zero.comp h1

lemma xbb_approx_core {κ : 𝔼 → ℂ} (hκc : Continuous κ) (hκi : Integrable κ) (h1 : ∫ u : 𝔼, κ u = 1)
    {W : 𝔼 → ℂ} (hW : Continuous W) {L : ℝ} (hb : ∀ z, ‖W z‖ ≤ L) (j₀ : ℤ) (x : 𝔼) :
    Tendsto (fun k : ℕ => ∫ u : 𝔼, κ u * W (x - ((2 : ℝ) ^ (j₀ + (k : ℤ)))⁻¹ • u)) atTop (𝓝 (W x)) := by
  have hlim : Tendsto (fun k : ℕ => ∫ u : 𝔼, κ u * W (x - ((2 : ℝ) ^ (j₀ + (k : ℤ)))⁻¹ • u))
      atTop (𝓝 (∫ u : 𝔼, κ u * W x)) := by
    refine tendsto_integral_of_dominated_convergence (fun u => L * ‖κ u‖) ?_ ?_ ?_ ?_
    · intro k
      have hcomp : Continuous (fun u : 𝔼 => W (x - ((2 : ℝ) ^ (j₀ + (k : ℤ)))⁻¹ • u)) :=
        hW.comp (by fun_prop)
      exact hκc.aestronglyMeasurable.mul hcomp.aestronglyMeasurable
    · exact hκi.norm.const_mul L
    · intro k
      refine Eventually.of_forall fun u => ?_
      rw [norm_mul]
      calc ‖κ u‖ * ‖W (x - ((2 : ℝ) ^ (j₀ + (k : ℤ)))⁻¹ • u)‖
          ≤ ‖κ u‖ * L := mul_le_mul_of_nonneg_left (hb _) (norm_nonneg _)
        _ = _ := mul_comm _ _
    · refine Eventually.of_forall fun u => ?_
      refine Tendsto.const_mul _ ?_
      have h1 : Tendsto (fun k : ℕ => x - ((2 : ℝ) ^ (j₀ + (k : ℤ)))⁻¹ • u) atTop (𝓝 (x - (0 : ℝ) • u)) :=
        tendsto_const_nhds.sub ((xbb_inv_pow_tendsto j₀).smul_const u)
      rw [zero_smul, sub_zero] at h1
      exact (hW.continuousAt.tendsto).comp h1
  rw [integral_mul_const, h1, one_mul] at hlim
  exact hlim

lemma xbb_approx {W : 𝔼 → ℂ} (hW : Continuous W) {L : ℝ} (hb : ∀ z, ‖W z‖ ≤ L) (j₀ : ℤ) (x : 𝔼) :
    Tendsto (fun k : ℕ => cv ⇑(xbbK (j₀ + (k : ℤ))) W x) atTop (𝓝 (W x)) := by
  obtain ⟨hκc, hκi, -⟩ := schwartz_of_cs (cutC_contDiff (d := d)) cutC_cs
  simp_rw [xbb_cv_xbbK_eq]
  exact xbb_approx_core hκc hκi xbb_int_kappa hW hb j₀ x


lemma xbb_integrable_kernel_mul {K W : 𝔼 → ℂ} (hK : Integrable K) (hWm : AEStronglyMeasurable W volume)
    {L : ℝ} (hb : ∀ z, ‖W z‖ ≤ L) (x : 𝔼) : Integrable (fun y => K y * W (x - y)) := by
  refine hK.mul_bdd (c := L) ?_ (Eventually.of_forall fun y => hb _)
  exact hWm.comp_quasiMeasurePreserving (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving

lemma xbb_cv_sub {K₁ K₂ W : 𝔼 → ℂ} (h₁ : Integrable K₁) (h₂ : Integrable K₂)
    (hWm : AEStronglyMeasurable W volume) {L : ℝ} (hb : ∀ z, ‖W z‖ ≤ L) (x : 𝔼) :
    cv (fun y => K₁ y - K₂ y) W x = cv K₁ W x - cv K₂ W x := by
  simp only [cv_apply]
  rw [← integral_sub (xbb_integrable_kernel_mul h₁ hWm hb x) (xbb_integrable_kernel_mul h₂ hWm hb x)]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  ring

lemma xbb_norm_cv_le {K W : 𝔼 → ℂ} (hKm : Measurable K) {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hK : ∫⁻ y, ‖K y‖ₑ ≤ ENNReal.ofReal M) (hb : ∀ z, ‖W z‖ ≤ L) (x : 𝔼) :
    ‖cv K W x‖ ≤ M * L := by
  have h1 := enorm_cv_le K W x
  have h2 : ∫⁻ y, ‖K y‖ₑ * ‖W (x - y)‖ₑ ≤ ENNReal.ofReal (M * L) := by
    calc ∫⁻ y, ‖K y‖ₑ * ‖W (x - y)‖ₑ ≤ ∫⁻ y, ‖K y‖ₑ * ENNReal.ofReal L := by
          refine lintegral_mono fun y => ?_
          gcongr
          rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hb _)
      _ = (∫⁻ y, ‖K y‖ₑ) * ENNReal.ofReal L := lintegral_mul_const'' _ hKm.enorm.aemeasurable
      _ ≤ ENNReal.ofReal M * ENNReal.ofReal L := by gcongr
      _ = _ := by rw [ENNReal.ofReal_mul hM]
  have h3 := h1.trans h2
  rw [← ofReal_norm] at h3
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3

lemma xbb_fourier_tendsto {h : ℕ → 𝔼 → ℂ} {hLim : 𝔼 → ℂ} {Γ : 𝓢(𝔼, ℂ)} {M : ℝ}
    (hm : ∀ k, AEStronglyMeasurable (h k) volume) (hb : ∀ k x, ‖h k x‖ ≤ M)
    (hlim : ∀ x, Tendsto (fun k => h k x) atTop (𝓝 (hLim x))) (ξ : 𝔼) :
    Tendsto (fun k => 𝓕 (fun x => h k x * Γ x) ξ) atTop (𝓝 (𝓕 (fun x => hLim x * Γ x) ξ)) := by
  simp only [Real.fourier_eq]
  refine tendsto_integral_of_dominated_convergence (fun x => M * ‖Γ x‖) ?_ (Γ.integrable.norm.const_mul M) ?_ ?_
  · intro k
    exact (Continuous.aestronglyMeasurable (by fun_prop)).smul ((hm k).mul Γ.continuous.aestronglyMeasurable)
  · intro k
    refine Eventually.of_forall fun x => ?_
    rw [Circle.norm_smul, norm_mul]
    exact mul_le_mul_of_nonneg_right (hb k x) (norm_nonneg _)
  · refine Eventually.of_forall fun x => ?_
    exact Tendsto.const_smul ((hlim x).mul tendsto_const_nhds) _


lemma xbbQ_eq_N_sq (β : ℝ) (u : 𝔼 → ℂ) : xbbQ β u = xbbN β u ^ (2 : ℝ) := by
  unfold xbbN
  rw [← ENNReal.rpow_mul]
  norm_num

lemma xbbN_fatou (β : ℝ) {u : ℕ → 𝔼 → ℂ} {v : 𝔼 → ℂ} (hu : ∀ k, Integrable (u k))
    (hlim : ∀ ξ : 𝔼, Tendsto (fun k => 𝓕 (u k) ξ) atTop (𝓝 (𝓕 v ξ)))
    {M : ℕ → ℝ≥0∞} {M0 : ℝ≥0∞} (hM : ∀ k, xbbN β (u k) ≤ M k)
    (hMlim : Tendsto M atTop (𝓝 M0)) : xbbN β v ≤ M0 := by
  have hM' : Tendsto (fun k => M k ^ (2 : ℝ)) atTop (𝓝 (M0 ^ (2 : ℝ))) :=
    (ENNReal.continuous_rpow_const.tendsto _).comp hMlim
  have hQ : xbbQ β v ≤ M0 ^ (2 : ℝ) := by
    refine le_of_forall_gt_imp_ge_of_dense fun M1 hM1 => ?_
    refine xbbQ_fatou β hu hlim (M := M1) ?_
    have hev : ∀ᶠ k in atTop, M k ^ (2 : ℝ) < M1 := hM'.eventually (gt_mem_nhds hM1)
    refine (hev.mono fun k hk => ?_).frequently
    rw [xbbQ_eq_N_sq]
    exact (ENNReal.rpow_le_rpow (hM k) (by norm_num)).trans hk.le
  unfold xbbN
  calc xbbQ β v ^ (1 / 2 : ℝ) ≤ (M0 ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hQ (by norm_num)
    _ = M0 := by rw [← ENNReal.rpow_mul]; norm_num

end HRS.Commutator.Whole.XBB
