import HRS.Commutator.Whole.ExternalAuxHLS5
import HRS.Commutator.Whole.ExternalAuxHLS8

/-!
# The Riesz representation of the `-σ` pieces and the Fubini pairing (packet X-HLS, part 9)
-/

open MeasureTheory Filter Topology Metric Real Set
open scoped ENNReal NNReal FourierTransform ContDiff

noncomputable section

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ}

/-- `∫ |z|^{σ-d} (1+|x₀-z|)^{-N} dz < ∞`. -/
lemma cmxHLS_kernel_decay_integrable (hd : 1 ≤ d) {σ : ℝ} (hσ : 0 < σ) (hσd : σ < d)
    (x₀ : Euc d) {N : ℝ} (hN : (d : ℝ) < N) :
    Integrable (fun z : Euc d => ‖z‖ ^ (σ - (d : ℝ)) * (1 + ‖x₀ - z‖) ^ (-N)) := by
  have hloc : IntegrableOn (fun z : Euc d => ‖z‖ ^ (σ - (d : ℝ))) (ball 0 1) := by
    refine integrableOn_ball_of_norm_le_rpow (μ := volume) (f := fun z : Euc d => ‖z‖ ^ (σ - (d : ℝ)))
      (C := 1) (α := (d : ℝ) - σ) (r := 1) (by rw [finrank_euclideanSpace_fin]; exact hd) ?_ ?_ ?_
    · rw [finrank_euclideanSpace_fin]; linarith
    · exact Eventually.of_forall fun z => by
        rw [one_mul, show -((d : ℝ) - σ) = σ - (d : ℝ) by ring,
          Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)]
    · exact (measurable_norm.pow_const _).aestronglyMeasurable
  have hind : Integrable (Set.indicator (ball (0 : Euc d) 1) fun z : Euc d => ‖z‖ ^ (σ - (d : ℝ))) :=
    (integrable_indicator_iff measurableSet_ball).2 hloc
  have hI : Integrable (fun z : Euc d => (1 + ‖x₀ - z‖) ^ (-N)) := by
    have := (integrable_one_add_norm (μ := (volume : Measure (Euc d))) (r := N)
      (by rwa [finrank_euclideanSpace_fin])).comp_sub_left x₀
    exact this
  refine (hind.add hI).mono' ?_ (Eventually.of_forall fun z => ?_)
  · refine ((measurable_norm.pow_const _).mul ?_).aestronglyMeasurable
    exact ((measurable_const.add (measurable_norm.comp (measurable_const.sub measurable_id))).pow_const _)
  · have h1 : 0 ≤ ‖z‖ ^ (σ - (d : ℝ)) := Real.rpow_nonneg (norm_nonneg z) _
    have h2 : 0 ≤ (1 + ‖x₀ - z‖) ^ (-N) := Real.rpow_nonneg (by positivity) _
    rw [Real.norm_of_nonneg (mul_nonneg h1 h2)]
    simp only [Pi.add_apply]
    by_cases hz : z ∈ ball (0 : Euc d) 1
    · rw [Set.indicator_of_mem hz]
      have h3 : (1 + ‖x₀ - z‖) ^ (-N) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg (x₀ - z)]) (by linarith)
      have : ‖z‖ ^ (σ - (d : ℝ)) * (1 + ‖x₀ - z‖) ^ (-N) ≤ ‖z‖ ^ (σ - (d : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left h3 h1
      linarith
    · rw [Set.indicator_of_notMem hz]
      have hz1 : 1 ≤ ‖z‖ := by simpa using hz
      have h3 : ‖z‖ ^ (σ - (d : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hz1 (by linarith)
      have : ‖z‖ ^ (σ - (d : ℝ)) * (1 + ‖x₀ - z‖) ^ (-N) ≤ 1 * (1 + ‖x₀ - z‖) ^ (-N) :=
        mul_le_mul_of_nonneg_right h3 h2
      linarith


lemma cmxHLS_sym_hasCompactSupport {f : Euc d → ℂ} (s : ℝ) (j : ℤ) :
    HasCompactSupport (cmxHLS_sym s f j) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Euc d)
    ((2 : ℝ) ^ (j + 1))) ?_
  intro ξ hξ
  by_contra h
  have h' : (2 : ℝ) ^ (j + 1) < ‖ξ‖ := by simpa using h
  exact hξ (cmxHLS_sym_support s f j ξ h'.le)

/-- The Fourier-side symbol of a dyadic piece, as a Schwartz function. -/
def cmxHLS_symS (s : ℝ) (F : SchwartzMap (Euc d) ℂ) (j : ℤ) : SchwartzMap (Euc d) ℂ :=
  (cmxHLS_sym_hasCompactSupport (f := (⇑F : Euc d → ℂ)) s j).toSchwartzMap
    (cmxHLS_sym_contDiff (F.smooth ⊤) s j)

lemma cmxHLS_symS_coe (s : ℝ) (F : SchwartzMap (Euc d) ℂ) (j : ℤ) :
    (⇑(cmxHLS_symS s F j) : Euc d → ℂ) = cmxHLS_sym s (⇑F) j := rfl

/-- The dyadic piece as a Schwartz function. -/
def cmxHLS_pieceS (s : ℝ) (F : SchwartzMap (Euc d) ℂ) (j : ℤ) : SchwartzMap (Euc d) ℂ :=
  𝓕⁻ (cmxHLS_symS s F j)

lemma cmxHLS_pieceS_coe (s : ℝ) (F : SchwartzMap (Euc d) ℂ) (j : ℤ) :
    (⇑(cmxHLS_pieceS s F j) : Euc d → ℂ) = cmxHLS_piece s (⇑F) j := by
  unfold cmxHLS_pieceS cmxHLS_piece
  rw [SchwartzMap.fourierInv_coe, cmxHLS_symS_coe]

lemma cmxHLS_fourier_pieceS (s : ℝ) (F : SchwartzMap (Euc d) ℂ) (j : ℤ) :
    𝓕 (⇑(cmxHLS_pieceS s F j) : Euc d → ℂ) = cmxHLS_sym s (⇑F) j := by
  have h : (𝓕 (cmxHLS_pieceS s F j) : SchwartzMap (Euc d) ℂ) = cmxHLS_symS s F j := by
    unfold cmxHLS_pieceS
    exact FourierTransform.fourier_fourierInv_eq _
  have h2 : (⇑(𝓕 (cmxHLS_pieceS s F j) : SchwartzMap (Euc d) ℂ) : Euc d → ℂ) =
      𝓕 (⇑(cmxHLS_pieceS s F j)) := SchwartzMap.fourier_coe _
  rw [← h2, h]
  rfl


/-- Schwartz decay in the form `‖R y‖ ≤ C (1+‖y‖)^{-N}`. -/
lemma cmxHLS_schwartz_rpow_decay (R : SchwartzMap (Euc d) ℂ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Euc d, ‖R y‖ ≤ C * (1 + ‖y‖) ^ (-(N : ℝ)) := by
  obtain ⟨-, hdec⟩ := cmxHLS_schwartz_dec R
  obtain ⟨C, hC0, hC⟩ := hdec 0 N
  refine ⟨C, hC0, fun y => ?_⟩
  have h := hC y
  rw [norm_iteratedFDeriv_zero] at h
  have hp : 0 < (1 + ‖y‖) ^ N := by positivity
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hp]
  linarith

theorem cmxHLS_repr_piece (hd : 1 ≤ d) {σ : ℝ} (hσ : 0 < σ) (hσd : σ < d)
    (F : SchwartzMap (Euc d) ℂ) (j : ℤ) (x₀ : Euc d) :
    ((Real.Gamma (((d : ℝ) - σ) / 2) : ℝ) : ℂ) *
        ∫ z : Euc d, ((‖z‖ ^ (σ - (d : ℝ)) : ℝ) : ℂ) * cmxHLS_piece 0 (⇑F) j (x₀ - z)
      = (((π ^ (((d : ℝ) - σ) - (d : ℝ) / 2) * Real.Gamma (σ / 2) * (2 * π) ^ σ : ℝ)) : ℂ) *
        cmxHLS_piece (-σ) (⇑F) j x₀ := by
  have hγ : 0 < (d : ℝ) - σ := by linarith
  have hγd : (d : ℝ) - σ < d := by linarith
  set U : Euc d → ℂ := cmxHLS_sym 0 (⇑F) j with hU
  set H : Euc d → ℂ := fun ξ => Complex.exp (((2 * π * inner ℝ ξ x₀ : ℝ) : ℂ) * Complex.I) * U ξ
    with hH
  have hUc : Continuous U := (cmxHLS_sym_contDiff (F.smooth ⊤) 0 j).continuous
  have hHc : Continuous H := by
    rw [hH]
    exact (Complex.continuous_exp.comp (Continuous.mul (Complex.continuous_ofReal.comp
      (by fun_prop)) continuous_const)).mul hUc
  have hnormH : ∀ ξ : Euc d, ‖H ξ‖ = ‖U ξ‖ := by
    intro ξ; rw [hH]; simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hHint : Integrable H :=
    (cmxHLS_sym_integrable (F.smooth ⊤) 0 j).norm.mono' hHc.aestronglyMeasurable
      (Eventually.of_forall fun ξ => by rw [hnormH])
  have hmod : ∀ z : Euc d, 𝓕 H z = cmxHLS_piece 0 (⇑F) j (x₀ - z) := fun z =>
    cmxHLS_modulation U x₀ z
  -- decay of the `0`-piece
  obtain ⟨C, hC0, hC⟩ := cmxHLS_schwartz_rpow_decay (cmxHLS_pieceS 0 F j) (d + 1)
  have hCp : ∀ y : Euc d, ‖cmxHLS_piece 0 (⇑F) j y‖ ≤ C * (1 + ‖y‖) ^ (-((d + 1 : ℕ) : ℝ)) := by
    intro y; have := hC y; rwa [cmxHLS_pieceS_coe] at this
  have hL : Integrable (fun x : Euc d => ‖x‖ ^ (-((d : ℝ) - σ)) * ‖𝓕 H x‖) := by
    have hbase := (cmxHLS_kernel_decay_integrable hd hσ hσd x₀
      (N := (((d + 1 : ℕ) : ℝ))) (by push_cast; linarith)).const_mul C
    refine hbase.mono' ?_ (Eventually.of_forall fun x => ?_)
    · refine ((measurable_norm.pow_const _).mul ?_).aestronglyMeasurable
      have : Continuous (𝓕 H) :=
        VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hHint
      exact this.norm.measurable
    · rw [hmod x, neg_sub, Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
        (norm_nonneg _))]
      have := hCp (x₀ - x)
      calc ‖x‖ ^ (σ - (d : ℝ)) * ‖cmxHLS_piece 0 (⇑F) j (x₀ - x)‖
          ≤ ‖x‖ ^ (σ - (d : ℝ)) * (C * (1 + ‖x₀ - x‖) ^ (-((d + 1 : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_left this (Real.rpow_nonneg (norm_nonneg _) _)
        _ = C * (‖x‖ ^ (σ - (d : ℝ)) * (1 + ‖x₀ - x‖) ^ (-((d + 1 : ℕ) : ℝ))) := by ring
  have hR : Integrable (fun ξ : Euc d => ‖ξ‖ ^ (((d : ℝ) - σ) - (d : ℝ)) * ‖H ξ‖) := by
    have hc : 0 < (2 : ℝ) ^ j / 2 := by have := zpow_pos (by norm_num : (0 : ℝ) < 2) j; positivity
    have hbase := (cmxHLS_sym_integrable (F.smooth ⊤) 0 j).norm.const_mul (((2 : ℝ) ^ j / 2) ^ (-σ))
    refine hbase.mono' ?_ (Eventually.of_forall fun ξ => ?_)
    · exact ((measurable_norm.pow_const _).mul hHc.norm.measurable).aestronglyMeasurable
    · rw [show ((d : ℝ) - σ) - (d : ℝ) = -σ by ring, hnormH,
        Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (norm_nonneg _))]
      by_cases hξ : ‖ξ‖ ≤ (2 : ℝ) ^ j / 2
      · have : U ξ = 0 := by
          rw [hU]; unfold cmxHLS_sym
          rw [cmxMY_rho_eq_zero_of_le, mul_zero, Complex.ofReal_zero, zero_mul]
          rw [norm_smul, norm_inv, Real.norm_of_nonneg (zpow_pos (by norm_num) j).le,
            inv_mul_le_iff₀ (zpow_pos (by norm_num) j)]
          linarith
        rw [this, norm_zero, mul_zero]; positivity
      · have hξ' : (2 : ℝ) ^ j / 2 < ‖ξ‖ := not_le.1 hξ
        have h1 : ‖ξ‖ ^ (-σ) ≤ ((2 : ℝ) ^ j / 2) ^ (-σ) :=
          Real.rpow_le_rpow_of_nonpos hc hξ'.le (by linarith)
        exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  have key := cmxHLS_riesz_general hd hγ hγd H hHint hHc.measurable hL hR
  have hlhs : ∫ x : Euc d, ((‖x‖ ^ (-((d : ℝ) - σ)) : ℝ) : ℂ) * 𝓕 H x =
      ∫ z : Euc d, ((‖z‖ ^ (σ - (d : ℝ)) : ℝ) : ℂ) * cmxHLS_piece 0 (⇑F) j (x₀ - z) := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hmod z, neg_sub]
  have hrhs : ∫ ξ : Euc d, ((‖ξ‖ ^ (((d : ℝ) - σ) - (d : ℝ)) : ℝ) : ℂ) * H ξ =
      (((2 * π) ^ σ : ℝ) : ℂ) * cmxHLS_piece (-σ) (⇑F) j x₀ := by
    unfold cmxHLS_piece
    rw [Real.fourierInv_eq', ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_ne_zero_euc hd] with ξ hξ
    have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    simp only [smul_eq_mul, hH, hU, cmxHLS_sym]
    have hk : ‖ξ‖ ^ (-σ) = (2 * π) ^ σ * (2 * π * ‖ξ‖) ^ (-σ) := by
      rw [Real.mul_rpow (by positivity) hn.le, ← mul_assoc, ← Real.rpow_add (by positivity),
        add_neg_cancel, Real.rpow_zero, one_mul]
    rw [show ((d : ℝ) - σ) - (d : ℝ) = -σ by ring, hk, Real.rpow_zero]
    push_cast
    ring
  rw [hlhs, hrhs] at key
  have hc : (((π ^ (((d : ℝ) - σ) - (d : ℝ) / 2) * Real.Gamma (σ / 2) * (2 * π) ^ σ : ℝ)) : ℂ) =
      (((π ^ (((d : ℝ) - σ) - (d : ℝ) / 2) * Real.Gamma (((d : ℝ) - ((d : ℝ) - σ)) / 2)) : ℝ) : ℂ) *
        (((2 * π) ^ σ : ℝ) : ℂ) := by
    rw [show ((d : ℝ) - ((d : ℝ) - σ)) / 2 = σ / 2 by ring]
    push_cast
    ring
  rw [hc, mul_assoc, ← key]

end HRS.Commutator.Whole
