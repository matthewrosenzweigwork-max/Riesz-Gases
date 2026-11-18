import HRS.Commutator.Whole.ExternalAuxHLS7

/-!
# The dyadic partition of unity and the series of the pieces (packet X-HLS, part 8)
-/

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal FourierTransform ContDiff

noncomputable section

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ}

/-- Localisation of the dyadic partition of unity at `ξ ≠ 0`. -/
lemma cmxHLS_rho_support (ξ : Euc d) (hξ : ξ ≠ 0) :
    ∃ J : ℤ, (∀ j : ℤ, j ≠ J → j ≠ J + 1 → cmxMY_rho (((2 : ℝ) ^ j)⁻¹ • ξ) = 0) ∧
      cmxMY_rho (((2 : ℝ) ^ J)⁻¹ • ξ) + cmxMY_rho (((2 : ℝ) ^ (J + 1))⁻¹ • ξ) = 1 := by
  have hpos : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  obtain ⟨J, hJ⟩ := exists_mem_Ico_zpow hpos (by norm_num : (1 : ℝ) < 2)
  have ha : 0 < (2 : ℝ) ^ J := zpow_pos (by norm_num) J
  have hJ1 : (2 : ℝ) ^ (J + 1) = 2 * (2 : ℝ) ^ J := by
    rw [zpow_add_one₀ (by norm_num), mul_comm]
  have hnorm : ∀ j : ℤ, ‖((2 : ℝ) ^ j)⁻¹ • ξ‖ = ‖ξ‖ / (2 : ℝ) ^ j := by
    intro j
    have : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
    rw [norm_smul, norm_inv, Real.norm_of_nonneg this.le, inv_mul_eq_div]
  refine ⟨J, fun j hj1 hj2 => ?_, ?_⟩
  · have hjpos : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
    rcases lt_or_gt_of_ne hj1 with hlt | hgt
    · -- j ≤ J - 1
      have h1 : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ (J - 1) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      have h2 : (2 : ℝ) ^ (J - 1) = (2 : ℝ) ^ J / 2 := by
        rw [zpow_sub_one₀ (by norm_num)]; ring
      apply cmxMY_rho_eq_zero_of_ge
      rw [hnorm, le_div_iff₀ hjpos]
      have := hJ.1
      nlinarith
    · -- j ≥ J + 2
      have hj3 : J + 2 ≤ j := by omega
      have h1 : (2 : ℝ) ^ (J + 2) ≤ (2 : ℝ) ^ j := zpow_le_zpow_right₀ (by norm_num) hj3
      have h2 : (2 : ℝ) ^ (J + 2) = 4 * (2 : ℝ) ^ J := by
        rw [zpow_add₀ (by norm_num)]; norm_num; ring
      apply cmxMY_rho_eq_zero_of_le
      rw [hnorm, div_le_iff₀ hjpos]
      have := hJ.2
      rw [hJ1] at this
      nlinarith
  · have hc1 : chi (((2 : ℝ) ^ (J + 1))⁻¹ • ξ) = 1 := by
      apply cmxFB_chi_one
      rw [hnorm, div_le_iff₀ (zpow_pos (by norm_num) _), one_mul]
      have := hJ.2
      linarith
    have hc2 : chi ((2 : ℝ) • (((2 : ℝ) ^ J)⁻¹ • ξ)) = 0 := by
      apply cmxFB_chi_zero
      rw [norm_smul, hnorm, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), ← mul_div_assoc,
        le_div_iff₀ ha]
      have := hJ.1
      linarith
    have hshift : (2 : ℝ) • (((2 : ℝ) ^ (J + 1))⁻¹ • ξ) = ((2 : ℝ) ^ J)⁻¹ • ξ := by
      rw [smul_smul, hJ1, mul_inv, ← mul_assoc]
      have : (2 : ℝ) * (2 : ℝ)⁻¹ = 1 := by norm_num
      rw [this, one_mul]
    unfold cmxMY_rho
    rw [hshift, hc1, hc2]
    ring

lemma cmxHLS_rho_hasSum (ξ : Euc d) (hξ : ξ ≠ 0) :
    HasSum (fun j : ℤ => cmxMY_rho (((2 : ℝ) ^ j)⁻¹ • ξ)) 1 := by
  obtain ⟨J, h0, h1⟩ := cmxHLS_rho_support ξ hξ
  have hs : HasSum (fun j : ℤ => cmxMY_rho (((2 : ℝ) ^ j)⁻¹ • ξ))
      (∑ j ∈ ({J, J + 1} : Finset ℤ), cmxMY_rho (((2 : ℝ) ^ j)⁻¹ • ξ)) :=
    hasSum_sum_of_ne_finset_zero (fun j hj => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
      exact h0 j hj.1 hj.2)
  rwa [Finset.sum_pair (by omega), h1] at hs


lemma cmxHLS_rho_abs_le (η : Euc d) : |cmxMY_rho η| ≤ 1 := by
  unfold cmxMY_rho
  have h1 := cmxFB_chi_nonneg η
  have h2 := cmxFB_chi_le_one η
  have h3 := cmxFB_chi_nonneg ((2 : ℝ) • η)
  have h4 := cmxFB_chi_le_one ((2 : ℝ) • η)
  rw [abs_le]; constructor <;> linarith

lemma cmxHLS_sym_hasSum (s : ℝ) (f : Euc d → ℂ) (ξ : Euc d) (hξ : ξ ≠ 0) :
    HasSum (fun j : ℤ => cmxHLS_sym s f j ξ) ((((2 * Real.pi * ‖ξ‖) ^ s : ℝ) : ℂ) * f ξ) := by
  have h := (Complex.hasSum_ofReal.2 (cmxHLS_rho_hasSum ξ hξ)).mul_left
    ((((2 * Real.pi * ‖ξ‖) ^ s : ℝ) : ℂ) * f ξ)
  convert h using 1
  · funext j
    unfold cmxHLS_sym
    push_cast
    ring
  · push_cast; ring

lemma cmxHLS_sym_summable_norm (s : ℝ) (f : Euc d → ℂ) (ξ : Euc d) (hξ : ξ ≠ 0) :
    Summable (fun j : ℤ => ‖cmxHLS_sym s f j ξ‖) ∧
      ∑' j : ℤ, ‖cmxHLS_sym s f j ξ‖ ≤ 2 * ((2 * Real.pi * ‖ξ‖) ^ s * ‖f ξ‖) := by
  obtain ⟨J, h0, -⟩ := cmxHLS_rho_support ξ hξ
  have hz : ∀ j : ℤ, j ∉ ({J, J + 1} : Finset ℤ) → ‖cmxHLS_sym s f j ξ‖ = 0 := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    unfold cmxHLS_sym
    rw [h0 j hj.1 hj.2]; simp
  have hA : 0 ≤ (2 * Real.pi * ‖ξ‖) ^ s := Real.rpow_nonneg (by positivity) s
  have hb : ∀ j : ℤ, ‖cmxHLS_sym s f j ξ‖ ≤ (2 * Real.pi * ‖ξ‖) ^ s * ‖f ξ‖ := by
    intro j
    unfold cmxHLS_sym
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hA]
    have := cmxHLS_rho_abs_le (((2 : ℝ) ^ j)⁻¹ • ξ)
    have hf0 := norm_nonneg (f ξ)
    calc (2 * Real.pi * ‖ξ‖) ^ s * |cmxMY_rho (((2 : ℝ) ^ j)⁻¹ • ξ)| * ‖f ξ‖
        ≤ (2 * Real.pi * ‖ξ‖) ^ s * 1 * ‖f ξ‖ := by gcongr
      _ = _ := by ring
  have hsum : Summable (fun j : ℤ => ‖cmxHLS_sym s f j ξ‖) := summable_of_ne_finset_zero hz
  refine ⟨hsum, ?_⟩
  rw [tsum_eq_sum hz, Finset.sum_pair (by omega)]
  have := hb J; have := hb (J + 1)
  linarith


/-- The series of dyadic pieces. -/
theorem cmxHLS_piece_hasSum (hd : 1 ≤ d) {f : Euc d → ℂ} (hf : ContDiff ℝ ∞ f) (s : ℝ)
    (hint : Integrable (fun ξ : Euc d => (2 * Real.pi * ‖ξ‖) ^ s * ‖f ξ‖)) (x : Euc d) :
    HasSum (fun j : ℤ => cmxHLS_piece s f j x)
      (𝓕⁻ (fun ξ : Euc d => (((2 * Real.pi * ‖ξ‖) ^ s : ℝ) : ℂ) * f ξ) x) := by
  set Fj : ℤ → Euc d → ℂ := fun j ξ =>
    Complex.exp (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) * Complex.I) * cmxHLS_sym s f j ξ with hFj
  set g : Euc d → ℂ := fun ξ => Complex.exp (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) * Complex.I) *
    ((((2 * Real.pi * ‖ξ‖) ^ s : ℝ) : ℂ) * f ξ) with hg
  have hnorm : ∀ (j : ℤ) (ξ : Euc d), ‖Fj j ξ‖ = ‖cmxHLS_sym s f j ξ‖ := by
    intro j ξ
    rw [hFj]; simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hmeas : ∀ j : ℤ, AEStronglyMeasurable (Fj j) volume := by
    intro j
    refine Continuous.aestronglyMeasurable ?_
    exact (Complex.continuous_exp.comp (Continuous.mul (Complex.continuous_ofReal.comp
      (by fun_prop)) continuous_const)).mul (cmxHLS_sym_contDiff hf s j).continuous
  have hlim : ∀ᵐ ξ ∂(volume : Measure (Euc d)), HasSum (fun j => Fj j ξ) (g ξ) := by
    filter_upwards [ae_ne_zero_euc hd] with ξ hξ
    exact (cmxHLS_sym_hasSum s f ξ hξ).mul_left _
  have hbs : ∀ᵐ ξ ∂(volume : Measure (Euc d)), Summable (fun j : ℤ => ‖cmxHLS_sym s f j ξ‖) := by
    filter_upwards [ae_ne_zero_euc hd] with ξ hξ
    exact (cmxHLS_sym_summable_norm s f ξ hξ).1
  have hbint : Integrable (fun ξ : Euc d => ∑' j : ℤ, ‖cmxHLS_sym s f j ξ‖) := by
    refine (hint.const_mul 2).mono' ?_ ?_
    · exact (AEMeasurable.tsum (fun j => (cmxHLS_sym_contDiff hf s j).continuous.norm.aemeasurable)).aestronglyMeasurable
    · filter_upwards [ae_ne_zero_euc hd] with ξ hξ
      rw [Real.norm_of_nonneg (tsum_nonneg fun j => norm_nonneg _)]
      exact (cmxHLS_sym_summable_norm s f ξ hξ).2
  have h := hasSum_integral_of_dominated_convergence (fun j ξ => ‖cmxHLS_sym s f j ξ‖) hmeas
    (fun j => Eventually.of_forall fun ξ => (hnorm j ξ).le) hbs hbint hlim
  convert h using 1
  · funext j
    unfold cmxHLS_piece
    rw [Real.fourierInv_eq']
    simp only [smul_eq_mul]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [hFj]
  · rw [Real.fourierInv_eq']
    simp only [smul_eq_mul, hg]

end HRS.Commutator.Whole
