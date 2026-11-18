import HRS.MS.CritWholeFieldMoment

/-!
# S8.1 XS, TT05: truncated quadratic envelope in `L^{2q}(μ^n)`

Whole-space port of `HRS.TaylorAux.taylor_B1_bound`: Jensen in `y` against the (mass-bounded) test `φ`, then the
`L^{4q}` field moment `s81b_field_moment`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole HRS.MS.Wr HRS.TaylorAux

namespace HRS.Whole.S81b

variable {d : ℕ} {M βm βp : ℝ}

theorem s81b_critG_meas (hd : 1 ≤ d) : Measurable (critG d) := by
  have hs0 : ((d : ℝ) / 2) ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  exact Q34.measurable_rieszKernel hs0

theorem s81b_trunc_meas (hd : 1 ≤ d) (H : ℝ) : Measurable (truncKernel d ((d : ℝ) / 2) H) :=
  (s81b_critG_meas hd).min measurable_const

theorem s81b_conv_meas (hd : 1 ≤ d) (D : Data d M βm βp) : Measurable (convMeasure (critG d) (mu D)) := by
  have hs0 : 0 < ((d : ℝ) / 2) := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  have := Q34.isProbabilityMeasure_nu D.prob
  exact wr13a_conv_meas hs0 (mu D)

theorem s81b_fieldH_meas (hd : 1 ≤ d) (D : Data d M βm βp) (N : ℕ) (i : Fin (N - 1)) (H : ℝ) :
    Measurable (fun p : EucConfig d (N - 1) × Euc d => fieldH D N i H p.1 p.2) := by
  unfold fieldH
  refine Measurable.sub ?_ ?_
  · refine Measurable.const_mul (Finset.measurable_sum _ fun j _ => ?_) _
    exact (s81b_trunc_meas hd H).comp (measurable_snd.sub ((measurable_pi_apply j).comp measurable_fst))
  · exact ((s81b_conv_meas hd D).comp measurable_snd).const_mul _

theorem s81b_field_lower (hd : 2 ≤ d) (D : Data d M βm βp) (hβm : 0 < βm) (N : ℕ) (i : Fin (N - 1)) (H : ℝ)
    (hH : 0 ≤ H) (Y : EucConfig d (N - 1)) (y : Euc d) :
    -fieldLowerBound d M βp ≤ fieldH D N i H Y y := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < ((d : ℝ) / 2) := by linarith
  have hsd : ((d : ℝ) / 2) < d := by linarith
  have hkern : ∀ z : Euc d, 0 ≤ critG d z := fun z => by
    rw [critG, Q34.rieszKernel_eq hs0.ne']; exact Real.rpow_nonneg (norm_nonneg _) _
  have hβ0 : 0 < D.beta := hβm.trans_le D.beta_mem.1
  have h1 : 0 ≤ (D.beta / N) * ∑ j ∈ Finset.univ.erase i, truncKernel d ((d : ℝ) / 2) H (y - Y j) :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => le_min (hkern _) hH)
  have h2 := (wr13a_potential_bound hd1 hs0 hsd D.prob D.bound y).2.2
  have h3 : D.beta * convMeasure (critG d) (mu D) y ≤ max βp 0 * max (potentialBound d ((d : ℝ) / 2) M) 0 :=
    mul_le_mul (D.beta_mem.2.trans (le_max_left _ _)) (h2.trans (le_max_left _ _))
      (wr13a_conv_nonneg hs0 _ y) (le_max_right _ _)
  unfold fieldH fieldLowerBound
  linarith

theorem s81b_field_bdd (hd : 2 ≤ d) (D : Data d M βm βp) (hβm : 0 < βm) (N : ℕ) (i : Fin (N - 1)) (H : ℝ)
    (hH : 0 ≤ H) (y : Euc d) : ∃ B : ℝ, ∀ Y : EucConfig d (N - 1), |fieldH D N i H Y y| ≤ B := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < ((d : ℝ) / 2) := by linarith
  have hsd : ((d : ℝ) / 2) < d := by linarith
  have hkern : ∀ z : Euc d, 0 ≤ critG d z := fun z => by
    rw [critG, Q34.rieszKernel_eq hs0.ne']; exact Real.rpow_nonneg (norm_nonneg _) _
  have hβ0 : 0 < D.beta := hβm.trans_le D.beta_mem.1
  obtain ⟨-, hh0, hh1⟩ := wr13a_potential_bound hd1 hs0 hsd D.prob D.bound y
  refine ⟨(D.beta / N) * (((N - 1 : ℕ) : ℝ) * H) + D.beta * potentialBound d ((d : ℝ) / 2) M, fun Y => ?_⟩
  unfold fieldH
  have hg0 : ∀ j, 0 ≤ truncKernel d ((d : ℝ) / 2) H (y - Y j) := fun j => le_min (hkern _) hH
  have hgH : ∀ j, truncKernel d ((d : ℝ) / 2) H (y - Y j) ≤ H := fun j => min_le_right _ _
  have hsum : ∑ j ∈ Finset.univ.erase i, truncKernel d ((d : ℝ) / 2) H (y - Y j) ≤ ((N - 1 : ℕ) : ℝ) * H := by
    calc _ ≤ ∑ _j ∈ Finset.univ.erase i, H := Finset.sum_le_sum fun j _ => hgH j
      _ = ((Finset.univ.erase i).card : ℝ) * H := by simp
      _ ≤ ((N - 1 : ℕ) : ℝ) * H := by
        have : ((Finset.univ.erase i).card : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by
          exact_mod_cast (Finset.card_erase_le).trans (by simp)
        exact mul_le_mul_of_nonneg_right this hH
  have hs : 0 ≤ ∑ j ∈ Finset.univ.erase i, truncKernel d ((d : ℝ) / 2) H (y - Y j) :=
    Finset.sum_nonneg fun j _ => hg0 j
  have hb : 0 ≤ D.beta / N := by positivity
  rw [abs_le]; constructor
  · nlinarith [mul_nonneg hb hs, mul_le_mul_of_nonneg_left hh1 hβ0.le]
  · nlinarith [mul_le_mul_of_nonneg_left hsum hb, mul_nonneg hβ0.le hh0]

set_option maxHeartbeats 1600000 in
theorem s81b_truncated_quadratic_product (hd : 2 ≤ d) (M βm βp : ℝ)
    (hβm : 0 < βm) (hβ : βm ≤ βp) (q : ℕ) (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ D : Data d M βm βp, ∀ N : ℕ, 2 ≤ N →
      ∀ i : Fin (N - 1), ∀ H : ℝ, 2 ≤ H → ∀ x : Euc d,
      ∀ φ ∈ tests d x,
        Measurable (quadraticEnvelope D N i H φ) ∧
        HRS.TaylorAux.taylorLp (product D (N - 1)) ((2 * q : ℕ) : ℝ)
          (quadraticEnvelope D N i H φ) ≤
            ENNReal.ofReal (C * (Real.log H / N + H ^ 2 / (N : ℝ) ^ 2 +
              1 / H ^ 2 + 1 / (N : ℝ) ^ 2)) := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < ((d : ℝ) / 2) := by linarith
  have hsd : ((d : ℝ) / 2) < d := by linarith
  obtain ⟨Cf, hCf0, hCf⟩ := s81b_field_moment hd M βm βp hβm hβ q hq
  set Ch : ℝ := max (potentialBound d ((d : ℝ) / 2) M) 0 with hChdef
  have hCh0 : 0 ≤ Ch := le_max_right _ _
  set K : ℝ := fieldLowerBound d M βp with hKdef
  have hβp : 0 < βp := hβm.trans_le hβ
  have hK0 : 0 ≤ K := by rw [hKdef]; unfold fieldLowerBound; positivity
  set Cp : ℝ := max 1 Ch with hCpdef
  have hCp0 : 0 ≤ Cp := le_trans zero_le_one (le_max_left _ _)
  refine ⟨Cp * Real.exp K * max Cf 1, by positivity, fun D N hN i H hH x φ hφ => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hH0 : 0 < H := by linarith
  have hp0 : (0 : ℝ) < ((2 * q : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * q)
  have hprob : IsProbabilityMeasure (mu D) := Q34.isProbabilityMeasure_nu D.prob
  set μ : Measure (Euc d) := mu D with hμdef
  set Pm : Measure (EucConfig d (N - 1)) := product D (N - 1) with hPm
  set Θ : ℝ := Real.log H / N + H ^ 2 / (N : ℝ) ^ 2 + 1 / H ^ 2 + 1 / (N : ℝ) ^ 2 with hΘ
  have hlog : 0 ≤ Real.log H := Real.log_nonneg (by linarith)
  have hΘ0 : 0 ≤ Θ := by positivity
  have hgm := s81b_critG_meas hd1
  have hφm : Measurable φ := by
    rcases hφ with rfl | rfl
    · exact measurable_const
    · exact hgm.comp (measurable_const.sub measurable_id)
  have hmass : ∫⁻ y, ENNReal.ofReal (φ y) ∂μ ≤ ENNReal.ofReal Cp := by
    rcases hφ with rfl | rfl
    · simp only [ENNReal.ofReal_one, lintegral_const, measure_univ, mul_one]
      exact ENNReal.ofReal_one.symm.le.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    · obtain ⟨hi, -, hle⟩ := wr13a_potential_bound hd1 hs0 hsd D.prob D.bound x
      have hnn : ∀ y, 0 ≤ critG d (x - y) := fun y => by
        rw [critG, Q34.rieszKernel_eq hs0.ne']; exact Real.rpow_nonneg (norm_nonneg _) _
      rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hnn)]
      exact ENNReal.ofReal_le_ofReal (hle.trans ((le_max_left _ _).trans (le_max_right _ _)))
  have hφ0 : ∀ y, 0 ≤ φ y := by
    rcases hφ with rfl | rfl
    · intro y; exact zero_le_one
    · intro y; show 0 ≤ critG d (x - y)
      rw [critG, Q34.rieszKernel_eq hs0.ne']; exact Real.rpow_nonneg (norm_nonneg _) _
  set Fm : Euc d → ℝ≥0∞ := fun y => ENNReal.ofReal (φ y) with hFm
  have hFmm : Measurable Fm := hφm.ennreal_ofReal
  have hvm := s81b_fieldH_meas hd1 D N i H
  set Gf : EucConfig d (N - 1) → Euc d → ℝ≥0∞ :=
    fun Y y => ENNReal.ofReal (Real.exp K * fieldH D N i H Y y ^ 2) with hGf
  have hGfm : Measurable (Function.uncurry Gf) := by
    refine Measurable.ennreal_ofReal ?_
    exact measurable_const.mul (hvm.pow_const 2)
  have hGfy : ∀ Y, Measurable (Gf Y) := fun Y =>
    (hGfm.comp (measurable_const.prodMk measurable_id) : Measurable fun y => Function.uncurry Gf (Y, y))
  have hGfY : ∀ y, Measurable (fun Y => Gf Y y) := fun y =>
    (hGfm.comp (measurable_id.prodMk measurable_const) : Measurable fun Y => Function.uncurry Gf (Y, y))
  have hEm : Measurable (quadraticEnvelope D N i H φ) := by
    unfold quadraticEnvelope
    refine Measurable.lintegral_prod_right' (f := fun p : EucConfig d (N - 1) × Euc d =>
      ENNReal.ofReal (φ p.2) * ENNReal.ofReal (Real.exp K * fieldH D N i H p.1 p.2 ^ 2)) ?_
    exact (hφm.comp measurable_snd).ennreal_ofReal.mul
      ((measurable_const.mul (hvm.pow_const 2)).ennreal_ofReal)
  refine ⟨hEm, ?_⟩
  have hjen : ∀ Y, (∫⁻ y, Fm y * Gf Y y ∂μ) ^ (2 * q) ≤
      (∫⁻ y, Fm y ∂μ) ^ (2 * q - 1) * ∫⁻ y, Fm y * Gf Y y ^ (2 * q) ∂μ :=
    fun Y => taylor_jensen hFmm (hGfy Y) (2 * q) (by omega)
  set bd : ℝ := Real.exp K ^ (2 * q) * (Cf * Θ ^ (2 * q)) with hbd
  have hbd0 : 0 ≤ bd := by positivity
  have hY : ∀ y : Euc d, ∫⁻ Y, Gf Y y ^ (2 * q) ∂Pm ≤ ENNReal.ofReal bd := by
    intro y
    obtain ⟨B, hB⟩ := s81b_field_bdd hd D hβm N i H hH0.le y
    set vv : EucConfig d (N - 1) → ℝ := fun Y => fieldH D N i H Y y with hvv
    have hvvm : Measurable vv :=
      Measurable.of_uncurry_right (f := fun (Y : EucConfig d (N - 1)) (y : Euc d) =>
        fieldH D N i H Y y) hvm
    have hev : Even (4 * q) := ⟨2 * q, by ring⟩
    have e0 : ∀ Y, (Real.exp K * vv Y ^ 2) ^ (2 * q) = Real.exp K ^ (2 * q) * vv Y ^ (4 * q) := by
      intro Y; ring
    have e1 : ∀ Y, Gf Y y ^ (2 * q) = ENNReal.ofReal (Real.exp K ^ (2 * q) * vv Y ^ (4 * q)) := by
      intro Y
      have : Gf Y y = ENNReal.ofReal (Real.exp K * vv Y ^ 2) := rfl
      rw [this, ← ENNReal.ofReal_pow (by positivity), e0]
    simp_rw [e1]
    have hgint : Integrable (fun Y => Real.exp K ^ (2 * q) * vv Y ^ (4 * q)) Pm :=
      taylor_integrable_of_bdd ((hvvm.pow_const _).const_mul _)
        (B := Real.exp K ^ (2 * q) * B ^ (4 * q)) fun Y => by
          rw [abs_mul, abs_pow, abs_pow, abs_of_pos (Real.exp_pos K)]
          gcongr
          exact hB Y
    rw [← ofReal_integral_eq_lintegral_ofReal hgint (Filter.Eventually.of_forall fun Y => by
      have := hev.pow_nonneg (vv Y); positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hCf D N hN H hH i y) (by positivity)
  have hswap : ∫⁻ Y, ∫⁻ y, Fm y * Gf Y y ^ (2 * q) ∂μ ∂Pm =
      ∫⁻ y, ∫⁻ Y, Fm y * Gf Y y ^ (2 * q) ∂Pm ∂μ := by
    refine lintegral_lintegral_swap ?_
    exact ((hFmm.comp measurable_snd).mul (hGfm.pow_const (2 * q))).aemeasurable
  have hFmfin : (∫⁻ y, Fm y ∂μ) ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmass
  have hmid : ∫⁻ Y, (∫⁻ y, Fm y * Gf Y y ∂μ) ^ (2 * q) ∂Pm ≤
      ENNReal.ofReal Cp ^ (2 * q) * ENNReal.ofReal bd := by
    calc ∫⁻ Y, (∫⁻ y, Fm y * Gf Y y ∂μ) ^ (2 * q) ∂Pm
        ≤ ∫⁻ Y, (∫⁻ y, Fm y ∂μ) ^ (2 * q - 1) * ∫⁻ y, Fm y * Gf Y y ^ (2 * q) ∂μ ∂Pm :=
          lintegral_mono hjen
      _ = (∫⁻ y, Fm y ∂μ) ^ (2 * q - 1) * ∫⁻ Y, ∫⁻ y, Fm y * Gf Y y ^ (2 * q) ∂μ ∂Pm :=
          lintegral_const_mul' _ _ (ENNReal.pow_ne_top hFmfin)
      _ = (∫⁻ y, Fm y ∂μ) ^ (2 * q - 1) * ∫⁻ y, ∫⁻ Y, Fm y * Gf Y y ^ (2 * q) ∂Pm ∂μ := by
          rw [hswap]
      _ ≤ (∫⁻ y, Fm y ∂μ) ^ (2 * q - 1) * ∫⁻ y, Fm y * ENNReal.ofReal bd ∂μ := by
          refine mul_le_mul' le_rfl (lintegral_mono fun y => ?_)
          rw [lintegral_const_mul _ ((hGfY y).pow_const _)]
          exact mul_le_mul' le_rfl (hY y)
      _ = (∫⁻ y, Fm y ∂μ) ^ (2 * q - 1) * ((∫⁻ y, Fm y ∂μ) * ENNReal.ofReal bd) := by
          rw [lintegral_mul_const _ hFmm]
      _ = (∫⁻ y, Fm y ∂μ) ^ (2 * q) * ENNReal.ofReal bd := by
          rw [← mul_assoc, ← pow_succ]
          congr 2; omega
      _ ≤ ENNReal.ofReal Cp ^ (2 * q) * ENNReal.ofReal bd := by gcongr
  refine taylorLp_le_of_lintegral_le hp0 _ ?_
  simp_rw [ENNReal.rpow_natCast]
  refine hmid.trans ?_
  rw [← ENNReal.ofReal_pow hCp0, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hmx : Cf ≤ max Cf 1 ^ (2 * q) := by
    calc Cf ≤ max Cf 1 := le_max_left _ _
      _ = max Cf 1 ^ 1 := (pow_one _).symm
      _ ≤ max Cf 1 ^ (2 * q) := pow_le_pow_right₀ (le_max_right _ _) (by omega)
  calc Cp ^ (2 * q) * bd = Cp ^ (2 * q) * Real.exp K ^ (2 * q) * (Cf * Θ ^ (2 * q)) := by
        rw [hbd]; ring
    _ ≤ Cp ^ (2 * q) * Real.exp K ^ (2 * q) * (max Cf 1 ^ (2 * q) * Θ ^ (2 * q)) := by
        gcongr
    _ = (Cp * Real.exp K * max Cf 1 * Θ) ^ (2 * q) := by
        rw [mul_pow, mul_pow, mul_pow]; ring

end HRS.Whole.S81b
