import HRS.MS.WhoAux1
import HRS.MS.UlOuCAux1
import HRS.MS.UlOuSAux2

/-!
# S54 part 2: weighted bounds for Gaussian averages (`ouSg`)

Notation: `γ = stdGaussian (Euc d)`; for `E S : Euc d →L Euc d` and a weight `b`, `wavg` is not named: the key estimate `who_key` bounds
`wSq P (x ↦ ∫ Ψ(E x + S w) b(w) dγ(w))` by `‖b‖²_{L²(γ)} · C_E · ∫ 2^P ⟨S w⟩^{2P} dγ · wSq P Ψ` (Cauchy-Schwarz, Tonelli, Peetre, change
of variables).  No density of `ouLaw` is used.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff MatrixOrder Matrix

namespace HRS.MS.Who

open HRS HRS.Whole HRS.MS.Ul

variable {d : ℕ}

theorem who_jb_cont : Continuous (jbracket (d := d)) := by
  unfold jbracket; fun_prop

/-- Cauchy-Schwarz for lintegrals, squared form -/
theorem who_cs_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ a, f a * g a ∂μ) ^ 2 ≤ (∫⁻ a, f a ^ 2 ∂μ) * ∫⁻ a, g a ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ (p := 2) (q := 2) (by simpa using Real.HolderConjugate.two_two) hf hg
  have h2 := pow_le_pow_left' h 2
  rw [mul_pow] at h2
  refine h2.trans (le_of_eq ?_)
  simp only [one_div]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  norm_num


theorem who_pw_cs {Ψ b : Euc d → ℝ} (hΨ : Measurable Ψ) (hb : Measurable b) (E S : Euc d →L[ℝ] Euc d)
    (x : Euc d) :
    ENNReal.ofReal ((∫ w, Ψ (E x + S w) * b w ∂(stdGaussian (Euc d))) ^ 2) ≤
      (∫⁻ w, ENNReal.ofReal (b w ^ 2) ∂(stdGaussian (Euc d))) *
        ∫⁻ w, ENNReal.ofReal (Ψ (E x + S w) ^ 2) ∂(stdGaussian (Euc d)) := by
  set γ := stdGaussian (Euc d) with hγ
  set f : Euc d → ℝ := fun w => Ψ (E x + S w) * b w with hf
  have hfm : Measurable f := (hΨ.comp (measurable_const.add S.continuous.measurable)).mul hb
  have h1 : (∫ w, f w ∂γ) ^ 2 ≤ (∫ w, |f w| ∂γ) ^ 2 := by
    have := norm_integral_le_integral_norm (μ := γ) f
    simp only [Real.norm_eq_abs] at this
    exact sq_le_sq' (by linarith [abs_nonneg (∫ w, f w ∂γ), le_abs_self (∫ w, f w ∂γ), neg_abs_le (∫ w, f w ∂γ)]) 
      (by nlinarith [abs_nonneg (∫ w, f w ∂γ), le_abs_self (∫ w, f w ∂γ), neg_abs_le (∫ w, f w ∂γ)])
  have h2 : ENNReal.ofReal (∫ w, |f w| ∂γ) ≤ ∫⁻ w, ENNReal.ofReal |f w| ∂γ := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun w => abs_nonneg _)
      hfm.abs.aestronglyMeasurable]
    exact ENNReal.ofReal_toReal_le
  calc ENNReal.ofReal ((∫ w, f w ∂γ) ^ 2) ≤ ENNReal.ofReal ((∫ w, |f w| ∂γ) ^ 2) :=
        ENNReal.ofReal_le_ofReal h1
    _ = ENNReal.ofReal (∫ w, |f w| ∂γ) ^ 2 := ENNReal.ofReal_pow (integral_nonneg fun w => abs_nonneg _) 2
    _ ≤ (∫⁻ w, ENNReal.ofReal |f w| ∂γ) ^ 2 := by gcongr
    _ = (∫⁻ w, ENNReal.ofReal |Ψ (E x + S w)| * ENNReal.ofReal |b w| ∂γ) ^ 2 := by
        congr 1
        refine lintegral_congr fun w => ?_
        simp only [hf, abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
    _ ≤ (∫⁻ w, ENNReal.ofReal |b w| ^ 2 ∂γ) * ∫⁻ w, ENNReal.ofReal |Ψ (E x + S w)| ^ 2 ∂γ := by
        rw [mul_comm (∫⁻ w, ENNReal.ofReal |b w| ^ 2 ∂γ)]
        exact who_cs_lintegral (hΨ.comp (measurable_const.add S.continuous.measurable)).abs.ennreal_ofReal.aemeasurable
          hb.abs.ennreal_ofReal.aemeasurable
    _ = _ := by
        congr 1
        · refine lintegral_congr fun w => ?_
          rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
        · refine lintegral_congr fun w => ?_
          rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]


/-- the Gaussian-moment factor of the weighted bound -/
def gMom (P : ℝ) (S : Euc d →L[ℝ] Euc d) : ℝ≥0∞ :=
  ∫⁻ w, ENNReal.ofReal (2 ^ P * jbracket (S w) ^ (2 * P)) ∂(stdGaussian (Euc d))

/-- the factor from the linear change of variables -/
def cLin (P : ℝ) (E : Euc d →L[ℝ] Euc d) : ℝ :=
  (1 + ‖E‖) ^ (2 * P) * |(LinearMap.det (E : Euc d →ₗ[ℝ] Euc d))⁻¹|

/-- weighted translation + linear change for the shifted function -/
theorem who_wSq_affine {P : ℝ} (hP : 0 ≤ P) (E : Euc d →L[ℝ] Euc d)
    (hE : LinearMap.det (E : Euc d →ₗ[ℝ] Euc d) ≠ 0) {Ψ : Euc d → ℝ} (hΨ : Measurable Ψ) (z : Euc d) :
    wSq P (fun x => Ψ (E x + z)) ≤
      ENNReal.ofReal (2 ^ P * jbracket z ^ (2 * P)) * ENNReal.ofReal (cLin P E) * wSq P Ψ := by
  have h1 := who_wSq_comp_linear hP E hE (G := fun y => Ψ (y + z)) (hΨ.comp (measurable_id.add_const z))
  have h2 := who_wSq_shift hP Ψ (-z)
  have e : (fun y => Ψ (y - -z)) = fun y => Ψ (y + z) := by funext y; simp
  rw [e] at h2
  refine h1.trans ?_
  unfold cLin
  calc ENNReal.ofReal ((1 + ‖E‖) ^ (2 * P) * |(LinearMap.det (E : Euc d →ₗ[ℝ] Euc d))⁻¹|) *
        wSq P (fun y => Ψ (y + z))
      ≤ ENNReal.ofReal ((1 + ‖E‖) ^ (2 * P) * |(LinearMap.det (E : Euc d →ₗ[ℝ] Euc d))⁻¹|) *
        (ENNReal.ofReal (2 ^ P * jbracket (-z) ^ (2 * P)) * wSq P Ψ) := by gcongr
    _ = _ := by
        have : jbracket (-z) = jbracket z := by unfold jbracket; rw [norm_neg]
        rw [this]; ring

theorem who_key {P : ℝ} (hP : 0 ≤ P) (E S : Euc d →L[ℝ] Euc d)
    (hE : LinearMap.det (E : Euc d →ₗ[ℝ] Euc d) ≠ 0) {Ψ b : Euc d → ℝ} (hΨ : Measurable Ψ)
    (hb : Measurable b) :
    wSq P (fun x => ∫ w, Ψ (E x + S w) * b w ∂(stdGaussian (Euc d))) ≤
      (∫⁻ w, ENNReal.ofReal (b w ^ 2) ∂(stdGaussian (Euc d))) *
        (gMom P S * ENNReal.ofReal (cLin P E)) * wSq P Ψ := by
  set γ := stdGaussian (Euc d) with hγ
  have hmeas : Measurable (Function.uncurry fun (x w : Euc d) =>
      ENNReal.ofReal (wt P x * Ψ (E x + S w) ^ 2)) := by
    refine ENNReal.measurable_ofReal.comp ?_
    refine ((who_wt_meas P).comp measurable_fst).mul ?_
    exact (hΨ.comp ((E.continuous.measurable.comp measurable_fst).add
      (S.continuous.measurable.comp measurable_snd))).pow_const 2
  unfold wSq
  calc ∫⁻ x, ENNReal.ofReal (wt P x * (∫ w, Ψ (E x + S w) * b w ∂γ) ^ 2)
      ≤ ∫⁻ x, (∫⁻ w, ENNReal.ofReal (b w ^ 2) ∂γ) *
          ∫⁻ w, ENNReal.ofReal (wt P x * Ψ (E x + S w) ^ 2) ∂γ := by
        refine lintegral_mono fun x => ?_
        rw [ENNReal.ofReal_mul (who_wt_pos P x).le]
        refine (mul_le_mul' le_rfl (who_pw_cs hΨ hb E S x)).trans (le_of_eq ?_)
        rw [mul_left_comm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        refine lintegral_congr fun w => ?_
        rw [ENNReal.ofReal_mul (who_wt_pos P x).le]
    _ = (∫⁻ w, ENNReal.ofReal (b w ^ 2) ∂γ) * ∫⁻ w, ∫⁻ x, ENNReal.ofReal (wt P x * Ψ (E x + S w) ^ 2) ∂volume ∂γ := by
        have hm2 : Measurable fun x : Euc d => ∫⁻ w, ENNReal.ofReal (wt P x * Ψ (E x + S w) ^ 2) ∂γ :=
          hmeas.lintegral_prod_right'
        rw [lintegral_const_mul _ hm2]
        congr 1
        exact lintegral_lintegral_swap hmeas.aemeasurable
    _ ≤ (∫⁻ w, ENNReal.ofReal (b w ^ 2) ∂γ) * ∫⁻ w, (ENNReal.ofReal (2 ^ P * jbracket (S w) ^ (2 * P)) *
          ENNReal.ofReal (cLin P E)) * wSq P Ψ ∂γ := by
        refine mul_le_mul' le_rfl (lintegral_mono fun w => ?_)
        exact who_wSq_affine hP E hE hΨ (S w)
    _ = _ := by
        have hm : Measurable fun w : Euc d => ENNReal.ofReal (2 ^ P * jbracket (S w) ^ (2 * P)) *
            ENNReal.ofReal (cLin P E) := by
          refine Measurable.mul_const ?_ _
          refine ENNReal.measurable_ofReal.comp (measurable_const.mul ?_)
          exact (who_jb_cont.comp S.continuous).measurable.pow_const _
        rw [lintegral_mul_const _ hm, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
        unfold gMom
        simp only [hγ]
        unfold wSq
        ring


theorem who_pow_le (a : ℝ) (ha : 0 ≤ a) (n : ℕ) : (1 + a) ^ n ≤ 2 ^ n * (1 + a ^ n) := by
  rcases le_total a 1 with h | h
  · calc (1 + a) ^ n ≤ 2 ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ ≤ 2 ^ n * (1 + a ^ n) := le_mul_of_one_le_right (by positivity) (by
          have := pow_nonneg ha n; linarith)
  · calc (1 + a) ^ n ≤ (2 * a) ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ = 2 ^ n * a ^ n := mul_pow _ _ _
      _ ≤ 2 ^ n * (1 + a ^ n) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem who_gauss_int {P : ℝ} (hP : 0 ≤ P) :
    Integrable (fun w : Euc d => (1 + ‖w‖ ^ 2) ^ P) (stdGaussian (Euc d)) := by
  set n : ℕ := ⌈P⌉₊ + 1 with hn
  have hmem : MemLp id ((2 * n : ℕ) : ℝ≥0∞) (stdGaussian (Euc d)) :=
    IsGaussian.memLp_id _ _ (ENNReal.natCast_ne_top _)
  have hint := hmem.integrable_norm_rpow (by simp [hn]) (ENNReal.natCast_ne_top _)
  simp only [ENNReal.toReal_natCast, id, Real.rpow_natCast] at hint
  have hint2 : Integrable (fun w : Euc d => 2 ^ n * (1 + (‖w‖ ^ 2) ^ n)) (stdGaussian (Euc d)) := by
    refine (integrable_const (1 : ℝ) |>.add ?_).const_mul _
    simpa [← pow_mul] using hint
  refine hint2.mono' ?_ (Filter.Eventually.of_forall fun w => ?_)
  · exact (Measurable.pow_const (by fun_prop) _).aestronglyMeasurable
  · have h0 : 0 ≤ 1 + ‖w‖ ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg h0 _)]
    calc (1 + ‖w‖ ^ 2) ^ P ≤ (1 + ‖w‖ ^ 2) ^ (n : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ‖w‖])
            (by have := Nat.le_ceil P; rw [hn]; push_cast; linarith)
      _ = (1 + ‖w‖ ^ 2) ^ n := Real.rpow_natCast _ _
      _ ≤ _ := who_pow_le _ (sq_nonneg _) n


theorem who_gMom_le {P : ℝ} (hP : 0 ≤ P) (S : Euc d →L[ℝ] Euc d) {a : ℝ} (ha : 0 ≤ a)
    (hS : ∀ w, ‖S w‖ ≤ a * ‖w‖) :
    gMom P S ≤ ENNReal.ofReal (2 ^ P * (1 + a ^ 2) ^ P) *
      ∫⁻ w, ENNReal.ofReal ((1 + ‖w‖ ^ 2) ^ P) ∂(stdGaussian (Euc d)) := by
  unfold gMom
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun w => ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have h1 : jbracket (S w) ^ (2 * P) = (1 + ‖S w‖ ^ 2) ^ P := by
    rw [show 2 * P = (2 : ℕ) * P by push_cast; ring, Real.rpow_mul (who_jb_pos _).le, Real.rpow_natCast,
      who_jb_sq]
  rw [h1]
  have h2 : 1 + ‖S w‖ ^ 2 ≤ (1 + a ^ 2) * (1 + ‖w‖ ^ 2) := by
    have : ‖S w‖ ^ 2 ≤ a ^ 2 * ‖w‖ ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hS w) 2
    nlinarith [sq_nonneg a, sq_nonneg ‖w‖, mul_nonneg (sq_nonneg a) (sq_nonneg ‖w‖)]
  have h3 := Real.rpow_le_rpow (by positivity) h2 hP
  rw [Real.mul_rpow (by positivity) (by positivity)] at h3
  calc 2 ^ P * (1 + ‖S w‖ ^ 2) ^ P ≤ 2 ^ P * ((1 + a ^ 2) ^ P * (1 + ‖w‖ ^ 2) ^ P) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by ring

theorem who_gMom_lt_top {P : ℝ} (hP : 0 ≤ P) (S : Euc d →L[ℝ] Euc d) {a : ℝ} (ha : 0 ≤ a)
    (hS : ∀ w, ‖S w‖ ≤ a * ‖w‖) : gMom P S < ⊤ :=
  lt_of_le_of_lt (who_gMom_le hP S ha hS)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (who_gauss_int hP).lintegral_lt_top)

/-- the square root of the OU covariance as a linear map -/
def sOU (Q : Matrix (Fin d) (Fin d) ℝ) (ν τ : ℝ) : Euc d →L[ℝ] Euc d :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (ouCov Q ν τ))

theorem who_ouSg_eq (Q : Matrix (Fin d) (Fin d) ℝ) (ν τ : ℝ) {H : Euc d → ℝ} (hH : Continuous H)
    (x : Euc d) :
    ouSg Q ν τ H x = ∫ w, H (ouExp Q τ x + sOU Q ν τ w) ∂(stdGaussian (Euc d)) := by
  unfold ouSg
  rw [ouLaw_eq_map]
  have hm : Measurable (fun w : Euc d => (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (ouCov Q ν τ))) w) :=
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (ouCov Q ν τ))).continuous.measurable
  rw [integral_map hm.aemeasurable]
  · rfl
  · exact (hH.comp (continuous_const.add continuous_id)).aestronglyMeasurable


theorem who_iter_const_mul {i : ℕ} {F : Euc d → ℝ} (hF : ContDiff ℝ i F) (a : ℝ) (x : Euc d) :
    iteratedFDeriv ℝ i (fun x => a * F x) x = a • iteratedFDeriv ℝ i F x := by
  have := iteratedFDeriv_const_smul_apply' (a := a) (i := i) (f := F) (x := x) hF.contDiffAt
  simpa [smul_eq_mul] using this

theorem who_iter_aff {j : ℕ} {H : Euc d → ℝ} (hH : ContDiff ℝ j H) (E : Euc d →L[ℝ] Euc d) (a : ℝ)
    (y : Euc d) {i : ℕ} (hi : i ≤ j) (x : Euc d) :
    iteratedFDeriv ℝ i (fun x => a * H (E x + y)) x =
      a • (iteratedFDeriv ℝ i H (E x + y)).compContinuousLinearMap (fun _ => E) := by
  rw [who_iter_const_mul (F := fun x => H (E x + y))
    ((hH.comp ((E.contDiff).add contDiff_const)).of_le (by exact_mod_cast hi)) a x,
    ul3C_iter_comp hH E y hi x]

/-- smoothness of a weighted Gaussian average and the formula for its derivatives -/
theorem who_gav_smooth (E S : Euc d →L[ℝ] Euc d) {j : ℕ} {H : Euc d → ℝ} (hH : ContDiff ℝ j H)
    {B : ℝ} (hB : ∀ i ≤ j, ∀ y, ‖iteratedFDeriv ℝ i H y‖ ≤ B) {a : Euc d → ℝ} (ha : Continuous a)
    (hai : Integrable a (stdGaussian (Euc d))) :
    ContDiff ℝ j (fun x => ∫ w, a w * H (E x + S w) ∂(stdGaussian (Euc d))) ∧
      ∀ i ≤ j, ∀ x, iteratedFDeriv ℝ i (fun x => ∫ w, a w * H (E x + S w) ∂(stdGaussian (Euc d))) x =
        ∫ w, a w • (iteratedFDeriv ℝ i H (E x + S w)).compContinuousLinearMap (fun _ => E)
          ∂(stdGaussian (Euc d)) := by
  set γ := stdGaussian (Euc d) with hγ
  have hG : ∀ w : Euc d, ContDiff ℝ (j : WithTop ℕ∞) (fun x => a w * H (E x + S w)) := fun w =>
    contDiff_const.mul (hH.comp ((E.contDiff).add contDiff_const))
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) 0)
  have hbd : ∀ i ≤ j, ∀ (w x : Euc d), ‖iteratedFDeriv ℝ i (fun x => a w * H (E x + S w)) x‖ ≤
      |a w| * (B * (max 1 ‖E‖) ^ j) := by
    intro i hi w x
    rw [who_iter_aff hH E (a w) (S w) hi x, norm_smul, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have h3 : ∏ _i : Fin i, ‖E‖ ≤ (max 1 ‖E‖) ^ j := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      calc ‖E‖ ^ i ≤ (max 1 ‖E‖) ^ i := pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) i
        _ ≤ _ := pow_le_pow_right₀ (le_max_left _ _) hi
    exact mul_le_mul (hB i hi _) h3 (by positivity) hB0
  have hmeas : ∀ i ≤ j, ∀ x, AEStronglyMeasurable
      (fun w => iteratedFDeriv ℝ i (fun x => a w * H (E x + S w)) x) γ := by
    intro i hi x
    have : (fun w => iteratedFDeriv ℝ i (fun x => a w * H (E x + S w)) x) = fun w =>
        a w • (iteratedFDeriv ℝ i H (E x + S w)).compContinuousLinearMap (fun _ => E) := by
      funext w
      exact who_iter_aff hH E (a w) (S w) hi x
    rw [this]
    refine Continuous.aestronglyMeasurable ?_
    have h1 : Continuous (iteratedFDeriv ℝ i H) := hH.continuous_iteratedFDeriv (by exact_mod_cast hi)
    exact ha.smul ((ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin i => E)).continuous.comp
      (h1.comp (continuous_const.add (S.continuous))))
  obtain ⟨hc, hf⟩ := HRS.MS.Lc.lc4_iteratedFDeriv_integral (μ := γ) (fun w x => a w * H (E x + S w)) j hG
    (Φ := fun w => |a w| * (B * (max 1 ‖E‖) ^ j)) (hai.abs.mul_const _) hbd hmeas
  refine ⟨hc, fun i hi x => ?_⟩
  rw [hf i hi x]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  exact who_iter_aff hH E (a w) (S w) hi x


/-- **weighted bound for a weighted Gaussian average** -/
theorem who_wSq_gav {P : ℝ} (hP : 0 ≤ P) (E S : Euc d →L[ℝ] Euc d)
    (hE : LinearMap.det (E : Euc d →ₗ[ℝ] Euc d) ≠ 0) {j : ℕ} {H : Euc d → ℝ} (hH : ContDiff ℝ j H)
    {B : ℝ} (hB : ∀ i ≤ j, ∀ y, ‖iteratedFDeriv ℝ i H y‖ ≤ B) {a : Euc d → ℝ} (ha : Continuous a)
    (hai : Integrable a (stdGaussian (Euc d))) {i : ℕ} (hi : i ≤ j) :
    wSq P (fun x => ‖iteratedFDeriv ℝ i
        (fun x => ∫ w, a w * H (E x + S w) ∂(stdGaussian (Euc d))) x‖) ≤
      ENNReal.ofReal ((‖E‖ ^ i) ^ 2) *
        ((∫⁻ w, ENNReal.ofReal (a w ^ 2) ∂(stdGaussian (Euc d))) *
          (gMom P S * ENNReal.ofReal (cLin P E)) * wSq P (fun y => ‖iteratedFDeriv ℝ i H y‖)) := by
  set γ := stdGaussian (Euc d) with hγ
  obtain ⟨-, hf⟩ := who_gav_smooth E S hH hB ha hai
  have hΨm : Measurable fun y => ‖iteratedFDeriv ℝ i H y‖ :=
    (hH.continuous_iteratedFDeriv (by exact_mod_cast hi)).norm.measurable
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) 0)
  set A : Euc d → ℝ := fun x => ∫ w, ‖iteratedFDeriv ℝ i H (E x + S w)‖ * |a w| ∂γ with hA
  have hpt : ∀ x, ‖iteratedFDeriv ℝ i
      (fun x => ∫ w, a w * H (E x + S w) ∂γ) x‖ ≤ ‖E‖ ^ i * A x := by
    intro x
    rw [hf i hi x]
    refine (norm_integral_le_integral_norm _).trans ?_
    have hint : Integrable (fun w => ‖iteratedFDeriv ℝ i H (E x + S w)‖ * |a w|) γ := by
      refine (hai.abs.mul_const B).mono' ?_ (Filter.Eventually.of_forall fun w => ?_)
      · exact ((hΨm.comp (measurable_const.add S.continuous.measurable)).mul ha.measurable.abs).aestronglyMeasurable
      · rw [norm_mul, norm_norm, Real.norm_eq_abs, abs_abs, mul_comm]
        exact mul_le_mul_of_nonneg_left (hB i hi _) (abs_nonneg _)
    rw [hA, ← integral_const_mul]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => norm_nonneg _)
      (hint.const_mul _) (Filter.Eventually.of_forall fun w => ?_)
    beta_reduce
    rw [norm_smul, Real.norm_eq_abs]
    have := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ i H (E x + S w)) (fun _ : Fin i => E)
    have h3 : ∏ _l : Fin i, ‖E‖ = ‖E‖ ^ i := by simp
    rw [h3] at this
    calc |a w| * ‖(iteratedFDeriv ℝ i H (E x + S w)).compContinuousLinearMap fun _ => E‖
        ≤ |a w| * (‖iteratedFDeriv ℝ i H (E x + S w)‖ * ‖E‖ ^ i) :=
          mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = _ := by ring
  calc wSq P (fun x => ‖iteratedFDeriv ℝ i
          (fun x => ∫ w, a w * H (E x + S w) ∂γ) x‖)
      ≤ wSq P (fun x => ‖E‖ ^ i * A x) := who_wSq_mono fun x => by
        have h0 := norm_nonneg (iteratedFDeriv ℝ i (fun x => ∫ w, a w * H (E x + S w) ∂γ) x)
        exact pow_le_pow_left₀ h0 (hpt x) 2
    _ = ENNReal.ofReal ((‖E‖ ^ i) ^ 2) * wSq P A := who_wSq_smul P _ _
    _ ≤ _ := by
        refine mul_le_mul' le_rfl ?_
        have := who_key hP E S hE hΨm ha.measurable.abs
        simp only [sq_abs] at this
        exact this


/-- **Stein's identity** for the Gaussian average: `E[G'(z+SW)(Sc)] = E[G(z+SW)⟪c,W⟫]` -/
theorem who_stein {G : Euc d → ℝ} (hG : ContDiff ℝ 1 G) {B M : ℝ} (hB : ∀ y, |G y| ≤ B)
    (hM : ∀ y, ‖fderiv ℝ G y‖ ≤ M) (S : Euc d →L[ℝ] Euc d) (z c : Euc d) :
    ∫ w, fderiv ℝ G (z + S w) (S c) ∂(stdGaussian (Euc d)) =
      ∫ w, G (z + S w) * inner ℝ c w ∂(stdGaussian (Euc d)) := by
  set γ := stdGaussian (Euc d) with hγ
  have hSc : Continuous S := S.continuous
  have hhc : Continuous G := hG.continuous
  have hdc : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
  have hdiff : ∀ y, DifferentiableAt ℝ G y := fun y => (hG.differentiable one_ne_zero) y
  have hF : ContDiff ℝ 1 (fun w => G (z + S w)) := hG.comp (contDiff_const.add S.contDiff)
  have hFd : ∀ w, fderiv ℝ (fun w => G (z + S w)) w = (fderiv ℝ G (z + S w)).comp S := by
    intro w
    have := (hdiff (z + S w)).hasFDerivAt.comp w ((S.hasFDerivAt).const_add z)
    exact this.fderiv
  have hst : ∀ i : Fin d, ∫ w, w i * G (z + S w) ∂γ =
      ∫ w, fderiv ℝ G (z + S w) (S (EuclideanSpace.single i 1)) ∂γ := by
    intro i
    have := ul3_stein_std hF (B := B) (M := M * ‖S‖) (fun w => hB _) (fun w => by
      rw [hFd]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _))) i
    simpa [hFd] using this
  have hcexp : c = ∑ i : Fin d, c i • (EuclideanSpace.single i (1 : ℝ) : Euc d) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have hbnd : ∀ i : Fin d, Integrable (fun w => fderiv ℝ G (z + S w) (S (EuclideanSpace.single i 1))) γ :=
    fun i => Integrable.of_bound
      ((hdc.comp (continuous_const.add hSc)).clm_apply continuous_const).aestronglyMeasurable
      (M * ‖S (EuclideanSpace.single i (1 : ℝ))‖) (Filter.Eventually.of_forall fun w => by
        refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
        exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _))
  have hfun : ∀ w, fderiv ℝ G (z + S w) (S c) =
      ∑ i : Fin d, c i * fderiv ℝ G (z + S w) (S (EuclideanSpace.single i 1)) := by
    intro w
    conv_lhs => rw [hcexp]
    simp only [map_sum, map_smul, smul_eq_mul]
  simp_rw [hfun]
  rw [integral_finsetSum _ (fun i _ => (hbnd i).const_mul (c i))]
  have hsum : ∀ w, G (z + S w) * inner ℝ c w = ∑ i : Fin d, c i * (w i * G (z + S w)) := by
    intro w
    rw [PiLp.inner_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  simp_rw [hsum]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, integral_const_mul, hst i]
  · intro i _
    refine Integrable.const_mul ?_ _
    refine ((IsGaussian.integrable_id (μ := γ)).norm.mul_const B).mono'
      ((((continuous_apply i).comp (PiLp.continuous_ofLp 2 _)).mul
        (hhc.comp (continuous_const.add hSc))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun w => ?_)
    rw [norm_mul]
    refine mul_le_mul ?_ (by simpa [Real.norm_eq_abs] using hB _) (norm_nonneg _) (norm_nonneg _)
    exact PiLp.norm_apply_le w i


/-- uniform control of the OU data on `[0,T]` -/
theorem who_ou_unif (Q : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ} (hν : 0 < ν) (T : ℝ) :
    ∃ K a lam : ℝ, 1 ≤ K ∧ 0 ≤ a ∧ 0 < lam ∧ ∀ η ∈ Set.Icc (0 : ℝ) T,
      ‖ouExp Q η‖ ≤ K ∧ K⁻¹ ≤ |LinearMap.det ((ouExp Q η : Euc d →L[ℝ] Euc d) : Euc d →ₗ[ℝ] Euc d)| ∧
      (∀ w, ‖sOU Q ν η w‖ ≤ a * ‖w‖) ∧
      (0 < η → ∀ j : Fin d, ∃ c : Euc d, sOU Q ν η c = EuclideanSpace.single j 1 ∧
        ‖c‖ ≤ 1 / Real.sqrt (lam * η)) := by
  obtain ⟨K, hK1, hK⟩ := ul3_exp_unif Q T
  obtain ⟨lam, Lam, hlam, hLam, hb⟩ := ouCov_bounds Q hν T
  refine ⟨K, Real.sqrt (Lam * max T 0), lam, hK1, Real.sqrt_nonneg _, hlam, fun η hη => ⟨(hK η hη).1,
    (hK η hη).2.2, fun w => ?_, fun hη0 j => ?_⟩⟩
  · have hpsd := ouCov_posSemidef Q hν.le hη.1
    have h1 : ‖sOU Q ν η w‖ ^ 2 = w ⬝ᵥ ouCov Q ν η *ᵥ w := ul3_S_norm_sq hpsd w
    have h2 := (hb η hη w).2
    have hT : η ≤ max T 0 := hη.2.trans (le_max_left _ _)
    have h3 : ‖sOU Q ν η w‖ ^ 2 ≤ (Real.sqrt (Lam * max T 0) * ‖w‖) ^ 2 := by
      rw [h1, mul_pow, Real.sq_sqrt (by positivity)]
      calc _ ≤ Lam * η * ‖w‖ ^ 2 := h2
        _ ≤ Lam * max T 0 * ‖w‖ ^ 2 := by gcongr
    exact abs_le_of_sq_le_sq' h3 (by positivity) |>.2
  · have hpsd := ouCov_posSemidef Q hν.le hη.1
    obtain ⟨c, hc, hcn⟩ := ul3_S_preimage hpsd (μ2 := lam * η) (by positivity)
      (fun ξ => (hb η hη ξ).1.trans_eq (by ring)) (EuclideanSpace.single j (1 : ℝ))
    refine ⟨c, hc, ?_⟩
    simpa using hcn


/-- the Gaussian constant `∫ (1+‖w‖²)^P dγ` -/
def gC (d : ℕ) (P : ℝ) : ℝ := ∫ w : Euc d, (1 + ‖w‖ ^ 2) ^ P ∂(stdGaussian (Euc d))

theorem who_gC_nonneg (d : ℕ) (P : ℝ) : 0 ≤ gC d P :=
  integral_nonneg fun w => Real.rpow_nonneg (by positivity) _

theorem who_gMom_real {P : ℝ} (hP : 0 ≤ P) (S : Euc d →L[ℝ] Euc d) {a : ℝ} (ha : 0 ≤ a)
    (hS : ∀ w, ‖S w‖ ≤ a * ‖w‖) : gMom P S ≤ ENNReal.ofReal (2 ^ P * (1 + a ^ 2) ^ P * gC d P) := by
  refine (who_gMom_le hP S ha hS).trans (le_of_eq ?_)
  have e : ENNReal.ofReal (gC d P) = ∫⁻ w : Euc d, ENNReal.ofReal ((1 + ‖w‖ ^ 2) ^ P)
      ∂(stdGaussian (Euc d)) := by
    unfold gC
    exact ofReal_integral_eq_lintegral_ofReal (who_gauss_int hP)
      (Filter.Eventually.of_forall fun w => Real.rpow_nonneg (by positivity) _)
  rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ P * (1 + a ^ 2) ^ P), e,
    ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ P)]

theorem who_det_ne {K : ℝ} (hK : 1 ≤ K) {E : Euc d →L[ℝ] Euc d}
    (h : K⁻¹ ≤ |LinearMap.det (E : Euc d →ₗ[ℝ] Euc d)|) : LinearMap.det (E : Euc d →ₗ[ℝ] Euc d) ≠ 0 := by
  intro h0
  rw [h0, abs_zero] at h
  have : 0 < K⁻¹ := inv_pos.2 (by linarith)
  linarith

theorem who_cLin_le {P : ℝ} (hP : 0 ≤ P) {K : ℝ} (hK : 1 ≤ K) {E : Euc d →L[ℝ] Euc d} (hE : ‖E‖ ≤ K)
    (h : K⁻¹ ≤ |LinearMap.det (E : Euc d →ₗ[ℝ] Euc d)|) : cLin P E ≤ (1 + K) ^ (2 * P) * K := by
  unfold cLin
  have h1 : |(LinearMap.det (E : Euc d →ₗ[ℝ] Euc d))⁻¹| ≤ K := by
    rw [abs_inv, inv_le_comm₀ (abs_pos.2 (who_det_ne hK h)) (by linarith)]
    exact h
  have h2 : (1 + ‖E‖) ^ (2 * P) ≤ (1 + K) ^ (2 * P) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
  exact mul_le_mul h2 h1 (abs_nonneg _) (by positivity)

/-- **W1**: the weighted bound for the OU semigroup on `[0,T]` -/
theorem who_W1 {P : ℝ} (hP : 0 ≤ P) (Q : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ} (hν : 0 < ν) (T : ℝ)
    (r : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ η ∈ Set.Icc (0 : ℝ) T, ∀ {j : ℕ}, j ≤ r → ∀ {H : Euc d → ℝ},
      ContDiff ℝ j H → (∃ B : ℝ, ∀ i ≤ j, ∀ y, ‖iteratedFDeriv ℝ i H y‖ ≤ B) →
      wSq P (fun x => ‖iteratedFDeriv ℝ j (ouSg Q ν η H) x‖) ≤
        ENNReal.ofReal C * wSq P (fun y => ‖iteratedFDeriv ℝ j H y‖) := by
  obtain ⟨K, a, lam, hK1, ha0, hlam, hU⟩ := who_ou_unif Q hν T
  have hK0 : 0 ≤ K := by linarith
  refine ⟨K ^ (2 * r) * ((2 ^ P * (1 + a ^ 2) ^ P * gC d P) * ((1 + K) ^ (2 * P) * K)),
    mul_nonneg (pow_nonneg hK0 _) (mul_nonneg (mul_nonneg (by positivity) (who_gC_nonneg d P))
      (mul_nonneg (Real.rpow_nonneg (by linarith) _) hK0)),
    fun η hη j hj H hH ⟨B, hB⟩ => ?_⟩
  obtain ⟨hEK, hdet, hS, -⟩ := hU η hη
  set E := ouExp Q η with hE
  set S := sOU Q ν η with hSd
  have hEd := who_det_ne hK1 hdet
  have hfun : ouSg Q ν η H = fun x => ∫ w, (fun _ : Euc d => (1 : ℝ)) w * H (E x + S w) ∂(stdGaussian (Euc d)) := by
    funext x
    rw [who_ouSg_eq Q ν η (hH.continuous) x]
    simp only [one_mul]
    rfl
  rw [hfun]
  have key := who_wSq_gav hP E S hEd hH hB (a := fun _ => (1 : ℝ)) continuous_const
    (integrable_const _) (le_refl j)
  refine key.trans ?_
  have hI : (∫⁻ w, ENNReal.ofReal (((fun _ : Euc d => (1 : ℝ)) w) ^ 2) ∂(stdGaussian (Euc d))) = 1 := by
    simp
  rw [hI, one_mul]
  have h1 : ENNReal.ofReal ((‖E‖ ^ j) ^ 2) ≤ ENNReal.ofReal (K ^ (2 * r)) := by
    apply ENNReal.ofReal_le_ofReal
    rw [← pow_mul]
    calc ‖E‖ ^ (j * 2) ≤ K ^ (j * 2) := pow_le_pow_left₀ (norm_nonneg _) hEK _
      _ ≤ K ^ (2 * r) := pow_le_pow_right₀ hK1 (by omega)
  have h2 := who_gMom_real hP S ha0 hS
  have h3 := who_cLin_le hP hK1 hEK hdet
  calc ENNReal.ofReal ((‖E‖ ^ j) ^ 2) * (gMom P S * ENNReal.ofReal (cLin P E) *
        wSq P fun y => ‖iteratedFDeriv ℝ j H y‖)
      ≤ ENNReal.ofReal (K ^ (2 * r)) * (ENNReal.ofReal (2 ^ P * (1 + a ^ 2) ^ P * gC d P) *
        ENNReal.ofReal ((1 + K) ^ (2 * P) * K) * wSq P fun y => ‖iteratedFDeriv ℝ j H y‖) := by
        gcongr
    _ = _ := by
        have hm1 : (0 : ℝ) ≤ 2 ^ P * (1 + a ^ 2) ^ P * gC d P := mul_nonneg (by positivity) (who_gC_nonneg d P)
        rw [← ENNReal.ofReal_mul hm1, ← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hK0 _)]


theorem who_m2_int : Integrable (fun w : Euc d => ‖w‖ ^ 2) (stdGaussian (Euc d)) := by
  have h := who_gauss_int (d := d) (P := 1) zero_le_one
  simp only [Real.rpow_one] at h
  have := h.sub (integrable_const (1 : ℝ))
  refine this.congr (Filter.Eventually.of_forall fun w => ?_)
  simp

/-- **W2**: one derivative moved onto the Gaussian costs `η^{-1/2}` (squared: `η⁻¹`) -/
theorem who_W2 {P : ℝ} (hP : 0 ≤ P) (Q : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ} (hν : 0 < ν) (T : ℝ)
    (r : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ η ∈ Set.Ioc (0 : ℝ) T, ∀ k : Fin d, ∀ {i : ℕ}, i ≤ r →
      ∀ {G : Euc d → ℝ}, ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) G →
      (∃ B : ℝ, ∀ l ≤ r + 1, ∀ y, ‖iteratedFDeriv ℝ l G y‖ ≤ B) →
      wSq P (fun x => ‖iteratedFDeriv ℝ i
          (ouSg Q ν η (fun y => fderiv ℝ G y (EuclideanSpace.single k 1))) x‖) ≤
        ENNReal.ofReal (C * η⁻¹) * wSq P (fun y => ‖iteratedFDeriv ℝ i G y‖) := by
  obtain ⟨K, a, lam, hK1, ha0, hlam, hU⟩ := who_ou_unif Q hν T
  set m2 : ℝ := ∫ w : Euc d, ‖w‖ ^ 2 ∂(stdGaussian (Euc d)) with hm2
  have hm20 : 0 ≤ m2 := integral_nonneg fun w => by positivity
  have hK0 : 0 ≤ K := by linarith
  refine ⟨K ^ (2 * r) * (m2 / lam) * ((2 ^ P * (1 + a ^ 2) ^ P * gC d P) * ((1 + K) ^ (2 * P) * K)),
    mul_nonneg (mul_nonneg (pow_nonneg hK0 _) (div_nonneg hm20 hlam.le))
      (mul_nonneg (mul_nonneg (by positivity) (who_gC_nonneg d P))
        (mul_nonneg (Real.rpow_nonneg (by linarith) _) hK0)),
    fun η hη k i hi G hG ⟨B, hB⟩ => ?_⟩
  have hη0 : 0 < η := hη.1
  obtain ⟨hEK, hdet, hS, hpre⟩ := hU η ⟨hη.1.le, hη.2⟩
  obtain ⟨c, hcS, hcn⟩ := hpre hη0 k
  set E := ouExp Q η with hE
  set S := sOU Q ν η with hSd
  have hEd := who_det_ne hK1 hdet
  set γ := stdGaussian (Euc d) with hγ
  have hG1 : ContDiff ℝ 1 G := hG.of_le (by exact_mod_cast Nat.le_add_left 1 r)
  have hB0 : ∀ y, |G y| ≤ B := fun y => by
    have := hB 0 (Nat.zero_le _) y
    simpa using this
  have hB1 : ∀ y, ‖fderiv ℝ G y‖ ≤ B := fun y => by
    have := hB 1 (by omega) y
    simpa using this
  have hcont : Continuous fun y => fderiv ℝ G y (EuclideanSpace.single k (1 : ℝ)) :=
    (hG1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hfun : ouSg Q ν η (fun y => fderiv ℝ G y (EuclideanSpace.single k 1)) =
      fun x => ∫ w, (fun w : Euc d => inner ℝ c w) w * G (E x + S w) ∂γ := by
    funext x
    rw [who_ouSg_eq Q ν η hcont x]
    have := who_stein hG1 hB0 hB1 S (E x) c
    rw [hcS] at this
    simp only [mul_comm (G _)] at this
    exact this
  rw [hfun]
  have hac : Continuous fun w : Euc d => inner ℝ c w := continuous_const.inner continuous_id
  have hai : Integrable (fun w : Euc d => inner ℝ c w) γ := by
    refine ((IsGaussian.integrable_id (μ := γ)).norm.const_mul ‖c‖).mono' hac.aestronglyMeasurable
      (Filter.Eventually.of_forall fun w => ?_)
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm c w)
  have key := who_wSq_gav hP E S hEd hG (fun l hl y => hB l hl y) hac hai (j := r + 1) (i := i) (by omega)
  refine key.trans ?_
  have hI : (∫⁻ w, ENNReal.ofReal ((inner ℝ c w) ^ 2) ∂γ) ≤
      ENNReal.ofReal (1 / (lam * η) * m2) := by
    calc (∫⁻ w, ENNReal.ofReal ((inner ℝ c w) ^ 2) ∂γ)
        ≤ ∫⁻ w, ENNReal.ofReal (‖c‖ ^ 2) * ENNReal.ofReal (‖w‖ ^ 2) ∂γ := by
          refine lintegral_mono fun w => ?_
          rw [← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          have := abs_real_inner_le_norm c w
          rw [← sq_abs, ← mul_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = ENNReal.ofReal (‖c‖ ^ 2) * ENNReal.ofReal m2 := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1
          rw [hm2]
          exact (ofReal_integral_eq_lintegral_ofReal who_m2_int
            (Filter.Eventually.of_forall fun w => by positivity)).symm
      _ ≤ _ := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          refine mul_le_mul_of_nonneg_right ?_ hm20
          have h1 : ‖c‖ ^ 2 ≤ (1 / Real.sqrt (lam * η)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hcn 2
          rw [div_pow, Real.sq_sqrt (by positivity)] at h1
          simpa using h1
  have h1 : ENNReal.ofReal ((‖E‖ ^ i) ^ 2) ≤ ENNReal.ofReal (K ^ (2 * r)) := by
    apply ENNReal.ofReal_le_ofReal
    rw [← pow_mul]
    calc ‖E‖ ^ (i * 2) ≤ K ^ (i * 2) := pow_le_pow_left₀ (norm_nonneg _) hEK _
      _ ≤ K ^ (2 * r) := pow_le_pow_right₀ hK1 (by omega)
  have h2 := who_gMom_real hP S ha0 hS
  have h3 := who_cLin_le hP hK1 hEK hdet
  have hm1 : (0 : ℝ) ≤ 2 ^ P * (1 + a ^ 2) ^ P * gC d P := mul_nonneg (by positivity) (who_gC_nonneg d P)
  calc ENNReal.ofReal ((‖E‖ ^ i) ^ 2) * ((∫⁻ w, ENNReal.ofReal ((inner ℝ c w) ^ 2) ∂γ) *
        (gMom P S * ENNReal.ofReal (cLin P E)) * wSq P fun y => ‖iteratedFDeriv ℝ i G y‖)
      ≤ ENNReal.ofReal (K ^ (2 * r)) * (ENNReal.ofReal (1 / (lam * η) * m2) *
        (ENNReal.ofReal (2 ^ P * (1 + a ^ 2) ^ P * gC d P) * ENNReal.ofReal ((1 + K) ^ (2 * P) * K)) *
        wSq P fun y => ‖iteratedFDeriv ℝ i G y‖) := by
        gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_mul hm1, ← ENNReal.ofReal_mul (by positivity),
          ← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hK0 _)]
        congr 2
        field_simp

end HRS.MS.Who
