import HRS.MS.Fp81S21GaussG4U12
import HRS.MS.WhoAux12
import HRS.MS.R2WinOrbAux9
import HRS.MS.ProClosureS111OscillatorCb

/-! Weighted costs of directional derivatives. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.Who HRS.MS.Ul

/-- A directional derivative costs one weighted derivative of the input. -/
theorem fp81s21_g4_directional_cost {d : ℕ} (P : ℝ) (v : Euc d)
    {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f) :
    Nsq 0 P (fun x => fderiv ℝ f x v) ≤
      ENNReal.ofReal (‖v‖ ^ 2) * Nsq 1 P f := by
  have hpoint : ∀ x, ‖fderiv ℝ f x v‖ ≤ ‖v‖ * ‖iteratedFDeriv ℝ 1 f x‖ := by
    intro x
    simpa using who_dir_norm (l := 0) hf v x
  calc
    Nsq 0 P (fun x => fderiv ℝ f x v) =
        wSq P (fun x => ‖fderiv ℝ f x v‖) := by
          simp [Nsq, iteratedFDeriv_zero_apply]
    _ ≤ wSq P (fun x => ‖v‖ * ‖iteratedFDeriv ℝ 1 f x‖) := by
      apply who_wSq_mono
      intro x
      exact pow_le_pow_left₀ (norm_nonneg _) (hpoint x) 2
    _ = ENNReal.ofReal (‖v‖ ^ 2) *
        wSq P (fun x => ‖iteratedFDeriv ℝ 1 f x‖) := who_wSq_smul P _ _
    _ ≤ ENNReal.ofReal (‖v‖ ^ 2) * Nsq 1 P f :=
      mul_le_mul' le_rfl (who_wSq_le_Nsq (by omega) P f)

/-- Each actual matrix-gradient convolution is controlled by one weighted
spatial derivative. The constant is uniform in the physical time. -/
theorem fp81s21_g4_coordinate_cost (p : Parameters) {δ : ℝ}
    (R : Trajectory p δ) (k : Fin p.d) {P : ℝ}
    (hP : 0 ≤ P) (hPd : (p.d : ℝ) / 2 < P)
    (n : ℕ) (hnP : (p.d : ℝ) / 2 < (n : ℝ) - P)
    (hnd : (p.d : ℝ) < n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℝ, 0 ≤ q →
      ∀ f : Euc p.d → ℝ, CbCls 2 f →
        wSq P (fun x => ‖(convGradConvW (rieszKernelGrad p.d p.s)
          (fun y => R.ρ q y * (HRS.Torus.matVec (r26t3_coeff R).M.transpose
            (gradient f y)) k) x) k‖) ≤
          ENNReal.ofReal C * Nsq 1 P f := by
  obtain ⟨C, hC, hc⟩ := fp81s21_g4_density_convolution_cost p R k hP hPd n hnP hnd
  let v := ul1w (r26t3_coeff R).M k
  refine ⟨C * ‖v‖ ^ 2, by positivity, ?_⟩
  intro q hq f hf
  have hdir : CbCls 1 (fun y => fderiv ℝ f y v) := who_dir_cb hf v
  have heq : (fun y => R.ρ q y * (HRS.Torus.matVec (r26t3_coeff R).M.transpose
      (gradient f y)) k) = (fun y => R.ρ q y * fderiv ℝ f y v) := by
    funext y
    rw [ul1_matVec]
  rw [heq]
  calc
    _ ≤ ENNReal.ofReal C * Nsq 0 P (fun y => fderiv ℝ f y v) := hc q hq _ hdir
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal (‖v‖ ^ 2) * Nsq 1 P f) :=
      mul_le_mul' le_rfl (fp81s21_g4_directional_cost P v (hf.1.of_le (by norm_num)))
    _ = ENNReal.ofReal (C * ‖v‖ ^ 2) * Nsq 1 P f := by
      rw [ENNReal.ofReal_mul hC]
      ring

/-- The convolution coordinates are continuous for bounded smooth jets. -/
theorem fp81s21_g4_coordinate_continuous (p : Parameters) {δ : ℝ}
    (R : Trajectory p δ) (q : ℝ) (hq : 0 ≤ q) (f : Euc p.d → ℝ)
    (hf : CbCls 2 f) (k : Fin p.d) :
    Continuous (fun x => (convGradConvW (rieszKernelGrad p.d p.s)
      (fun y => R.ρ q y * (HRS.Torus.matVec (r26t3_coeff R).M.transpose
        (gradient f y)) k) x) k) := by
  have hd : 1 ≤ p.d := le_trans (by decide) p.hd
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  let v := ul1w (r26t3_coeff R).M k
  obtain ⟨A, hA, hρ⟩ := fp81s21_g4_density_decay p R (p.d + 1)
  obtain ⟨hφ, B, hB⟩ := who_dir_cb hf v
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by omega) 0)
  have hdec : U2Dec 1 ((p.d + 1 : ℕ) : ℝ) (A * B * 2 ^ 1)
      (fun y => R.ρ q y * fderiv ℝ f y v) := who_u2dec_mul (hρ q hq) hφ hB
  have hL : (p.d : ℝ) < ((p.d + 1 : ℕ) : ℝ) := by push_cast; linarith
  have heq : (fun x => (convGradConvW (rieszKernelGrad p.d p.s)
      (fun y => R.ρ q y * (HRS.Torus.matVec (r26t3_coeff R).M.transpose
        (gradient f y)) k) x) k) =
      ultK (u2_kap p.d p.s k) (fun y => R.ρ q y * fderiv ℝ f y v) := by
    funext x
    have : (fun y => R.ρ q y * (HRS.Torus.matVec (r26t3_coeff R).M.transpose
        (gradient f y)) k) = (fun y => R.ρ q y * fderiv ℝ f y v) := by
      funext y
      rw [ul1_matVec]
    rw [this]
    exact (ult_conv_comp hd p.hs0 hsd hL (by positivity) hdec x).2 k
  rw [heq]
  exact (ult_K_iter hd (ult_ker_kap p.hs0 hsd k) hL (by positivity) hdec).2.continuous

/-- The full nonlocal sum has a time-uniform weighted L² bound. -/
theorem fp81s21_g4_nonlocal_weighted (p : Parameters) {δ : ℝ}
    (R : Trajectory p δ) {P : ℝ} (hP : 0 ≤ P)
    (hPd : (p.d : ℝ) / 2 < P) (n : ℕ)
    (hnP : (p.d : ℝ) / 2 < (n : ℝ) - P) (hnd : (p.d : ℝ) < n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℝ, 0 ≤ q → ∀ f : Euc p.d → ℝ,
      CbCls 2 f → wSq P (fun x => ‖fp81s21_g4N p R q f x‖) ≤
        ENNReal.ofReal C * Nsq 1 P f := by
  choose C hC hc using fun k : Fin p.d =>
    fp81s21_g4_coordinate_cost p R k hP hPd n hnP hnd
  refine ⟨(p.d : ℝ) * ∑ k, C k, mul_nonneg (Nat.cast_nonneg _)
    (Finset.sum_nonneg fun k _ => hC k), ?_⟩
  intro q hq f hf
  let G : Fin p.d → Euc p.d → ℝ := fun k x =>
    ‖(convGradConvW (rieszKernelGrad p.d p.s)
      (fun y => R.ρ q y * (HRS.Torus.matVec (r26t3_coeff R).M.transpose
        (gradient f y)) k) x) k‖
  have hm : ∀ k, Measurable (G k) := fun k =>
    (fp81s21_g4_coordinate_continuous p R q hq f hf k).norm.measurable
  calc
    wSq P (fun x => ‖fp81s21_g4N p R q f x‖) ≤ wSq P (fun x => ∑ k, G k x) := by
      apply who_wSq_mono
      intro x
      apply pow_le_pow_left₀ (norm_nonneg _)
      exact norm_sum_le _ _
    _ ≤ (p.d : ℝ≥0∞) * ∑ k, wSq P (G k) := by
      simpa using who_wSq_sum_le (Finset.univ : Finset (Fin p.d)) hm
    _ ≤ (p.d : ℝ≥0∞) * ∑ k, (ENNReal.ofReal (C k) * Nsq 1 P f) := by
      gcongr
      exact hc _ q hq f hf
    _ = ENNReal.ofReal ((p.d : ℝ) * ∑ k, C k) * Nsq 1 P f := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
        ENNReal.ofReal_sum_of_nonneg (fun k _ => hC k), ← Finset.sum_mul]
      ring

/-- The thermal reference density is dominated by every nonnegative
polynomial Sobolev weight. -/
theorem fp81s21_g4_reference_weight (p : Parameters) {δ : ℝ}
    (R : Trajectory p δ) {P : ℝ} (hP : 0 ≤ P) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Euc p.d, R.ρβ x ≤ C * wt P x := by
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  obtain ⟨hprob, ψ, hψ⟩ := HRS.MS.R2WinOrb.s103_rho_schwartz
    p.hd p.hs0 hsd p.ha p.hβ R.thermal
  obtain ⟨A, hA, hdec⟩ := who_schwartz_u2dec ψ 0 (2 * P)
  refine ⟨A, hA, fun x => ?_⟩
  have hx : R.ρβ x ≤ A * u2Wt (2 * P) x := by
    have h := hdec.2 0 (by omega) x
    have h' : |ψ x| ≤ A * u2Wt (2 * P) x := by
      simpa [iteratedFDeriv_zero_apply, Real.norm_eq_abs] using h
    rw [hψ] at h'
    exact (le_abs_self _).trans h'
  have hw : u2Wt (2 * P) x ≤ wt P x := by
    unfold u2Wt wt
    have hj : jbracket x ≤ 1 + ‖x‖ := by
      have hs := who_jb_sq x
      have hp := who_one_le_jb x
      nlinarith [norm_nonneg x, sq_nonneg (‖x‖)]
    have h := Real.rpow_le_rpow_of_nonpos
      (lt_of_lt_of_le zero_lt_one (who_one_le_jb x)) hj (show -(2 * P) ≤ 0 by linarith)
    convert h using 1 <;> congr 1 <;> ring
  exact hx.trans (mul_le_mul_of_nonneg_left hw hA)

/-- Convert the operator-norm weighted derivative cost to the square of the
frozen tuple Sobolev norm. -/
theorem fp81s21_g4_Nsq_cost {d : ℕ} (hd : 1 ≤ d) {P : ℝ}
    (hP : (d : ℝ) / 2 < P) {f : Euc d → ℝ} (hf : CbCls 2 f) :
    Nsq 1 P f ≤ ENNReal.ofReal ((d : ℝ) ^ 2 *
      (weightedSobolevE 2 P f).toReal ^ 2) := by
  obtain ⟨hfc, B, hB⟩ := hf
  have hN : Nsq 2 P f < ⊤ := who_Nsq_lt_top hP (fun j hj => ⟨B, hB j hj⟩)
  have hE : Esq 2 P f < ⊤ := lt_of_le_of_lt (who_Esq_le hd)
    (ENNReal.mul_lt_top (ENNReal.pow_lt_top (ENNReal.natCast_lt_top d)) hN)
  have hW : weightedSobolevE 2 P f < ⊤ := by
    rw [who_E_eq]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hE.ne
  have heq : Esq 2 P f = ENNReal.ofReal ((weightedSobolevE 2 P f).toReal ^ 2) := by
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hW.ne, who_E_eq,
      ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  calc
    Nsq 1 P f ≤ Nsq 2 P f := who_Nsq_mono (by omega) P f
    _ ≤ (d : ℝ≥0∞) ^ 2 * Esq 2 P f := who_Nsq_le hd hfc
    _ = ENNReal.ofReal ((d : ℝ) ^ 2 * (weightedSobolevE 2 P f).toReal ^ 2) := by
      rw [heq, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (Nat.cast_nonneg _),
        ENNReal.ofReal_natCast]

/-- A weighted square bound gives both integrability and a real integral
bound under the thermal reference measure. -/
theorem fp81s21_g4_weight_to_reference (p : Parameters) {δ : ℝ}
    (R : Trajectory p δ) {P : ℝ} (hP : 0 ≤ P) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : Euc p.d → ℝ), Continuous g →
      ∀ B : ℝ, 0 ≤ B → wSq P (fun x => ‖g x‖) ≤ ENNReal.ofReal B →
        MemLp g 2 (HRS.Whole.withDensityReal R.ρβ) ∧
        (∫ x, (g x)^2 ∂HRS.Whole.withDensityReal R.ρβ) ≤ C * B := by
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  obtain ⟨hprob, -⟩ := HRS.MS.R2WinOrb.s103_rho_schwartz
    p.hd p.hs0 hsd p.ha p.hβ R.thermal
  obtain ⟨C, hC, hρ⟩ := fp81s21_g4_reference_weight p R hP
  refine ⟨C, hC, ?_⟩
  intro g hg B hB hw
  have hlin : (∫⁻ x, ENNReal.ofReal ((g x)^2) ∂HRS.Whole.withDensityReal R.ρβ) ≤
      ENNReal.ofReal C * wSq P (fun x => ‖g x‖) := by
    unfold HRS.Whole.withDensityReal
    rw [lintegral_withDensity_eq_lintegral_mul (f := fun x => ENNReal.ofReal (R.ρβ x))
      (g := fun x => ENNReal.ofReal ((g x)^2)) volume
      hprob.measurable.ennreal_ofReal (hg.measurable.pow_const 2).ennreal_ofReal]
    unfold wSq
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono
    intro x
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (hprob.nonneg x), ← ENNReal.ofReal_mul hC]
    apply ENNReal.ofReal_le_ofReal
    have ht := mul_le_mul_of_nonneg_right (hρ x) (sq_nonneg (g x))
    simpa [wSq, Real.norm_eq_abs, sq_abs, mul_assoc] using ht
  have htop : (∫⁻ x, ENNReal.ofReal ((g x)^2) ∂HRS.Whole.withDensityReal R.ρβ) < ⊤ :=
    lt_of_le_of_lt (hlin.trans (mul_le_mul' le_rfl hw))
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  have hi : Integrable (fun x => (g x)^2) (HRS.Whole.withDensityReal R.ρβ) := by
    refine ⟨(hg.pow 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => sq_nonneg _)]
    exact htop
  refine ⟨(memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2 hi, ?_⟩
  have hb : ENNReal.ofReal (∫ x, (g x)^2 ∂HRS.Whole.withDensityReal R.ρβ) ≤
      ENNReal.ofReal (C * B) := by
    rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun x => sq_nonneg _),
      ENNReal.ofReal_mul hC]
    exact hlin.trans (mul_le_mul' le_rfl hw)
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC hB)).1 hb

/-- Original oscillator tests have the bounded two-jet needed for the
classical convolution formulas. -/
theorem fp81s21_g4_osc_cb2 (d : ℕ) {f : Euc d → ℝ}
    (hf : IsOscTest (wholeSpaceIndex d : ℝ) f) : CbCls 2 f := by
  have hn : (2 : ℝ) + (d : ℝ) / 2 < ((d + 3 : ℕ) : ℝ) := by
    push_cast
    linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hm : (d : ℝ) < ((wholeSpaceIndex d : ℝ) - (d + 3 : ℕ)) / 2 := by
    unfold wholeSpaceIndex
    push_cast
    linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  obtain ⟨B, -, hB⟩ := HRS.MS.ProClosureS111.oscillator_derivative_norm_bound 2 (d + 3) hn hm
  exact ⟨hf.1.of_le (by simp), B * oscNorm (wholeSpaceIndex d : ℝ) f,
    fun j hj x => hB f hf j hj x⟩

/-- Uniform nonlocal generator bound under the physical radius prefix. -/
theorem fp81s21_g4_nonlocal (p : Parameters) :
    fp81s21_g4Phys p (fun _ R =>
      ∃ A : ℝ, 0 ≤ A ∧
        ∀ q, 0 ≤ q → ∀ f, IsOscTest (wholeSpaceIndex p.d : ℝ) f →
          MemLp (fp81s21_g4N p R q f) 2 (HRS.Whole.withDensityReal R.ρβ) ∧
          (∫ x, (fp81s21_g4N p R q f x)^2 ∂HRS.Whole.withDensityReal R.ρβ) ≤
            A * fp81s21_g4J p.d f) := by
  refine ⟨1 / 2, by norm_num, le_rfl, ?_⟩
  intro δ hδ hδhalf R
  let P : ℝ := 2 * (p.d : ℝ) + 4
  let n : ℕ := 3 * p.d + 5
  have hd0 : (0 : ℝ) ≤ p.d := Nat.cast_nonneg p.d
  have hP : 0 ≤ P := by dsimp [P]; linarith
  have hPd : (p.d : ℝ) / 2 < P := by dsimp [P]; linarith
  have hnP : (p.d : ℝ) / 2 < (n : ℝ) - P := by dsimp [n, P]; push_cast; linarith
  have hnd : (p.d : ℝ) < n := by dsimp [n]; push_cast; linarith
  obtain ⟨C, hC, hc⟩ := fp81s21_g4_nonlocal_weighted p R hP hPd n hnP hnd
  obtain ⟨D, hD, hd⟩ := fp81s21_g4_weight_to_reference p R hP
  refine ⟨D * (C * (p.d : ℝ)^2), by positivity, ?_⟩
  intro q hq f hf
  have hcb := fp81s21_g4_osc_cb2 p.d hf
  have hcont : Continuous (fp81s21_g4N p R q f) := by
    unfold fp81s21_g4N
    exact continuous_finset_sum _ (fun k _ => fp81s21_g4_coordinate_continuous p R q hq f hcb k)
  have hJ : 0 ≤ fp81s21_g4J p.d f := fp81s21_g4J_nonneg _ _
  have hcost : wSq P (fun x => ‖fp81s21_g4N p R q f x‖) ≤
      ENNReal.ofReal (C * (p.d : ℝ)^2 * fp81s21_g4J p.d f) := by
    calc
      _ ≤ ENNReal.ofReal C * Nsq 1 P f := hc q hq f hcb
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal ((p.d : ℝ)^2 * fp81s21_g4J p.d f) := by
        apply mul_le_mul' le_rfl
        simpa [fp81s21_g4J, P] using
          fp81s21_g4_Nsq_cost (le_trans (by decide) p.hd) hPd hcb
      _ = _ := by rw [← ENNReal.ofReal_mul hC]; congr 1; ring
  have hB : 0 ≤ C * (p.d : ℝ)^2 * fp81s21_g4J p.d f := by positivity
  obtain ⟨hm, hi⟩ := hd _ hcont _ hB hcost
  refine ⟨hm, ?_⟩
  calc
    _ ≤ D * (C * (p.d : ℝ)^2 * fp81s21_g4J p.d f) := hi
    _ = _ := by ring

#print axioms HRS.Fp81.S21.fp81s21_g4_nonlocal
#print axioms HRS.Fp81.S21.fp81s21_g4_osc_cb2
#print axioms HRS.Fp81.S21.fp81s21_g4_weight_to_reference
#print axioms HRS.Fp81.S21.fp81s21_g4_Nsq_cost
#print axioms HRS.Fp81.S21.fp81s21_g4_reference_weight
#print axioms HRS.Fp81.S21.fp81s21_g4_nonlocal_weighted
#print axioms HRS.Fp81.S21.fp81s21_g4_coordinate_continuous
#print axioms HRS.Fp81.S21.fp81s21_g4_coordinate_cost
#print axioms HRS.Fp81.S21.fp81s21_g4_directional_cost
end HRS.Fp81.S21
