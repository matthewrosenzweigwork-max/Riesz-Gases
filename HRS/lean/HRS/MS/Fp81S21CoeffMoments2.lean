import HRS.MS.Fp81S21CoeffMoments
import HRS.MS.Fp81S21WeightedMomentsS3
import HRS.MS.Fp81S21Uniform

/-! The sixth-moment port for the raw empirical field in the strong chart. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.R2Interp
open HRS.MS.ProClosureS111

private theorem fp81s21_coeffMoments_strong_weighted_reference_integrable
    {d : ℕ} {ρ : Euc d → ℝ} {C₀ c₀ Pw : ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) (hc₀ : 0 < c₀) (hPw : 0 ≤ Pw)
    (hG : HRS.Whole.HasR2GaussianUpper C₀ c₀ ρ) :
    Integrable (fun x : Euc d => jbracket x ^ Pw)
      (HRS.Whole.withDensityReal ρ) := by
  obtain ⟨C, hC₀, hC⟩ := HRS.MS.R2Poly.s95_moment d C₀ c₀ hc₀
    (Pw := Pw / 2) (by linarith)
  have hpow : ∀ x : Euc d, (jbracket x ^ (Pw / 2)) ^ 2 = jbracket x ^ Pw := by
    intro x
    have hj : 0 < jbracket x := lt_of_lt_of_le zero_lt_one
      (HRS.MS.R2Poly.s95_one_le_jb x)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hj)]
    congr 1
    ring
  have hbound :
      (∫⁻ x, ENNReal.ofReal (jbracket x ^ Pw)
        ∂(HRS.Whole.withDensityReal ρ)) ≤ ENNReal.ofReal C := by
    calc
      _ = ∫⁻ x, ENNReal.ofReal ((jbracket x ^ (Pw / 2)) ^ 2)
          ∂(HRS.Whole.withDensityReal ρ) := by
            refine lintegral_congr fun x => ?_
            rw [hpow]
      _ ≤ ENNReal.ofReal C := hC ρ hρ hG.2
  have hjb : Continuous (fun x : Euc d => jbracket x) := by
    unfold jbracket
    fun_prop
  have hmeas : Measurable (fun x : Euc d => jbracket x ^ Pw) :=
    (hjb.rpow_const fun x => Or.inl
      (zero_lt_one.trans_le (HRS.MS.R2Poly.s95_one_le_jb x)).ne').measurable
  have hnonneg : ∀ x : Euc d, 0 ≤ jbracket x ^ Pw := fun x =>
    Real.rpow_nonneg (Real.sqrt_nonneg _) _
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  calc
    ∫⁻ x, ‖jbracket x ^ Pw‖ₑ ∂(HRS.Whole.withDensityReal ρ) =
        ∫⁻ x, ENNReal.ofReal (jbracket x ^ Pw)
          ∂(HRS.Whole.withDensityReal ρ) := by
            refine lintegral_congr fun x => ?_
            rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hnonneg x)]
    _ ≤ ENNReal.ofReal C := hbound
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- Uniform sixth moments for a time-indexed coefficient representative. -/
def fp81s21_Six {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (q : ℝ → Ω → r26t6_Coeff) (M : ℝ) : Prop :=
  ∀ u, 0 ≤ u → fp81s21_Moment6 P (q u) M

/-- Sixth-moment transfer when the exact chart norm identity holds almost
surely, as in `MomentRep`. -/
theorem fp81s21_rep_sixthMoment_ae
    {d r : ℕ} {Pw : ℝ} {S : Type*} [MeasurableSpace S]
    (P : Measure S) (T : S → (Euc d → ℝ) → ℝ)
    (z : S → r26t6_Coeff)
    (hz : Measurable z)
    (hrep : ∀ᵐ a ∂P, dualNormE r Pw (T a) = ENNReal.ofReal ‖z a‖)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb : ∀ a, dualNormE r Pw (T a) ≤
      ENNReal.ofReal C * r2NegSobNorm r Pw (T a))
    (hL : (∫⁻ a, r2NegSobNorm r Pw (T a) ^ (6 : ℝ) ∂P) ≤ ENNReal.ofReal D) :
    fp81s21_Moment6 P z (C ^ 6 * D) := by
  have hpoint : ∀ᵐ a ∂P,
      ENNReal.ofReal (‖z a‖ ^ 6) ≤
        ENNReal.ofReal (C ^ 6) * r2NegSobNorm r Pw (T a) ^ (6 : ℝ) := by
    filter_upwards [hrep] with a ha
    have hdual : ENNReal.ofReal ‖z a‖ ≤
        ENNReal.ofReal C * r2NegSobNorm r Pw (T a) := by
      rw [← ha]
      exact hb a
    have hpow := ENNReal.rpow_le_rpow hdual (by norm_num : (0 : ℝ) ≤ 6)
    have hleft : (ENNReal.ofReal ‖z a‖) ^ (6 : ℝ) =
        ENNReal.ofReal (‖z a‖ ^ 6) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
      exact congrArg ENNReal.ofReal (Real.rpow_natCast _ 6)
    have hCpow : (ENNReal.ofReal C) ^ (6 : ℝ) = ENNReal.ofReal (C ^ 6) := by
      rw [ENNReal.ofReal_rpow_of_nonneg hC (by norm_num)]
      exact congrArg ENNReal.ofReal (Real.rpow_natCast C 6)
    have hright : (ENNReal.ofReal C * r2NegSobNorm r Pw (T a)) ^ (6 : ℝ) =
        ENNReal.ofReal (C ^ 6) * r2NegSobNorm r Pw (T a) ^ (6 : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg (ENNReal.ofReal C)
        (r2NegSobNorm r Pw (T a)) (by norm_num : (0 : ℝ) ≤ 6), hCpow]
    rw [hleft, hright] at hpow
    exact hpow
  have hnonneg : ∀ a, 0 ≤ ‖z a‖ ^ 6 := fun a => by positivity
  have hmeas : AEStronglyMeasurable (fun a => ‖z a‖ ^ 6) P := by
    exact ((measurable_norm.comp hz).pow_const 6).aestronglyMeasurable
  have hlin :
      (∫⁻ a, ENNReal.ofReal (‖z a‖ ^ 6) ∂P) ≤
        ENNReal.ofReal (C ^ 6 * D) := by
    calc
      _ ≤ ∫⁻ a, ENNReal.ofReal (C ^ 6) *
          r2NegSobNorm r Pw (T a) ^ (6 : ℝ) ∂P := lintegral_mono_ae hpoint
      _ = ENNReal.ofReal (C ^ 6) *
          (∫⁻ a, r2NegSobNorm r Pw (T a) ^ (6 : ℝ) ∂P) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (C ^ 6) * ENNReal.ofReal D :=
        mul_le_mul_right hL _
      _ = ENNReal.ofReal (C ^ 6 * D) := by
        rw [ENNReal.ofReal_mul (by positivity)]
  have hi : Integrable (fun a => ‖z a‖ ^ 6) P := by
    refine ⟨hmeas, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnonneg)]
    exact lt_of_le_of_lt hlin ENNReal.ofReal_lt_top
  have hIntegralENN :
      (∫⁻ a, ENNReal.ofReal (‖z a‖ ^ 6) ∂P) =
        ENNReal.ofReal (∫ a, ‖z a‖ ^ 6 ∂P) :=
    (ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall hnonneg)).symm
  have hreal : ENNReal.ofReal (∫ a, ‖z a‖ ^ 6 ∂P) ≤
      ENNReal.ofReal (C ^ 6 * D) := by
    rw [← hIntegralENN]
    exact hlin
  refine ⟨hz.aemeasurable, hi, ?_⟩
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hreal

/-- Measurability of the negative Sobolev norm of the raw empirical field.
The norm is a supremum of continuous test evaluations, so lower
semicontinuity supplies the measurability needed for pushforward transfer. -/
theorem fp81s21_emp_r2NegSobNorm_measurable
    {d r N : ℕ} {Pw : ℝ} (hN : 0 < N) (μ : Measure (Euc d)) :
    Measurable (fun X : EucConfig d N =>
      r2NegSobNorm r Pw (r2EmpDistr μ X)) := by
  have hjb : Continuous (fun x : Euc d => jbracket x) := by
    unfold jbracket
    fun_prop
  have hw : Continuous (fun x : Euc d => jbracket x ^ Pw) :=
    hjb.rpow_const fun x => Or.inl
      (zero_lt_one.trans_le (HRS.MS.R2Poly.s95_one_le_jb x)).ne'
  have hlsc : LowerSemicontinuous (fun X : EucConfig d N =>
      ⨆ ψ : SchwartzMap (Euc d) ℝ,
        ⨆ h : HRS.Whole.sobolevNormE (r : ℝ) (fun x => ψ x) ≤ 1,
          ENNReal.ofReal |r2EmpDistr μ X (fun x => jbracket x ^ Pw * ψ x)|) := by
    apply lowerSemicontinuous_iSup
    intro ψ
    apply lowerSemicontinuous_iSup
    intro h
    have htest : Continuous (fun x : Euc d => jbracket x ^ Pw * ψ x) :=
      hw.mul ψ.continuous
    have hsum : Continuous (fun X : EucConfig d N =>
        ∑ i, (fun x : Euc d => jbracket x ^ Pw * ψ x) (X i)) :=
      continuous_finset_sum _ fun i _ => htest.comp (continuous_apply i)
    have hformula : (fun X : EucConfig d N =>
        r2EmpDistr μ X (fun x => jbracket x ^ Pw * ψ x)) =
        fun X => Real.sqrt N * ((N : ℝ)⁻¹ *
          ∑ i, (fun x : Euc d => jbracket x ^ Pw * ψ x) (X i) -
          HRS.Whole.pair μ (fun x => jbracket x ^ Pw * ψ x)) := by
      funext X
      simp only [r2EmpDistr]
      rw [HRS.Whole.pair_empirical hN]
    have hcont : Continuous (fun X : EucConfig d N =>
        r2EmpDistr μ X (fun x => jbracket x ^ Pw * ψ x)) := by
      rw [hformula]
      exact continuous_const.mul
        ((continuous_const.mul hsum).sub continuous_const)
    exact (ENNReal.continuous_ofReal.comp
      (continuous_abs.comp hcont)).lowerSemicontinuous
  simpa [HRS.Whole.r2NegSobNorm] using hlsc.measurable

/-- Strong-chart B2 substage: the raw empirical field has a common second
moment representative and sixth coefficient moments, with constants selected
before the particle count and realization. -/
theorem fp81s21_particleEmp_six_momentRep_strong (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4)) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ M2 M6 : ℝ, 0 ≤ M2 ∧ 0 ≤ M6 ∧
          ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N,
            ∃ qs : ℝ → A.Ω → r26t6_Coeff,
              fp81s21_MomentRep Es
                A.P (fp81s21_particleEmpField R N A) qs M2 ∧
              fp81s21_Six A.P qs M6 := by
  obtain ⟨δr, hδr, hδrhalf, hR⟩ := fp81s21_particle_eta_momentRep_strong p
  obtain ⟨δu, hδu, hδuhalf, hU⟩ := fp81s21_uniform_density_moments p
  let δ0 : ℝ := min δr δu
  have hδ0 : 0 < δ0 := lt_min hδr hδu
  have hδ0half : δ0 ≤ 1 / 2 := (min_le_right _ _).trans hδuhalf
  have hPw : 0 ≤ (p.d : ℝ) + 4 := by positivity
  have hChart : (p.d : ℝ) < 2 * ((p.d : ℝ) + 4) := by nlinarith
  obtain ⟨Cw, hCw, hCompare⟩ :=
    fp81s21_dualNormE_le_r2NegSobNorm (d := p.d) (r := 2 * p.d + 6)
      (Pw := (p.d : ℝ) + 4) hChart
  have hOrder : (p.d : ℝ) + 3 + (p.d : ℝ) / 2 <
      ((2 * p.d + 6 : ℕ) : ℝ) := by
    push_cast
    nlinarith [show (2 : ℝ) ≤ p.d by exact_mod_cast p.hd]
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R
  have hδr' : δ ≤ δr := hδle.trans (min_le_left _ _)
  have hδu' : δ ≤ δu := hδle.trans (min_le_right _ _)
  obtain ⟨M2, hM2, hRepR⟩ := hR δ hδ hδr' R
  obtain ⟨pinf, K, C₀, c₀, M, L, Mρ, Cm, hpinf, hc₀,
    hGaussian, hRound, hReferenceMoment, hParticle⟩ := hU δ hδ hδu' R
  obtain ⟨D6, hD6, hNeg6⟩ := fp81s21_emp_r2wfm_singleLaw_tau
    p (r := 2 * p.d + 6) (Pw := (p.d : ℝ) + 4)
    (M := M) (L := L) (C₀ := C₀) (c₀ := c₀) (pinf := pinf) (K := K)
    hPw hOrder hc₀ hpinf 6 (by norm_num)
  let M6 : ℝ := Cw ^ 6 * D6
  have hM6 : 0 ≤ M6 := by dsimp [M6]; positivity
  refine ⟨M2, M6, hM2, hM6, ?_⟩
  intro N hN A
  obtain ⟨qs, hqs⟩ := hRepR N hN A Es
  refine ⟨qs, hqs, ?_⟩
  intro u hu
  let t : NNReal := Real.toNNReal u
  let μ : Measure (Euc p.d) := r26t3_mu R u
  let T : EucConfig p.d N → (Euc p.d → ℝ) → ℝ :=
    fun X => r2EmpDistr μ X
  let Tω : A.Ω → (Euc p.d → ℝ) → ℝ :=
    fun ω => fp81s21_particleEmpField R N A u ω
  have hXmeas : Measurable (A.X t) := (A.strong (1 : ℝ)).adapted t
  have hActual := (hParticle N hN A u hu).1
  change HRS.Whole.HasR2ActualDensity p.s p.β pinf K
    (HRS.Whole.withDensityReal (R.ρ u)) (A.P.map (A.X t)) at hActual
  let Pactual : Measure (EucConfig p.d N) := A.P.map (A.X t)
  have hNeg := hNeg6 (R.ρ u) (hRound u hu) (hGaussian u hu)
    N hN Pactual hActual
  have hNormMeas : Measurable (fun X : EucConfig p.d N =>
      r2NegSobNorm (2 * p.d + 6) ((p.d : ℝ) + 4) (T X)) := by
    simpa [T] using fp81s21_emp_r2NegSobNorm_measurable
      (r := 2 * p.d + 6) (Pw := (p.d : ℝ) + 4) (N := N)
      (lt_of_lt_of_le (by norm_num) hN) μ
  have hPowMeas : Measurable (fun X : EucConfig p.d N =>
      r2NegSobNorm (2 * p.d + 6) ((p.d : ℝ) + 4) (T X) ^ (6 : ℝ)) :=
    (ENNReal.continuous_rpow_const (y := (6 : ℝ))).measurable.comp hNormMeas
  have hMap :
      (∫⁻ X, r2NegSobNorm (2 * p.d + 6) ((p.d : ℝ) + 4)
        (T X) ^ (6 : ℝ) ∂Pactual) =
      ∫⁻ ω, r2NegSobNorm (2 * p.d + 6) ((p.d : ℝ) + 4)
        (T (A.X t ω)) ^ (6 : ℝ) ∂A.P := by
    simpa [Pactual] using lintegral_map hPowMeas hXmeas
  have hLmap :
      (∫⁻ ω, r2NegSobNorm (2 * p.d + 6) ((p.d : ℝ) + 4)
        (T (A.X t ω)) ^ (6 : ℝ) ∂A.P) ≤ ENNReal.ofReal D6 := by
    rw [← hMap]
    simpa [T, μ, HRS.MS.R26T3.r26t3_mu] using hNeg
  have hTmatch : ∀ ω, Tω ω = T (A.X t ω) := by
    intro ω
    change r2EmpDistr (r26t3_mu R u) (A.X u.toNNReal ω) =
      r2EmpDistr (r26t3_mu R u) (A.X t ω)
    rfl
  have hL :
      (∫⁻ ω, r2NegSobNorm (2 * p.d + 6) ((p.d : ℝ) + 4)
        (Tω ω) ^ (6 : ℝ) ∂A.P) ≤ ENNReal.ofReal D6 := by
    calc
      _ = ∫⁻ ω, r2NegSobNorm (2 * p.d + 6) ((p.d : ℝ) + 4)
          (T (A.X t ω)) ^ (6 : ℝ) ∂A.P := by
            apply lintegral_congr
            intro ω
            rw [hTmatch]
      _ ≤ ENNReal.ofReal D6 := hLmap
  have hDualEq : ∀ᵐ ω ∂A.P,
      dualNormE (2 * p.d + 6) ((p.d : ℝ) + 4) (Tω ω) =
        ENNReal.ofReal ‖qs u ω‖ := by
    filter_upwards [(hqs.2 u hu).2.2] with ω hω
    exact hω.2
  have hHom : ∀ ω c f, IsR2Test f → Tω ω (c • f) = c * Tω ω f := by
    intro ω c f hf
    have hd1 : 1 ≤ p.d := le_trans (by decide : 1 ≤ 2) p.hd
    have hr : (p.d : ℝ) / 2 < (2 * p.d + 6 : ℕ) := by
      push_cast
      nlinarith [show (2 : ℝ) ≤ p.d by exact_mod_cast p.hd]
    have hIu := fp81s21_coeffMoments_strong_weighted_reference_integrable
      (hRound u hu).prob hc₀ hPw (hGaussian u hu)
    have hZ := HRS.MS.R2Interp.s102_Z_fluct hd1 hPw
      (2 * p.d + 6) hr (by omega : 0 < N)
      (A.X t ω) μ hIu (Real.sqrt N)
    have hwt : IsR2WeightedTest (2 * p.d + 6) ((p.d : ℝ) + 4) f :=
      (weightedTestSubmodule_iff).1
        (weighted_test_of_compact_smooth hChart hf)
    change r2EmpDistr μ (A.X t ω) (c • f) =
      c * r2EmpDistr μ (A.X t ω) f
    simpa [r2EmpDistr] using hZ.smul c f hwt
  have hb : ∀ ω, dualNormE (2 * p.d + 6) ((p.d : ℝ) + 4)
        (Tω ω) ≤ ENNReal.ofReal Cw * r2NegSobNorm
          (2 * p.d + 6) ((p.d : ℝ) + 4) (Tω ω) :=
    fun ω => hCompare (Tω ω) (hHom ω)
  exact fp81s21_rep_sixthMoment_ae A.P Tω (qs u)
    ((hqs.1.comp (measurable_const.prodMk measurable_id))) hDualEq
    Cw D6 hCw hD6 hb hL

#print axioms HRS.Fp81.S21.fp81s21_rep_sixthMoment_ae
#print axioms HRS.Fp81.S21.fp81s21_emp_r2NegSobNorm_measurable
#print axioms HRS.Fp81.S21.fp81s21_particleEmp_six_momentRep_strong

end HRS.Fp81.S21

end
