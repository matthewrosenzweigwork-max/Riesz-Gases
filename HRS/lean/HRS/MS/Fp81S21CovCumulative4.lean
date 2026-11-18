import HRS.MS.Fp81S21CovCumulative3
import HRS.MS.R2S11Aux10

/-!
# HRS S2.1(iii), packet 19c-i: integrable variation majorant

The moving reference moment and particle moment give a jointly measurable
majorant for the raw eta dual norm.  Its time integral is integrable under the
particle law, and bounds the pre-`toReal` variation integral almost surely.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp

/-- The integrated dual norm of moving raw eta is bounded by an integrable
random majorant.  The covariance constructor's variation estimate can therefore
be passed through `toReal` with an integrable bound. -/
theorem fp81s21_moving_raw_eta_integrable_variation_majorant
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N)
    (hphysical : Fp81MovingPhysicalInputs R hN A H) :
    ∃ Vf : A.Ω → ℝ, Integrable Vf A.P ∧
      ∀ᵐ ω ∂A.P,
        (∫⁻ v in Icc (0 : ℝ) H,
          dualNormE (2 * p.d + 8) ((p.d : ℝ) + 2)
            (fp81s21_movingRawEtaField p R A ω v)).toReal ≤ Vf ω := by
  classical
  let Pw : ℝ := (p.d : ℝ) + 2
  let r : ℕ := 2 * p.d + 8
  have hd1 : 1 ≤ p.d := le_trans (by norm_num) p.hd
  have hPw0 : 0 ≤ Pw := by dsimp [Pw]; positivity
  have hPd : (p.d : ℝ) / 2 < Pw := by dsimp [Pw]; linarith
  have hr : (p.d : ℝ) / 2 < r := by
    dsimp [r]
    push_cast
    have hd : 2 ≤ (p.d : ℝ) := by exact_mod_cast p.hd
    nlinarith
  have hN0 : 0 < N := by omega
  obtain ⟨Mρ, hρmom⟩ :=
    fp81s21_moving_eta_referenceMoment p R hN A hphysical
  obtain ⟨Cm, hpartmom⟩ :=
    fp81s21_moving_eta_particleMoment p R hN A hphysical
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) H := ⟨le_rfl, hH.le⟩
  have hMρ0 : 0 ≤ Mρ := by
    have hjb : ∀ x : Euc p.d, 0 ≤ jbracket x := by
      intro x
      unfold jbracket
      positivity
    have hnonneg : 0 ≤
        ∫ x : Euc p.d, jbracket x ^ Pw ∂(r26t3_mu R 0) :=
      integral_nonneg (fun x => Real.rpow_nonneg (hjb x) Pw)
    exact le_trans hnonneg (hρmom 0 h0).2
  have hCm0 : 0 ≤ Cm := by
    obtain ⟨-, hbound⟩ := hpartmom 0 h0
    have hnonneg : 0 ≤ ∫ ω, (N : ℝ)⁻¹ *
        ∑ k : Fin N, jbracket (A.X 0 ω k) ^ Pw ∂A.P :=
      integral_nonneg fun ω => mul_nonneg (by positivity)
        (Finset.sum_nonneg fun k _ => Real.rpow_nonneg (by
          unfold jbracket
          positivity) Pw)
    exact le_trans hnonneg (by simpa [Pw] using hbound)
  obtain ⟨C0, hC0, hηbound⟩ :=
    s102_eta_bound_unif hd1 hPw0 r hr hN0
  let α : ℝ := Real.sqrt N * C0
  have hα0 : 0 ≤ α := by dsimp [α]; positivity
  have hstrong := A.strong H
  have hXm : ∀ t : ℝ≥0, Measurable (A.X t) := hstrong.adapted
  have hXcont : ∀ᵐ ω ∂A.P, ∀ k : Fin N,
      Continuous fun t : ℝ≥0 => A.X t ω k := hstrong.cont
  obtain ⟨Xjoint, hXjoint, hXae⟩ :=
    HRS.MS.R2S11.s11_X_joint hXm hXcont
  let Q : ℝ × A.Ω → ℝ := fun q => (N : ℝ)⁻¹ *
    ∑ k : Fin N, jbracket (Xjoint q k) ^ Pw
  let W : ℝ × A.Ω → ℝ := fun q => α * (Q q + Mρ)
  have hjcont : Continuous fun x : Euc p.d => jbracket x ^ Pw := by
    have hb : Continuous fun x : Euc p.d => jbracket x := by
      unfold jbracket
      fun_prop
    exact hb.rpow_const (fun x => Or.inl
      (zero_lt_one.trans_le (HRS.MS.R2Poly.s95_one_le_jb x)).ne')
  have hj : Measurable fun x : Euc p.d => jbracket x ^ Pw := hjcont.measurable
  have hQm : Measurable Q := by
    dsimp [Q]
    exact measurable_const.mul (Finset.measurable_sum _ fun k _ =>
      hj.comp ((measurable_pi_apply k).comp hXjoint))
  have hWm : Measurable W := by
    dsimp [W]
    exact measurable_const.mul (hQm.add measurable_const)
  have hQ0 : ∀ q : ℝ × A.Ω, 0 ≤ Q q := by
    intro q
    dsimp [Q]
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun k _ => Real.rpow_nonneg (by
        unfold jbracket
        positivity) Pw)
  have hW0 : ∀ q : ℝ × A.Ω, 0 ≤ W q := by
    intro q
    dsimp [W]
    exact mul_nonneg hα0 (add_nonneg (hQ0 q) hMρ0)
  have hVmeasIntegrand : ∀ u ∈ Icc (0 : ℝ) H,
      Integrable (fun ω => W (u, ω)) A.P ∧
      ∫ ω, W (u, ω) ∂A.P ≤ α * (Cm + Mρ) := by
    intro u hu
    obtain ⟨hEmpInt, hEmpBound⟩ := hpartmom u hu
    have hQae : (fun ω => Q (u, ω)) =ᵐ[A.P]
        (fun ω => (N : ℝ)⁻¹ *
          ∑ k : Fin N, jbracket (A.X u.toNNReal ω k) ^ Pw) := by
      filter_upwards [hXae] with ω hω
      simp [Q, hω u]
    have hQint : Integrable (fun ω => Q (u, ω)) A.P :=
      hEmpInt.congr hQae.symm
    have hWint : Integrable (fun ω => W (u, ω)) A.P := by
      dsimp [W]
      exact (hQint.add (integrable_const Mρ)).const_mul α
    have hQintegral : (∫ ω, Q (u, ω) ∂A.P) ≤ Cm := by
      rw [integral_congr_ae hQae]
      exact hEmpBound
    have hWbound : (∫ ω, W (u, ω) ∂A.P) ≤ α * (Cm + Mρ) := by
      dsimp [W]
      rw [integral_const_mul, integral_add hQint (integrable_const Mρ)]
      have hconst : (∫ _ω : A.Ω, Mρ ∂A.P) = Mρ := by simp
      rw [hconst]
      have hsum : (∫ ω, Q (u, ω) ∂A.P) + Mρ ≤ Cm + Mρ := by
        linarith
      exact mul_le_mul_of_nonneg_left hsum hα0
    exact ⟨hWint, hWbound⟩
  let Cbar : ℝ := α * (Cm + Mρ)
  have hCbar0 : 0 ≤ Cbar := by
    dsimp [Cbar]
    exact mul_nonneg hα0 (add_nonneg hCm0 hMρ0)
  have hWbar : ∀ u ∈ Icc (0 : ℝ) H,
      ∫⁻ ω, ‖W (u, ω)‖ₑ ∂A.P ≤ ENNReal.ofReal Cbar := by
    intro u hu
    obtain ⟨hWint, hWbound⟩ := hVmeasIntegrand u hu
    have hWnn : ∀ ω, 0 ≤ W (u, ω) := fun ω => hW0 (u, ω)
    calc
      ∫⁻ ω, ‖W (u, ω)‖ₑ ∂A.P =
          ∫⁻ ω, ENNReal.ofReal (W (u, ω)) ∂A.P := by
        refine lintegral_congr fun ω => ?_
        exact Real.enorm_eq_ofReal (hWnn ω)
      _ = ENNReal.ofReal (∫ ω, W (u, ω) ∂A.P) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hWint
          (Eventually.of_forall hWnn)]
      _ ≤ ENNReal.ofReal Cbar :=
        ENNReal.ofReal_le_ofReal (by simpa [Cbar] using hWbound)
  have hWprod : Integrable W
      ((volume.restrict (Icc (0 : ℝ) H)).prod A.P) :=
    s102_prodInt (P := A.P) (C := Cbar) hWm hWbar
  let Vf : A.Ω → ℝ := fun ω => ∫ v in Icc (0 : ℝ) H, W (v, ω)
  have hVf : Integrable Vf A.P := by
    exact hWprod.integral_prod_right
  have hWcont : ∀ᵐ ω ∂A.P,
      ContinuousOn (fun v : ℝ => W (v, ω)) (Icc (0 : ℝ) H) := by
    have hqcont : ∀ᵐ ω ∂A.P, ContinuousOn
        (fun v : ℝ => (N : ℝ)⁻¹ *
          ∑ k : Fin N, jbracket (A.X v.toNNReal ω k) ^ Pw)
        (Icc (0 : ℝ) H) := by
      filter_upwards [hXcont] with ω hω
      have hc : Continuous fun v : ℝ => (N : ℝ)⁻¹ *
          ∑ k : Fin N, jbracket (A.X v.toNNReal ω k) ^ Pw := by
        refine continuous_const.mul (continuous_finsetSum _ fun k _ => ?_)
        exact (by
          exact hjcont.comp ((hω k).comp continuous_real_toNNReal))
      exact hc.continuousOn
    filter_upwards [hXae, hqcont] with ω hωX hωq
    have htarget : ContinuousOn (fun v : ℝ => α * ((N : ℝ)⁻¹ *
        ∑ k : Fin N, jbracket (A.X v.toNNReal ω k) ^ Pw + Mρ))
        (Icc (0 : ℝ) H) :=
      (hωq.add continuousOn_const).const_mul α
    apply htarget.congr
    intro v hv
    simp [W, Q, hωX v]
  refine ⟨Vf, hVf, ?_⟩
  filter_upwards [hXae, hXcont, fp81s21_moving_raw_eta_horizonL1F_ae
    p R hH hN A hphysical, hWcont] with ω hωX hωcont hL1 hWc
  have hcz : ∀ k : Fin N, Continuous fun t : ℝ≥0 => A.X t ω k := hωcont
  have hMajor : ∀ v ∈ Icc (0 : ℝ) H,
      dualNormE r Pw (fp81s21_movingRawEtaField p R A ω v) ≤
        ENNReal.ofReal (W (v, ω)) := by
    intro v hv
    have hμint := (hρmom v hv).1
    have hmeta : s102_Meta C0 Pw (r26t3_mu R v)
        (A.X v.toNNReal ω) ≤ W (v, ω) := by
      have hsum : (N : ℝ)⁻¹ *
          ∑ k : Fin N, jbracket (A.X v.toNNReal ω k) ^ Pw +
          ∫ x, jbracket x ^ Pw ∂(r26t3_mu R v) ≤ Q (v, ω) + Mρ := by
        have hQeq : Q (v, ω) = (N : ℝ)⁻¹ *
            ∑ k : Fin N, jbracket (A.X v.toNNReal ω k) ^ Pw := by
          simp [Q, hωX v]
        rw [hQeq]
        linarith [hρmom v hv]
      dsimp [s102_Meta, W, α]
      exact mul_le_mul_of_nonneg_left hsum (mul_nonneg
        (Real.sqrt_nonneg _) hC0.le)
    have hηb : ∀ f, IsR2WeightedTest r Pw f →
        |fp81s21_movingRawEtaField p R A ω v f| ≤
          W (v, ω) * (weightedSobolevE r Pw f).toReal := by
      intro f hf
      have h := hηbound (r26t3_mu R v) hμint (A.X v.toNNReal ω) f hf
      change |Real.sqrt N *
        (HRS.Whole.pair (HRS.Whole.empirical (A.X v.toNNReal ω)) f -
          HRS.Whole.pair (r26t3_mu R v) f)| ≤ _ at h
      simpa [fp81s21_movingRawEtaField, HRS.MS.R2Interp.s102_etaf] using
        h.trans (mul_le_mul_of_nonneg_right hmeta ENNReal.toReal_nonneg)
    exact s102_dualNormE_le (hW0 (v, ω)) hηb
  have hdualInt : (∫⁻ v in Icc (0 : ℝ) H,
      dualNormE r Pw (fp81s21_movingRawEtaField p R A ω v)).toReal ≤ Vf ω := by
    have hmono : (∫⁻ v in Icc (0 : ℝ) H,
        dualNormE r Pw (fp81s21_movingRawEtaField p R A ω v)) ≤
        ∫⁻ v in Icc (0 : ℝ) H, ENNReal.ofReal (W (v, ω)) := by
      refine lintegral_mono_ae ?_
      exact (ae_restrict_iff' measurableSet_Icc).2
        (Eventually.of_forall fun v hv => hMajor v hv)
    have hWintegrable : IntegrableOn (fun v : ℝ => W (v, ω))
        (Icc (0 : ℝ) H) := hWc.integrableOn_Icc
    have hWnonneg : ∀ v : ℝ, 0 ≤ W (v, ω) := fun v => hW0 (v, ω)
    rw [← ofReal_integral_eq_lintegral_ofReal hWintegrable
      (Eventually.of_forall hWnonneg)] at hmono
    have hnonneg : 0 ≤ ∫ v in Icc (0 : ℝ) H, W (v, ω) :=
      integral_nonneg_of_ae (ae_restrict_iff' measurableSet_Icc |>.2
        (Eventually.of_forall fun v hv => hWnonneg v))
    have hbound : (∫⁻ v in Icc (0 : ℝ) H,
        dualNormE r Pw (fp81s21_movingRawEtaField p R A ω v)) ≤
        ENNReal.ofReal (∫ v in Icc (0 : ℝ) H, W (v, ω)) := hmono
    have hreal := ENNReal.toReal_le_of_le_ofReal hnonneg hbound
    simpa [Vf] using hreal
  exact hdualInt

#print axioms HRS.Fp81.S21.fp81s21_moving_raw_eta_integrable_variation_majorant

end HRS.Fp81.S21

end
