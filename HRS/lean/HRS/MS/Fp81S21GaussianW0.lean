import HRS.MS.Fp81S21ResponseAll
import HRS.MS.Fp81S21RespIid3
import HRS.MS.S21E_Wick
import HRS.MS.ProClosureS111GaussianLaw

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.S21E
open HRS.MS.S104e.C HRS.MS.R2WinOrbNL HRS.MS.Ul

/-- Quantitative continuity of the chosen adjoint on arbitrary oscillator
    data, on a fixed finite horizon. The constant precedes the test. -/
theorem fp81s21_gaussian_W0_propagator_bound
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {t : ℝ} (ht : 0 ≤ t) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ φ : Euc p.d → ℝ,
      IsOscTest (wholeSpaceIndex p.d : ℝ) φ →
      ∀ r ∈ Icc (0 : ℝ) t, ∀ x,
        |propagatorW (r26t3_coeff R) r t φ x| ≤
          K * oscNorm (wholeSpaceIndex p.d : ℝ) (φ : Euc p.d → ℝ) := by
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  let η : ℝ := (max 0 (p.s - p.d + 1) + 1) / 2
  have hmax : max 0 (p.s - p.d + 1) < 1 :=
    max_lt (by norm_num) (by linarith)
  have hη0 : max 0 (p.s - p.d + 1) < η := by dsimp [η]; linarith
  have hη1 : η < 1 := by dsimp [η]; linarith
  have hηp : 0 < η := lt_of_le_of_lt (le_max_left _ _) hη0
  obtain ⟨CP, hCP1, hP1, hP2, hP3, hP4, hP5, hP6, hP7⟩ :=
    c1_P_fields (d := p.d) p.a p.β⁻¹ p.ha (inv_pos.2 p.hβ) hηp hη1 2 (t + 1)
  have hP : Nonempty (C5PHyp p.d p.a p.β⁻¹ 2 η (t + 1)) :=
    ⟨⟨CP, hCP1, hP1, hP2, hP3, hP4, hP5, hP6, hP7⟩⟩
  have hAjc := c5_Ajc p.hd p.hs0 hsd p.ha p.hβ
    δ p.c₁ p.C₁ R.thermal R.resulting hη0 hη1 (t + 1)
  obtain ⟨hyp⟩ := c5_volHyp p.hd p.hs0 hsd p.hβ
    δ p.c₁ p.C₁ R.thermal R.resulting p.ha hη0 hη1 (by linarith) hP hAjc
  obtain ⟨C, hC, hex⟩ := c3_volterra_exists 2 η (t + 1)
    hηp hη1 (by linarith) _ _ hyp
  have hn : (4 : ℝ) + (p.d : ℝ) / 2 < ((p.d + 10 : ℕ) : ℝ) := by
    push_cast; linarith
  have hm : (p.d : ℝ) <
      ((wholeSpaceIndex p.d : ℝ) - ((p.d + 10 : ℕ) : ℝ)) / 2 := by
    dsimp [wholeSpaceIndex]; push_cast; linarith
  obtain ⟨B, hB, hb⟩ := HRS.MS.ProClosureS111.oscillator_derivative_norm_bound
    (d := p.d) (m := (wholeSpaceIndex p.d : ℝ)) 4 (p.d + 10) hn hm
  refine ⟨C * (2 * B), by positivity, fun φ hφ => ?_⟩
  let A := B * oscNorm (wholeSpaceIndex p.d : ℝ) (φ : Euc p.d → ℝ)
  have hA : 0 ≤ A := mul_nonneg hB (Real.sqrt_nonneg _)
  have hbd : Bd 4 A φ :=
    ⟨hφ.1.of_le (by exact WithTop.coe_le_coe.2 (show (4 : ℕ∞) ≤ ⊤ from le_top)), fun i hi x => hb φ hφ i hi x⟩
  have hhol : HolB 2 η (2 * A) φ := holB_of_bd hηp hη1.le hbd
  obtain ⟨_, _, hvan, _⟩ := fp81s21_datum_of_osc hηp hη1.le hφ
  obtain ⟨w, hwH, hwt, hwc, hwm, _, hwTC⟩ :=
    hex t ⟨ht, by linarith⟩ (2 * A) φ hhol hvan
  have hw2 : ∀ r ∈ Icc (0 : ℝ) t, Bd 2 (C * (2 * A)) (w r) :=
    fun r hr => ⟨(hwH r hr).1.1.of_le (by norm_num),
      fun i hi x => (hwH r hr).1.2 i (by omega) x⟩
  have hmem : ∀ v ∈ Icc (0 : ℝ) t, v ∈ Icc (0 : ℝ) (t + 1) :=
    fun v hv => ⟨hv.1, by linarith [hv.2]⟩
  have hg2 : ∀ r ∈ Icc (0 : ℝ) t,
      Bd 2 (hyp.CA * (C * (2 * A))) (s103bQ p.d p.s (R.ρ r) (w r)) :=
    fun r hr => hyp.A_bd r (hmem r hr) _ (w r) (hwH r hr)
  have hTCg := hyp.A_tc t ⟨ht, by linarith⟩ _ w hwH hwTC
  have hclass : IsClassicalAdjointW (r26t3_coeff R) t φ w := by
    apply c4_classical p.s p.a p.β p.ha p.hβ R.ρ ht
      (hbd.mono_N (by omega) |>.mono_A (by linarith : A ≤ 2 * A))
      hw2 (fun i hi => hwc i (by omega)) hwt (fun r hr => rfl) hg2
    · intro r₀ hr₀ ε hε
      obtain ⟨εr, hεr, h⟩ := hTCg 0 (Nat.zero_le _) ε hε
      exact ⟨εr, hεr, fun r hr hd y => c5_norm0_le (h r hr r₀ hr₀ hd y)⟩
    · exact fun r hr x => hwm r hr x
  have heq := HRS.MS.S104e.s104e_unique p.hd p.hs0 hsd p.ha p.hβ
    δ p.c₁ p.C₁ R.thermal R.admissible R.resulting t ht ⟨ht, le_rfl⟩ hclass
  intro r hr x
  change |propagatorW ((quadraticGradientDyn p.d p.s p.a p.β).coeff R.ρ) r t φ x| ≤ _
  rw [heq r hr]
  have h := (hw2 r hr).2 0 (Nat.zero_le _) x
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  exact h.trans (le_of_eq (by dsimp [A]; ring))

/-- Hermite truncations converge uniformly after applying the actual chosen
propagator, including at the endpoints of the time interval. -/
theorem fp81s21_gaussian_W0_propagator_truncation
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {t : ℝ} (ht : 0 ≤ t) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) t)
    (φ : Euc p.d → ℝ) (hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ) :
    TendstoUniformly
      (fun n => propagatorW (r26t3_coeff R) r t (HRS.MS.MovOsc.mo_pSum φ n))
      (propagatorW (r26t3_coeff R) r t φ) atTop := by
  obtain ⟨K, hK, hb⟩ := fp81s21_gaussian_W0_propagator_bound p R ht
  have htest : ∀ n, IsOscTest (wholeSpaceIndex p.d : ℝ)
      (HRS.MS.MovOsc.mo_pSum φ n) := by
    intro n
    obtain ⟨f, hf⟩ := HRS.MS.Mov63.mn_pSum_schwartz φ n
    refine ⟨?_, (HRS.MS.MovOsc.mo_pSum_oscNorm_le _ hφ.2 n).1⟩
    rw [← hf]
    exact f.smooth (⊤ : ℕ∞)
  have hdiff : ∀ n, IsOscTest (wholeSpaceIndex p.d : ℝ)
      (fun x => φ x - HRS.MS.MovOsc.mo_pSum φ n x) :=
    fun n => ⟨hφ.1.sub (htest n).1,
      HRS.MS.MovLin.mov2d_memOsc_sub hφ.2 (htest n).2⟩
  have htail : Tendsto (fun n => K * oscNorm (wholeSpaceIndex p.d : ℝ)
      (fun x => φ x - HRS.MS.MovOsc.mo_pSum φ n x)) atTop (𝓝 0) := by
    simpa using (HRS.MS.MovOsc.mo_hsum_tail _ hφ.2).const_mul K
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [htail.eventually (gt_mem_nhds hε)] with n hn
  intro x
  have hlin := fp81s21_U_linear_of_osc_test p R hφ (htest n) (-1) ht hr
  have hsub : propagatorW (r26t3_coeff R) r t
      (fun y => φ y - HRS.MS.MovOsc.mo_pSum φ n y) x =
      propagatorW (r26t3_coeff R) r t φ x -
        propagatorW (r26t3_coeff R) r t (HRS.MS.MovOsc.mo_pSum φ n) x := by
    simpa only [r26t3_U, neg_one_mul, sub_eq_add_neg] using congrFun hlin x
  have hbound := hb _ (hdiff n) r hr x
  rw [hsub] at hbound
  simpa only [Real.dist_eq, abs_sub_comm] using hbound.trans_lt hn

open HRS.MS.S111X1 HRS.MS.S111X2 HRS.MS.ProClosureS111
open HRS.Whole.Q34 HRS.MC.E213U18

private theorem fp81s21_gaussian_W0_memLp
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {t : ℝ} (ht : 0 ≤ t) (φ : oscSub p.d (wholeSpaceIndex p.d)) :
    MemLp (propagatorW (r26t3_coeff R) 0 t φ) 2 (r26t3_mu R 0) := by
  letI := fp81s21_initialMeasure_isProbability p R
  exact x1_classical_memLp (fp81s21_U_osc_test_classical p R φ.property ht)
    ⟨le_rfl, ht⟩ _

private theorem fp81s21_gaussian_W0_class_linear
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    [IsProbabilityMeasure (r26t3_mu R 0)]
    {t : ℝ} (ht : 0 ≤ t)
    (φ ψ : oscSub p.d (wholeSpaceIndex p.d)) (c : ℝ) :
    s111x2_cl (fp81s21_gaussian_W0_memLp p R ht (φ + c • ψ)) =
      s111x2_cl (fp81s21_gaussian_W0_memLp p R ht φ) +
        c • s111x2_cl (fp81s21_gaussian_W0_memLp p R ht ψ) := by
  have hf := fp81s21_gaussian_W0_memLp p R ht φ
  have hg := fp81s21_gaussian_W0_memLp p R ht ψ
  have hh := fp81s21_gaussian_W0_memLp p R ht (φ + c • ψ)
  have hu := fp81s21_U_linear_of_osc_test p R φ.property ψ.property c ht ⟨le_rfl, ht⟩
  apply Lp.ext
  filter_upwards [s111x2_cl_ae hh, s111x2_cl_ae hf, s111x2_cl_ae hg,
    Lp.coeFn_add (s111x2_cl hf) (c • s111x2_cl hg),
    Lp.coeFn_smul c (s111x2_cl hg)] with x h1 h2 h3 h4 h5
  rw [← h1, h4, Pi.add_apply, h5, Pi.smul_apply, smul_eq_mul, ← h2, ← h3]
  change HRS.Whole.projMean (r26t3_mu R 0)
    (r26t3_U R 0 t (fun y => (φ : Euc p.d → ℝ) y + c * (ψ : Euc p.d → ℝ) y)) x = _
  rw [hu]
  exact s111x2_projMean_lin hf hg c x

/-- The actual centered response on oscillator tests, as an L² linear map.
The resolvent uses nonnegative preparation strength, including zero. -/
private def fp81s21_gaussian_W0_responseLinear
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    [IsProbabilityMeasure (r26t3_mu R 0)]
    {Mg : ℝ} {K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ] Lp ℝ 2 (r26t3_mu R 0)}
    (hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg)
    {t : ℝ} (ht : 0 ≤ t) :
    oscSub p.d (wholeSpaceIndex p.d) →ₗ[ℝ] Lp ℝ 2 (r26t3_mu R 0) := by
  let F := fun φ : oscSub p.d (wholeSpaceIndex p.d) =>
    s111x2_cl (fp81s21_gaussian_W0_memLp p R ht φ)
  have hlin : ∀ φ ψ c, F (φ + c • ψ) = F φ + c • F ψ :=
    fp81s21_gaussian_W0_class_linear p R ht
  have hzero : F 0 = 0 := by
    have he := hlin 0 0 1
    simp only [one_smul, zero_add] at he
    exact add_left_cancel (he.symm.trans (add_zero _).symm)
  let L : oscSub p.d (wholeSpaceIndex p.d) →ₗ[ℝ] Lp ℝ 2 (r26t3_mu R 0) :=
    { toFun := F
      map_add' := fun φ ψ => by simpa only [one_smul] using hlin φ ψ 1
      map_smul' := fun c φ => by
        simpa only [zero_add, hzero, RingHom.id_apply] using hlin 0 φ c }
  exact (s111x2_Rm hK.posOp p.hγ).toLinearMap.comp L

private theorem fp81s21_gaussian_W0_responseLinear_ae
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    [IsProbabilityMeasure (r26t3_mu R 0)]
    {Mg : ℝ} {K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ] Lp ℝ 2 (r26t3_mu R 0)}
    (hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg)
    {t : ℝ} (ht : 0 ≤ t) (φ : oscSub p.d (wholeSpaceIndex p.d)) :
    HRS.Whole.responseInverse (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
      (propagatorW (r26t3_coeff R) 0 t φ) =ᵐ[r26t3_mu R 0]
      (fp81s21_gaussian_W0_responseLinear p R hK ht φ : Euc p.d → ℝ) :=
  s111x2_responseInverse_ae hK p.hγ (fp81s21_gaussian_W0_memLp p R ht φ)

/-- Oscillator continuity of the actual response, with the constant chosen
before the test. -/
private theorem fp81s21_gaussian_W0_responseLinear_bound
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    [IsProbabilityMeasure (r26t3_mu R 0)]
    {Mg : ℝ} {K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ] Lp ℝ 2 (r26t3_mu R 0)}
    (hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg)
    {t : ℝ} (ht : 0 ≤ t) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ φ : oscSub p.d (wholeSpaceIndex p.d),
      ‖fp81s21_gaussian_W0_responseLinear p R hK ht φ‖ ≤
        B * oscNorm (wholeSpaceIndex p.d : ℝ) (φ : Euc p.d → ℝ) := by
  obtain ⟨B, hB, hb⟩ := fp81s21_gaussian_W0_propagator_bound p R ht
  refine ⟨B, hB, fun φ => ?_⟩
  have hf := fp81s21_gaussian_W0_memLp p R ht φ
  have hn : ‖s111x2_toLp (r26t3_mu R 0)
      (propagatorW (r26t3_coeff R) 0 t φ)‖ ≤ B * oscNorm (wholeSpaceIndex p.d : ℝ) (φ : Euc p.d → ℝ) := by
    have hx : ∀ᵐ x ∂r26t3_mu R 0,
        ‖s111x2_toLp (r26t3_mu R 0) (propagatorW (r26t3_coeff R) 0 t φ) x‖ ≤
          B * oscNorm (wholeSpaceIndex p.d : ℝ) (φ : Euc p.d → ℝ) := by
      filter_upwards [s111x2_toLp_ae hf] with x hx
      rw [hx, Real.norm_eq_abs]
      exact hb φ φ.property 0 ⟨le_rfl, ht⟩ x
    simpa [measureUnivNNReal, oscNorm] using Lp.norm_le_of_ae_bound
      (mul_nonneg hB (Real.sqrt_nonneg _)) hx
  change ‖s111x2_Res hK.posOp p.hγ (s111x2_cl hf)‖ ≤ _
  refine (s111x2_Res_bounds hK.posOp p.hγ _).2.2.trans ?_
  rw [s111x2_cl_eq_Pc hf]
  exact (Pc_norm_le _).trans hn

/-- Extension of the actual response coordinates to every oscillator test.
Only the coordinate certificate is supplied; the limiting response is
identified through its bounded L² resolvent. -/
private theorem fp81s21_gaussian_W0_observation_ae
    (p : Parameters) {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (a : ℝ) (ha : 0 ≤ a)
    (τ : Icc (0 : ℝ) p.T)
    (hmeas : AEStronglyMeasurable (responseWindow R a) (r26t3_mu R 0))
    (hcoord : ∀ x α,
      OscDual.coord (OscPath.at' (responseWindow R a x) τ) α =
        r26t3_a R (propagatorW (r26t3_coeff R) 0 (a + τ)
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x)
    (φ : Euc p.d → ℝ) (hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ) :
    (fun x => s21eObs (wholeSpaceIndex p.d : ℝ) p.T hφ.2 τ
      (responseWindow R a x)) =ᵐ[r26t3_mu R 0]
      HRS.Whole.responseInverse (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
        (propagatorW (r26t3_coeff R) 0 (a + τ) φ) := by
  classical
  letI := fp81s21_initialMeasure_isProbability p R
  have ht : 0 ≤ a + (τ : ℝ) := add_nonneg ha τ.2.1
  obtain ⟨Mg, K, hK⟩ := fp81s21_actualInitialKRep_exists p hδ hδh R
  let G := fp81s21_gaussian_W0_responseLinear p R hK ht
  let ψ : oscSub p.d (wholeSpaceIndex p.d) := ⟨φ, hφ⟩
  let v := fun x => OscPath.at' (responseWindow R a x) τ
  have hbase : ∀ α : MultiIndex p.d,
      (fun x => OscDual.coord (v x) α) =ᵐ[r26t3_mu R 0]
        (G (initialTestBasis (wholeSpaceIndex p.d : ℝ) α) : Euc p.d → ℝ) := by
    intro α
    have hf := fp81s21_gaussian_W0_memLp p R ht
      (initialTestBasis (wholeSpaceIndex p.d : ℝ) α)
    have h1 := fp81s21_response_inverse_ae hδ hδh R _ hf
    have h2 := fp81s21_gaussian_W0_responseLinear_ae p R hK ht
      (initialTestBasis (wholeSpaceIndex p.d : ℝ) α)
    filter_upwards [h1.trans h2] with x hx
    exact (hcoord x α).trans hx
  have hsection : ∀ n,
      (fun x => OscDual.eval (v x) (initialTestSection ψ n : Euc p.d → ℝ))
        =ᵐ[r26t3_mu R 0] (G (initialTestSection ψ n) : Euc p.d → ℝ) := by
    intro n
    let c := fun α : MultiIndex p.d =>
      oscEigenvalue p.d α ^ ((wholeSpaceIndex p.d : ℝ) / 2) *
        HRS.Whole.hermiteCoeff φ α
    let F := fun α => G (initialTestBasis (wholeSpaceIndex p.d : ℝ) α)
    have hsum := Lp.coeFn_finsetSum (HRS.MS.MovOsc.mova2_S p.d n)
      (fun α => c α • F α)
    have hsmul : ∀ᵐ x ∂r26t3_mu R 0, ∀ α : MultiIndex p.d,
        (c α • F α : Lp ℝ 2 (r26t3_mu R 0)) x = c α * F α x :=
      ae_all_iff.2 fun α => by
        filter_upwards [Lp.coeFn_smul (c α) (F α)] with x hx
        exact hx
    filter_upwards [ae_all_iff.2 hbase, hsum, hsmul] with x hx hs hm
    rw [initialTestSection_eval]
    change _ = (G (∑ α ∈ HRS.MS.MovOsc.mova2_S p.d n,
      c α • initialTestBasis (wholeSpaceIndex p.d : ℝ) α) : Lp ℝ 2 (r26t3_mu R 0)) x
    simp only [map_sum, map_smul]
    change _ = (∑ α ∈ HRS.MS.MovOsc.mova2_S p.d n, c α • F α :
      Lp ℝ 2 (r26t3_mu R 0)) x
    rw [hs]
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro α hα
    rw [hm α, ← hx α]
  have hseqMeas : ∀ n, AEStronglyMeasurable
      (fun x => OscDual.eval (v x) (initialTestSection ψ n : Euc p.d → ℝ))
      (r26t3_mu R 0) := by
    intro n
    have h := (s21eObs (wholeSpaceIndex p.d : ℝ) p.T
      (initialTestSection ψ n).property.2 τ).continuous.comp_aestronglyMeasurable hmeas
    simpa only [Function.comp_def, s21eObs_apply] using h
  have hleft := tendstoInMeasure_of_tendsto_ae hseqMeas
    (Eventually.of_forall fun x => initialTestSection_eval_tendsto ψ (v x))
  have hright := tendstoInMeasure_of_tendsto_Lp
    (linear_feature_section_tendsto G
      (fp81s21_gaussian_W0_responseLinear_bound p R hK ht) ψ)
  have heq := tendstoInMeasure_ae_unique hleft
    (TendstoInMeasure.congr_left (fun n => (hsection n).symm) hright)
  have hresp := fp81s21_gaussian_W0_responseLinear_ae p R hK ht ψ
  simpa only [s21eObs_apply] using heq.trans hresp.symm

/-- The initial cubic Wick identity and its integrability, for every original
oscillator test and every nonnegative preparation strength.

The proposed `Rad` and `W0` abbreviations are expanded in the signature.
The derived probability instance is installed after `R`, since `initialKappa`
requires it; this adds no hypothesis and preserves the radius quantifiers. -/
theorem fp81s21_gaussian_W0 (p : Parameters) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
      letI := fp81s21_initialMeasure_isProbability p R
      ∀ a : ℝ, 0 ≤ a → ∀ (τ : Fin 3 → Icc (0 : ℝ) p.T)
        (φ : Fin 3 → Euc p.d → ℝ)
        (hφ : ∀ i, IsOscTest (wholeSpaceIndex p.d : ℝ) (φ i)),
      let ℓ := fun i => s21eObs (wholeSpaceIndex p.d : ℝ) p.T (hφ i).2 (τ i)
      let g := fun i => HRS.Whole.responseInverse (rieszKernel p.d p.s)
        (r26t3_mu R 0) p.γ
        (propagatorW (r26t3_coeff R) 0 (a + τ i) (φ i))
      initialKappa R a (trilin ℓ) =
          (∫ x, g 0 x * g 1 x * g 2 x ∂r26t3_mu R 0) ∧
        Integrable (fun x => g 0 x * g 1 x * g 2 x) (r26t3_mu R 0) := by
  obtain ⟨δb, hb0, hbh, hb⟩ := fp81s21_responseWindow_all_strengths p
  obtain ⟨δp, hp0, hph, hp⟩ := fp81s21_responseWindow_genuine p
  obtain ⟨δz, hz0, hzh, hz⟩ := fp81s21_respIid_responseWindow_genuine p
  refine ⟨min δb (min δp δz), lt_min hb0 (lt_min hp0 hz0),
    (min_le_left _ _).trans hbh, fun δ hδ hδle R a ha τ φ hφ => ?_⟩
  have hδb := hδle.trans (min_le_left δb (min δp δz))
  have hδp := hδle.trans ((min_le_right δb (min δp δz)).trans (min_le_left δp δz))
  have hδz := hδle.trans ((min_le_right δb (min δp δz)).trans (min_le_right δp δz))
  have hδh := hδb.trans hbh
  letI := fp81s21_initialMeasure_isProbability p R
  obtain ⟨B, hB, hbnd⟩ := hb δ hδ hδb R
  obtain ⟨hmeas, hcube, hbound, _, _⟩ := hbnd a ha
  let ℓ := fun i => s21eObs (wholeSpaceIndex p.d : ℝ) p.T (hφ i).2 (τ i)
  let g := fun i => HRS.Whole.responseInverse (rieszKernel p.d p.s)
    (r26t3_mu R 0) p.γ (propagatorW (r26t3_coeff R) 0 (a + τ i) (φ i))
  change initialKappa R a (trilin ℓ) = _ ∧ Integrable _ _
  have hcoord : ∀ x (t : Icc (0 : ℝ) p.T) α,
      OscDual.coord (OscPath.at' (responseWindow R a x) t) α =
        r26t3_a R (propagatorW (r26t3_coeff R) 0 (a + t)
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x := by
    intro x t α
    by_cases hγ : 0 < p.γ
    · exact (hp δ hδ hδp R hγ a ha x).choose_spec.2 t α
    · have hγ0 : p.γ = 0 := le_antisymm (le_of_not_gt hγ) p.hγ
      exact (hz δ hδ hδz R hγ0 a ha x).choose_spec.2 t α
  have hae : ∀ i : Fin 3,
      (fun x => ℓ i (responseWindow R a x)) =ᵐ[r26t3_mu R 0] g i := by
    intro i
    exact fp81s21_gaussian_W0_observation_ae p hδ hδh R a ha (τ i)
      hmeas (fun x α => hcoord x (τ i) α) (φ i) (hφ i)
  have hprod : (fun x => ℓ 0 (responseWindow R a x) *
      ℓ 1 (responseWindow R a x) * ℓ 2 (responseWindow R a x)) =ᵐ[r26t3_mu R 0]
      (fun x => g 0 x * g 1 x * g 2 x) := (hae 0 |>.mul (hae 1)).mul (hae 2)
  have hnormprod : Integrable (fun x => ‖responseWindow R a x‖ *
      ‖responseWindow R a x‖ * ‖responseWindow R a x‖) (r26t3_mu R 0) := by
    apply hcube.congr
    filter_upwards with x
    ring
  constructor
  · exact (s21e_kappa0_trilin (r26t3_mu R 0) hmeas hnormprod ℓ).trans
      (integral_congr_ae hprod)
  · have hm : ∀ i : Fin 3, AEStronglyMeasurable
        (fun x => ℓ i (responseWindow R a x)) (r26t3_mu R 0) :=
      fun i => (ℓ i).continuous.comp_aestronglyMeasurable hmeas
    have hi : Integrable (fun x => ℓ 0 (responseWindow R a x) *
        ℓ 1 (responseWindow R a x) * ℓ 2 (responseWindow R a x)) (r26t3_mu R 0) := by
      refine Integrable.of_bound ((hm 0 |>.mul (hm 1)).mul (hm 2))
        ((‖ℓ 0‖ * B) * (‖ℓ 1‖ * B) * (‖ℓ 2‖ * B))
        (Eventually.of_forall fun x => ?_)
      have h : ∀ i : Fin 3, ‖ℓ i (responseWindow R a x)‖ ≤ ‖ℓ i‖ * B :=
        fun i => (ℓ i).le_opNorm _ |>.trans
          (mul_le_mul_of_nonneg_left (hbound x) (norm_nonneg _))
      simp only [norm_mul]
      gcongr
      · exact h 0
      · exact h 1
      · exact h 2
    exact hi.congr hprod

#print axioms fp81s21_gaussian_W0_propagator_bound
#print axioms fp81s21_gaussian_W0_propagator_truncation
#print axioms fp81s21_gaussian_W0_responseLinear
#print axioms fp81s21_gaussian_W0_responseLinear_bound
#print axioms fp81s21_gaussian_W0_observation_ae
#print axioms fp81s21_gaussian_W0
end HRS.Fp81.S21
end
