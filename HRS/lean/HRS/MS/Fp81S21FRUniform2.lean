import HRS.MS.Fp81S21FRUniform
import HRS.MS.Fp81S21InitialMab3

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section
namespace HRS.Fp81.S21
open S45 S99
open HRS.Whole
open HRS (Euc MemCb cbNorm)
open HRS.MS.R26T3

/-- A common mixed quadratic rate for fixed observables and an indexed feature family. -/
theorem fp81s21_initial_Mab_uniform
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {ι : Type} (Φ : ι → ℕ → Euc p.d → ℝ)
    (hΦ : ∀ i, IsSummableFeatureFamily (fp81s21_J1 p.d) (Φ i))
    (F : ∀ i, InitialFamData R (Φ i))
    (S : ℝ) (hS0 : 0 ≤ S)
    (hSum : ∀ i, featureSum (fp81s21_J1 p.d) (Φ i) ≤ S)
    {u v : Euc p.d → ℝ} (hu : MemCb (fp81s21_J1 p.d) u)
    (hv : MemCb (fp81s21_J1 p.d) v) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i, ∀ {G : Measure SeqL2} [IsProbabilityMeasure G],
      IsCenteredGaussianSeq G (fun j k =>
        HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
          (Φ i j) (Φ i k)) →
      ∀ N : ℕ, 2 ≤ N → ∀ {ψ : SeqL2 → ℝ}, S99.Bd 4 ψ →
      |(∫ X, s45_Yi N u (HRS.Whole.pair (r26t3_marg R N) u) X *
          (s45_Yi N v (HRS.Whole.pair (r26t3_marg R N) v) X *
            ψ (featureVec (Φ i) (r26t3_marg R N) X)) ∂(r26t3_Q R N)) -
        (∫ X, s45_Yi N u (HRS.Whole.pair (r26t3_marg R N) u) X *
          s45_Yi N v (HRS.Whole.pair (r26t3_marg R N) v) X ∂(r26t3_Q R N)) *
          (∫ X, ψ (featureVec (Φ i) (r26t3_marg R N) X) ∂(r26t3_Q R N)) -
        ∑' l, ∑' q, fp81s21_initial_kap (R := R) u (Φ i) l *
          fp81s21_initial_kap (R := R) v (Φ i) q *
            ∫ z, S99.pd (S99.pd ψ l) q z ∂G| ≤ K / Real.sqrt N := by
  have hsd : p.s < (p.d : ℝ) := by
    have hd0 : (0 : ℝ) ≤ (p.d : ℝ) / 2 := by positivity
    linarith [p.hs]
  obtain ⟨K₂, hK₂, hcorrect⟩ :=
    fp81s21_initial_orderOne_corrector hδ hδh R hγ
  obtain ⟨KB, hKB0, hKB⟩ := fp81s21_initial_Bq_bound hδ hδh E hγ
  obtain ⟨KT, hKT0, hTL2⟩ := fp81s21_initial_T_L2 hδ hδh E hγ
  obtain ⟨KY, hKY0, hY2⟩ := fp81s21_initial_Y_L2 hδ hδh E hγ
  obtain ⟨KM, hKM0, hMl⟩ :=
    fp81s21_initial_Mab_l_uniform hδ hδh R E hγ Φ hΦ F S hS0 hSum
  obtain ⟨KT1, hKT1, hT1⟩ := fp81s21_initial_T_L1 hδ hδh E hγ
  have hk0 : 1 ≤ fp81s21_k0 p.d := fp81s21_k0_ge_one p.d
  have hJ1 : 1 ≤ fp81s21_J1 p.d := by unfold fp81s21_J1; omega
  have hk0J : fp81s21_k0 p.d ≤ fp81s21_J1 p.d := by
    have h := fp81s21_J1_ge_k0 p.d
    omega
  have hu0 : MemCb (fp81s21_k0 p.d) u :=
    (HRS.MS.Tc5.tc5_cb_mono hk0J hu).1
  obtain ⟨χ, hχ2, hwf, hgen⟩ := hcorrect u hu0
  let Bχ : ℝ := K₂ * cbNorm (fp81s21_k0 p.d) u
  have hBχ0 : 0 ≤ Bχ := by
    dsimp [Bχ]
    exact mul_nonneg hK₂ (HRS.MS.Tc5.tc5_cb_nonneg _ _)
  have hχB : S47.S47Feat p.d p.s (R.ρ 0) p.γ u χ Bχ := by
    simpa [Bχ] using hwf
  let cv : ℝ := cbNorm (fp81s21_J1 p.d) v
  have hcv0 : 0 ≤ cv := HRS.MS.Tc5.tc5_cb_nonneg _ _
  let Cuv : ℝ := p.γ⁻¹ * Bχ * cv
  have hCuv0 : 0 ≤ Cuv := by positivity
  let K : ℝ := 2 * KB * Bχ * KY * cv + KM * Bχ * cv * S + 2 * KT1 * Cuv
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K, hK0, ?_⟩
  intro i G _ hG N hN ψ hψ
  let φ := Φ i
  have hφ := hΦ i
  have F := F i
  have hMl := hMl i hG
  let b : ℕ → ℝ := fun j => cbNorm (fp81s21_J1 p.d) (φ j)
  have hb0 : ∀ j, 0 ≤ b j := fun j => HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hbs : Summable b := hφ.2
  let Sb : ℝ := ∑' m, b m
  have hSb0 : 0 ≤ Sb := tsum_nonneg hb0
  have hSbS : Sb ≤ S := by simpa [Sb, b, featureSum, φ] using hSum i
  have hvbd : ∀ x, |v x| ≤ cv := fun x => by
    have h := HRS.MS.Tc5.tc5_cb_sup_le hv x
    simpa [cv, Real.norm_eq_abs] using h
  have hvc1 : ContDiff ℝ 1 v := hv.1.of_le (by exact_mod_cast hJ1)
  have hvm : Measurable v := hvc1.continuous.measurable
  have hDv : ∀ x, ‖fderiv ℝ v x‖ ≤ cv := fun x => s45_cb_deriv_le hJ1 hv x
  let cu : ℝ := cbNorm (fp81s21_J1 p.d) u
  have hcu0 : 0 ≤ cu := HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hubd : ∀ x, |u x| ≤ cu := fun x => by
    have h := HRS.MS.Tc5.tc5_cb_sup_le hu x
    simpa [cu, Real.norm_eq_abs] using h
  have huc1 : ContDiff ℝ 1 u := hu.1.of_le (by exact_mod_cast hJ1)
  have hv1 : ContDiff ℝ 1 (gradient χ) := s45_contDiff_gradient hχB.smooth
  let wuv : Euc p.d → ℝ := fun x => p.γ⁻¹ * ⟪gradient χ x, gradient v x⟫
  have hwuvbd : ∀ x, |wuv x| ≤ Cuv := by
    intro x
    dsimp [wuv, Cuv]
    rw [abs_mul, abs_of_nonneg (inv_nonneg.2 hγ.le)]
    exact (mul_le_mul_of_nonneg_left
      (s99_inner_grad_le hχB.B1 hDv x) (inv_nonneg.2 hγ.le)).trans_eq (by ring)
  have hwuvc : Continuous wuv :=
    continuous_const.mul (hv1.continuous.inner (s45_gradient_continuous hvc1))
  have hwuvm : Measurable wuv := hwuvc.measurable
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsqN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  haveI hP : IsProbabilityMeasure (r26t3_Q R N) := by
    rw [← E.law_eq N]
    exact (E.static N hN).prob
  haveI hν : IsProbabilityMeasure (r26t3_marg R N) := s99_nu_prob hN1
  haveI hμ : IsProbabilityMeasure (r26t3_mu R 0) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu E.reference.prob
  let P : Measure (EucConfig p.d N) := r26t3_Q R N
  let ν : Measure (Euc p.d) := r26t3_marg R N
  let Yu : EucConfig p.d N → ℝ := fun X =>
    s45_Yi N u (HRS.Whole.pair ν u) X
  let Yv : EucConfig p.d N → ℝ := fun X =>
    s45_Yi N v (HRS.Whole.pair ν v) X
  have hYvm : Measurable Yv :=
    measurable_const.mul ((s45_measurable_pair_empirical hN1 hvm).sub measurable_const)
  have hYvb : ∀ X, |Yv X| ≤ 2 * Real.sqrt N * cv := fun X => s99_Yi_bd hN1 hvbd X
  have hWc : Continuous (fun X : EucConfig p.d N => featureVec φ ν X) :=
    (s99_W_contDiff hN1 hJ1 hφ).continuous
  have hψ1 : S99.Bd 1 ψ := hψ.of_le (by norm_num)
  have hψWm : Measurable fun X : EucConfig p.d N => ψ (featureVec φ ν X) :=
    (hψ.1.continuous.comp hWc).measurable
  have hψWb : ∀ X : EucConfig p.d N, |ψ (featureVec φ ν X)| ≤ 1 :=
    fun X => hψ.abs_le _
  set Eψ : ℝ := ∫ X, ψ (featureVec φ ν X) ∂P with hEψ
  have hEψb : |Eψ| ≤ 1 := by
    have hi := norm_integral_le_of_norm_le_const (μ := P)
      (f := fun X : EucConfig p.d N => ψ (featureVec φ ν X)) (C := 1)
      (Filter.Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hψWb X)
    simpa [Eψ, Real.norm_eq_abs] using hi
  have hE1 := fp81s21_initial_E1b E hγ hN hφ
    (b := v) (u := u) (χ := χ) (Bχ := Bχ) hv hu0 hχB hψ1
  have hE0 := fp81s21_initial_E1b E hγ hN hφ
    (b := v) (u := u) (χ := χ) (Bχ := Bχ) hv hu0 hχB (s99_Bd_const 1)
  simp only [mul_one, s99_pd_const, mul_zero, integral_zero, tsum_zero, add_zero] at hE0
  let r : EucConfig p.d N → ℝ := fun X =>
    -Real.sqrt N * (HRS.Whole.pairEnergy (commutatorKernel p.d p.s (gradient χ))
      X (r26t3_mu R 0) -
      ∫ Y, HRS.Whole.pairEnergy (commutatorKernel p.d p.s (gradient χ))
        Y (r26t3_mu R 0) ∂P)
  have hsqrt : ∀ X : EucConfig p.d N,
      r X = -(fp81s21_initialBq R χ N X) / Real.sqrt N := by
    intro X
    dsimp [r, fp81s21_initialBq]
    have hsqr : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = N := by
      nlinarith [Real.sq_sqrt hN0.le]
    field_simp [hsqN.ne']
    rw [Real.sq_sqrt hN0.le]
  obtain ⟨hBi2, hB2, hBi, hB1⟩ := hKB N hN hχB.smooth hχB.B2
  have hBm : Measurable fun X : EucConfig p.d N => fp81s21_initialBq R χ N X := by
    unfold fp81s21_initialBq
    exact measurable_const.mul ((HRS.MS.Wr.wr9_measurable_pairEnergy
      (HRS.MS.Comm.comm_meas (s := p.s) (gradient χ) hv1.continuous.measurable)).sub
      measurable_const)
  have hBL2 : MemLp (fun X : EucConfig p.d N => fp81s21_initialBq R χ N X) 2 P :=
    (memLp_two_iff_integrable_sq hBm.aestronglyMeasurable).2 hBi2
  have hYvL2 : MemLp Yv 2 P := s99_memLp_two_of_bdd hYvm hYvb
  have hYvsq : ∫ X, (Yv X) ^ 2 ∂P ≤ (KY * cv) ^ 2 :=
    (hY2 N hN cv hcv0 v hvm hvbd).2
  have hRv : ∫ X, |r X| * |Yv X| ∂P ≤
      KB * Bχ * (KY * cv) / Real.sqrt N := by
    have hcs := s99_cs_bd hBL2 hYvL2 hB2 hYvsq
      (mul_nonneg hKB0 hBχ0) (mul_nonneg hKY0 hcv0)
    have heq : ∀ X : EucConfig p.d N,
        |r X| * |Yv X| =
          |fp81s21_initialBq R χ N X| * |Yv X| / Real.sqrt N := by
      intro X
      rw [hsqrt X, abs_div, abs_neg, abs_of_pos hsqN]
      ring
    simp_rw [heq]
    rw [integral_div]
    exact div_le_div_of_nonneg_right hcs hsqN.le
  have hrL2 : MemLp r 2 P := by
    have heq : r = fun X => -(Real.sqrt N)⁻¹ *
        fp81s21_initialBq R χ N X := by
      funext X
      rw [hsqrt X]
      ring
    rw [heq]
    exact hBL2.const_mul _
  have hrYint : Integrable (fun X : EucConfig p.d N => |r X| * |Yv X|) P := by
    have hfa : MemLp (fun X : EucConfig p.d N => |r X|) 2 P := hrL2.abs
    have hga : MemLp (fun X : EucConfig p.d N => |Yv X|) 2 P := hYvL2.abs
    exact hfa.integrable_mul hga
  have key : ∀ g : EucConfig p.d N → ℝ, (∀ X, |g X| ≤ 1) →
      |∫ X, r X * (Yv X * g X) ∂P| ≤ ∫ X, |r X| * |Yv X| ∂P := by
    intro g hg
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun X => norm_nonneg _) hrYint
      (Filter.Eventually.of_forall fun X => ?_)
    show ‖r X * (Yv X * g X)‖ ≤ |r X| * |Yv X|
    rw [Real.norm_eq_abs, abs_mul (r X), abs_mul (Yv X)]
    calc |r X| * (|Yv X| * |g X|) ≤ |r X| * (|Yv X| * 1) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hg X) (abs_nonneg _)) (abs_nonneg _)
      _ = |r X| * |Yv X| := by rw [mul_one]
  have hTe : ∀ X : EucConfig p.d N,
      p.γ⁻¹ * HRS.Whole.pair (HRS.Whole.empirical X)
        (fun x => ⟪gradient χ x, gradient v x⟫) =
      HRS.Whole.pair (HRS.Whole.empirical X) wuv := fun X =>
        (s99_pair_smul hN1 p.γ⁻¹ _ X).symm
  have hTm : Measurable fun X : EucConfig p.d N =>
      HRS.Whole.pair (HRS.Whole.empirical X) wuv :=
    s45_measurable_pair_empirical hN1 hwuvm
  have hTbd : ∀ X : EucConfig p.d N,
      |HRS.Whole.pair (HRS.Whole.empirical X) wuv| ≤ Cuv := fun X =>
    s45_abs_pair_empirical_le hN1 hwuvbd X
  have hrem1 : -(Real.sqrt N) *
      (∫ X, (HRS.Whole.pairEnergy (commutatorKernel p.d p.s (gradient χ))
        X (r26t3_mu R 0) -
        ∫ Y, HRS.Whole.pairEnergy (commutatorKernel p.d p.s (gradient χ))
          Y (r26t3_mu R 0) ∂P) *
        (Yv X * ψ (featureVec φ ν X)) ∂P) =
      ∫ X, r X * (Yv X * ψ (featureVec φ ν X)) ∂P := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    simp [r]
    ring
  have hrem0 : -(Real.sqrt N) *
      (∫ X, (HRS.Whole.pairEnergy (commutatorKernel p.d p.s (gradient χ))
        X (r26t3_mu R 0) -
        ∫ Y, HRS.Whole.pairEnergy (commutatorKernel p.d p.s (gradient χ))
          Y (r26t3_mu R 0) ∂P) * Yv X ∂P) =
      ∫ X, r X * Yv X ∂P := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    simp [r]
    ring
  have hE1' : (∫ X, Yu X * (Yv X * ψ (featureVec φ ν X)) ∂P) =
      (∫ X, r X * (Yv X * ψ (featureVec φ ν X)) ∂P) +
        (∑' l, ∫ X,
          (p.γ⁻¹ * HRS.Whole.pair (HRS.Whole.empirical X)
            (fun x => ⟪gradient χ x, gradient (φ l) x⟫)) *
            (Yv X * S99.pd ψ l (featureVec φ ν X)) ∂P) +
        ∫ X, HRS.Whole.pair (HRS.Whole.empirical X) wuv *
          ψ (featureVec φ ν X) ∂P := by
    have h := hE1
    simp_rw [hTe] at h
    rw [hrem1] at h
    simpa [Yu, Yv, P, ν] using h
  have hE0' : (∫ X, Yu X * Yv X ∂P) =
      (∫ X, r X * Yv X ∂P) +
        ∫ X, HRS.Whole.pair (HRS.Whole.empirical X) wuv ∂P := by
    have h := hE0
    simp_rw [hTe] at h
    rw [hrem0] at h
    simpa [Yu, Yv, P, ν] using h
  let RR1 : ℝ := ∫ X, r X * (Yv X * ψ (featureVec φ ν X)) ∂P
  let RR0 : ℝ := ∫ X, r X * Yv X ∂P
  let TT1 : ℝ := ∫ X,
    HRS.Whole.pair (HRS.Whole.empirical X) wuv * ψ (featureVec φ ν X) ∂P
  let TT0 : ℝ := ∫ X, HRS.Whole.pair (HRS.Whole.empirical X) wuv ∂P
  have hA1 : |RR1 - RR0 * Eψ| ≤ 2 *
      (KB * Bχ * (KY * cv) / Real.sqrt N) := by
    have h1 : |RR1| ≤ ∫ X, |r X| * |Yv X| ∂P := key _ hψWb
    have h0 : |RR0| ≤ ∫ X, |r X| * |Yv X| ∂P := by
      have hi := key (fun _ => (1 : ℝ)) (fun X => by simp)
      simpa [RR0] using hi
    calc |RR1 - RR0 * Eψ| ≤ |RR1| + |RR0| * |Eψ| := by
          refine (abs_sub _ _).trans ?_
          rw [abs_mul]
      _ ≤ (KB * Bχ * (KY * cv) / Real.sqrt N) +
          (KB * Bχ * (KY * cv) / Real.sqrt N) * 1 := by
          refine add_le_add (h1.trans hRv)
            (mul_le_mul (h0.trans hRv) hEψb (abs_nonneg _) ?_)
          exact (abs_nonneg _).trans (h0.trans hRv)
      _ = _ := by ring
  have hA3 : |TT1 - TT0 * Eψ| ≤ 2 * (KT1 * Cuv / Real.sqrt N) := by
    let c0 : ℝ := HRS.Whole.pair (r26t3_mu R 0) wuv
    have hTi : Integrable (fun X : EucConfig p.d N =>
        HRS.Whole.pair (HRS.Whole.empirical X) wuv) P :=
      Integrable.of_bound hTm.aestronglyMeasurable Cuv
        (Filter.Eventually.of_forall fun X => by
          rw [Real.norm_eq_abs]
          exact hTbd X)
    have hψi : Integrable (fun X : EucConfig p.d N => ψ (featureVec φ ν X)) P :=
      Integrable.of_bound hψWm.aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun X => by
          rw [Real.norm_eq_abs]
          exact hψWb X)
    have hTψi : Integrable (fun X : EucConfig p.d N =>
        HRS.Whole.pair (HRS.Whole.empirical X) wuv * ψ (featureVec φ ν X)) P :=
      Integrable.of_bound (hTm.mul hψWm).aestronglyMeasurable (Cuv * 1)
        (Filter.Eventually.of_forall fun X => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hTbd X) (hψWb X) (abs_nonneg _) hCuv0)
    have hid : TT1 - TT0 * Eψ = ∫ X,
        (HRS.Whole.pair (HRS.Whole.empirical X) wuv - c0) *
          (ψ (featureVec φ ν X) - Eψ) ∂P := by
      have heq : (fun X : EucConfig p.d N =>
          (HRS.Whole.pair (HRS.Whole.empirical X) wuv - c0) *
            (ψ (featureVec φ ν X) - Eψ)) = fun X =>
          (HRS.Whole.pair (HRS.Whole.empirical X) wuv * ψ (featureVec φ ν X) -
            Eψ * HRS.Whole.pair (HRS.Whole.empirical X) wuv) -
            c0 * (ψ (featureVec φ ν X) - Eψ) := by
        funext X
        ring
      have i1 : Integrable (fun X : EucConfig p.d N =>
          HRS.Whole.pair (HRS.Whole.empirical X) wuv * ψ (featureVec φ ν X) -
            Eψ * HRS.Whole.pair (HRS.Whole.empirical X) wuv) P :=
        hTψi.sub (hTi.const_mul Eψ)
      have i2 : Integrable (fun X : EucConfig p.d N =>
          c0 * (ψ (featureVec φ ν X) - Eψ)) P :=
        (hψi.sub (integrable_const _)).const_mul c0
      have i3 : Integrable (fun X : EucConfig p.d N =>
          Eψ * HRS.Whole.pair (HRS.Whole.empirical X) wuv) P := hTi.const_mul Eψ
      have i4 : Integrable (fun X : EucConfig p.d N =>
          ψ (featureVec φ ν X) - Eψ) P := hψi.sub (integrable_const _)
      rw [heq, integral_sub i1 i2, integral_sub hTψi i3, integral_const_mul,
        integral_const_mul, integral_sub hψi (integrable_const _)]
      simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one,
        smul_eq_mul, one_mul]
      rw [← hEψ]
      simp only [TT1, TT0]
      ring
    rw [hid, ← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    have hL1 := hT1 N hN Cuv hCuv0 wuv hwuvm hwuvbd
    have hint : Integrable (fun X : EucConfig p.d N =>
        2 * |HRS.Whole.pair (HRS.Whole.empirical X) wuv - c0|) P := by
      refine Integrable.of_bound
        (((hTm.sub measurable_const).abs.const_mul 2).aestronglyMeasurable)
        (2 * (Cuv + |c0|))
        (Filter.Eventually.of_forall fun X => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_two]
      exact mul_le_mul_of_nonneg_left
        ((abs_sub _ _).trans (add_le_add (hTbd X) le_rfl)) (by norm_num)
    have hmono := integral_mono_of_nonneg (μ := P)
      (f := fun X : EucConfig p.d N =>
        ‖(HRS.Whole.pair (HRS.Whole.empirical X) wuv - c0) *
          (ψ (featureVec φ ν X) - Eψ)‖)
      (g := fun X => 2 * |HRS.Whole.pair (HRS.Whole.empirical X) wuv - c0|)
      (Filter.Eventually.of_forall fun X => norm_nonneg _) hint
      (Filter.Eventually.of_forall fun X => by
        beta_reduce
        rw [Real.norm_eq_abs, abs_mul]
        have h3 : |ψ (featureVec φ ν X) - Eψ| ≤ 2 :=
          (abs_sub _ _).trans (by linarith [hψWb X, hEψb])
        calc |HRS.Whole.pair (HRS.Whole.empirical X) wuv - c0| *
              |ψ (featureVec φ ν X) - Eψ|
            ≤ |HRS.Whole.pair (HRS.Whole.empirical X) wuv - c0| * 2 :=
              mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
          _ = _ := by ring)
    refine hmono.trans ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hL1 (by norm_num)
  let Gm : ℕ → ℕ → ℝ := fun l q => ∫ z, S99.pd (S99.pd ψ l) q z ∂G
  have hGb : ∀ l q, |Gm l q| ≤ 1 := fun l q => by
    have hi := norm_integral_le_of_norm_le_const (μ := G)
      (f := S99.pd (S99.pd ψ l) q) (C := 1)
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]
        exact ((hψ.pd l).pd q).abs_le z)
    simpa [Gm, Real.norm_eq_abs] using hi
  have hκb : ∀ l, |fp81s21_initial_kap (R := R) u φ l| ≤
      cu * (F.K * b l) := by
    intro l
    have hpoint : ∀ x, |u x * r26t3_a R (φ l) x| ≤ cu * (F.K * b l) := by
      intro x
      have ha := HRS.MS.Tc5.tc5_cb_sup_le (F.amem l) x
      calc |u x * r26t3_a R (φ l) x| = |u x| * |r26t3_a R (φ l) x| := abs_mul _ _
        _ ≤ cu * cbNorm (fp81s21_k0 p.d) (r26t3_a R (φ l)) :=
          mul_le_mul (hubd x) ha (abs_nonneg _) (by positivity)
        _ ≤ cu * (F.K * b l) :=
          mul_le_mul_of_nonneg_left (F.anorm l) hcu0
    have hi := norm_integral_le_of_norm_le_const (μ := r26t3_mu R 0)
      (f := fun x => u x * r26t3_a R (φ l) x) (C := cu * (F.K * b l))
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        exact hpoint x)
    simpa [fp81s21_initial_kap, Real.norm_eq_abs] using hi
  have hκv : ∀ q, |fp81s21_initial_kap (R := R) v φ q| ≤
      cv * (F.K * b q) := by
    intro q
    have hpoint : ∀ x, |v x * r26t3_a R (φ q) x| ≤ cv * (F.K * b q) := by
      intro x
      have ha := HRS.MS.Tc5.tc5_cb_sup_le (F.amem q) x
      calc |v x * r26t3_a R (φ q) x| = |v x| * |r26t3_a R (φ q) x| := abs_mul _ _
        _ ≤ cv * cbNorm (fp81s21_k0 p.d) (r26t3_a R (φ q)) :=
          mul_le_mul (hvbd x) ha (abs_nonneg _) (by positivity)
        _ ≤ cv * (F.K * b q) :=
          mul_le_mul_of_nonneg_left (F.anorm q) hcv0
    have hi := norm_integral_le_of_norm_le_const (μ := r26t3_mu R 0)
      (f := fun x => v x * r26t3_a R (φ q) x) (C := cv * (F.K * b q))
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        exact hpoint x)
    simpa [fp81s21_initial_kap, Real.norm_eq_abs] using hi
  have hSlSum : ∀ l, Summable fun q =>
      fp81s21_initial_kap (R := R) v φ q * Gm l q := fun l =>
    Summable.of_norm_bounded (hbs.mul_left (cv * F.K)) (fun q => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      calc |fp81s21_initial_kap (R := R) v φ q| * |Gm l q| ≤
            (cv * (F.K * b q)) * 1 :=
          mul_le_mul (hκv q) (hGb l q) (abs_nonneg _)
            (mul_nonneg hcv0 (mul_nonneg F.hK (hb0 q)))
        _ = cv * F.K * b q := by ring)
  let Sl : ℕ → ℝ := fun l => ∑' q,
    fp81s21_initial_kap (R := R) v φ q * Gm l q
  have hSlb : ∀ l, |Sl l| ≤ cv * F.K * Sb := fun l => by
    have hg : HasSum (fun q => cv * F.K * b q) (cv * F.K * Sb) :=
      hbs.hasSum.mul_left _
    have hi := tsum_of_norm_bounded hg
      (f := fun q => fp81s21_initial_kap (R := R) v φ q * Gm l q)
      (fun q => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        calc |fp81s21_initial_kap (R := R) v φ q| * |Gm l q| ≤
              (cv * (F.K * b q)) * 1 :=
            mul_le_mul (hκv q) (hGb l q) (abs_nonneg _)
              (mul_nonneg hcv0 (mul_nonneg F.hK (hb0 q)))
          _ = cv * F.K * b q := by ring)
    simpa [Sl, Real.norm_eq_abs] using hi
  have hMeq :
      (∑' l, ∑' q, fp81s21_initial_kap (R := R) u φ l *
        fp81s21_initial_kap (R := R) v φ q * Gm l q) =
      ∑' l, fp81s21_initial_kap (R := R) u φ l * Sl l := by
    refine tsum_congr fun l => ?_
    simp only [Sl]
    rw [← tsum_mul_left]
    refine tsum_congr fun q => ?_
    ring
  let Al : ℕ → ℝ := fun l => ∫ X,
    (p.γ⁻¹ * HRS.Whole.pair (HRS.Whole.empirical X)
      (fun x => ⟪gradient χ x, gradient (φ l) x⟫)) *
      (Yv X * S99.pd ψ l (featureVec φ ν X)) ∂P
  have hDφ : ∀ m x, ‖fderiv ℝ (φ m) x‖ ≤ b m := fun m x =>
    s45_cb_deriv_le hJ1 (hφ.1 m) x
  have hAlb : ∀ l, ‖Al l‖ ≤
      (p.γ⁻¹ * Bχ * b l) * (2 * Real.sqrt N * cv) := fun l => by
    have hi := norm_integral_le_of_norm_le_const (μ := P)
      (C := (p.γ⁻¹ * Bχ * b l) * (2 * Real.sqrt N * cv))
      (f := fun X : EucConfig p.d N =>
        (p.γ⁻¹ * HRS.Whole.pair (HRS.Whole.empirical X)
          (fun x => ⟪gradient χ x, gradient (φ l) x⟫)) *
          (Yv X * S99.pd ψ l (featureVec φ ν X)))
      (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
          abs_of_nonneg (inv_nonneg.2 hγ.le)]
        have hemp : |HRS.Whole.pair (HRS.Whole.empirical X)
            (fun x => ⟪gradient χ x, gradient (φ l) x⟫)| ≤ Bχ * b l :=
          s45_abs_pair_empirical_le hN1 (fun x =>
            s99_inner_grad_le hχB.B1 (hDφ l) x) X
        have hpd : |S99.pd ψ l (featureVec φ ν X)| ≤ 1 := (hψ.pd l).abs_le _
        calc p.γ⁻¹ * |HRS.Whole.pair (HRS.Whole.empirical X)
              (fun x => ⟪gradient χ x, gradient (φ l) x⟫)| *
              (|Yv X| * |S99.pd ψ l (featureVec φ ν X)|)
            ≤ (p.γ⁻¹ * (Bχ * b l)) * ((2 * Real.sqrt N * cv) * 1) := by
              refine mul_le_mul (mul_le_mul_of_nonneg_left hemp
                (inv_nonneg.2 hγ.le))
                (mul_le_mul (hYvb X) hpd (abs_nonneg _)
                  (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hcv0))
                (by positivity)
                (mul_nonneg (inv_nonneg.2 hγ.le)
                  (mul_nonneg hBχ0 (hb0 l)))
          _ = _ := by ring)
    simpa [Al] using hi
  have hAlSum : Summable Al := Summable.of_norm_bounded
    (hbs.mul_left (p.γ⁻¹ * Bχ * (2 * Real.sqrt N * cv)))
    (fun l => (hAlb l).trans (le_of_eq (by ring)))
  have hBlSum : Summable fun l =>
      fp81s21_initial_kap (R := R) u φ l * Sl l := Summable.of_norm_bounded
    (hbs.mul_left (cu * F.K * (cv * F.K * Sb))) (fun l => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      calc |fp81s21_initial_kap (R := R) u φ l| * |Sl l| ≤
            (cu * (F.K * b l)) * (cv * F.K * Sb) :=
          mul_le_mul (hκb l) (hSlb l) (abs_nonneg _)
            (mul_nonneg hcu0 (mul_nonneg F.hK (hb0 l)))
        _ = cu * F.K * (cv * F.K * Sb) * b l := by ring)
  have hdl : ∀ l, ‖Al l - fp81s21_initial_kap (R := R) u φ l * Sl l‖ ≤
      KM * Bχ * cv * b l / Real.sqrt N := fun l => by
    rw [Real.norm_eq_abs]
    exact hMl N hN hu hv hχB hψ l
  have hS2 : |(∑' l, Al l) - ∑' l,
      fp81s21_initial_kap (R := R) u φ l * Sl l| ≤
      KM * Bχ * cv * Sb / Real.sqrt N := by
    have hg : HasSum (fun l => KM * Bχ * cv / Real.sqrt N * b l)
        (KM * Bχ * cv / Real.sqrt N * Sb) := hbs.hasSum.mul_left _
    have hi := tsum_of_norm_bounded hg
      (f := fun l => Al l - fp81s21_initial_kap (R := R) u φ l * Sl l)
      (fun l => (hdl l).trans (le_of_eq (by ring)))
    rw [hAlSum.tsum_sub hBlSum] at hi
    rw [← Real.norm_eq_abs]
    refine hi.trans (le_of_eq ?_)
    ring
  have hE1'' : (∫ X, Yu X * (Yv X * ψ (featureVec φ ν X)) ∂P) =
      RR1 + (∑' l, Al l) + TT1 := by
    rw [hE1']
  have hE0'' : (∫ X, Yu X * Yv X ∂P) = RR0 + TT0 := by
    rw [hE0']
  rw [hE1'', hE0'', hMeq]
  have hfin : (RR1 + (∑' l, Al l) + TT1) - (RR0 + TT0) * Eψ -
      ∑' l, fp81s21_initial_kap (R := R) u φ l * Sl l =
      (RR1 - RR0 * Eψ) + ((∑' l, Al l) -
        ∑' l, fp81s21_initial_kap (R := R) u φ l * Sl l) +
      (TT1 - TT0 * Eψ) := by ring
  change |(RR1 + (∑' l, Al l) + TT1) - (RR0 + TT0) * Eψ -
      ∑' l, fp81s21_initial_kap (R := R) u φ l * Sl l| ≤ K / Real.sqrt N
  rw [hfin]
  calc
    |(RR1 - RR0 * Eψ) + ((∑' l, Al l) -
        ∑' l, fp81s21_initial_kap (R := R) u φ l * Sl l) +
        (TT1 - TT0 * Eψ)| ≤
      |RR1 - RR0 * Eψ| + |(∑' l, Al l) -
        ∑' l, fp81s21_initial_kap (R := R) u φ l * Sl l| +
        |TT1 - TT0 * Eψ| := (abs_add_le _ _).trans
          (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 2 * (KB * Bχ * (KY * cv) / Real.sqrt N) +
        KM * Bχ * cv * Sb / Real.sqrt N +
        2 * (KT1 * Cuv / Real.sqrt N) :=
          add_le_add (add_le_add hA1 hS2) hA3
    _ ≤ K / Real.sqrt N := by
      have ht : KM * Bχ * cv * Sb ≤ KM * Bχ * cv * S :=
        mul_le_mul_of_nonneg_left hSbS (by positivity)
      dsimp [K]
      calc
        _ = (2 * KB * Bχ * KY * cv + KM * Bχ * cv * Sb +
            2 * KT1 * Cuv) / Real.sqrt N := by ring
        _ ≤ _ := div_le_div_of_nonneg_right (by linarith [ht]) hsqN.le

#print axioms fp81s21_initial_Mab_uniform

end HRS.Fp81.S21
end
