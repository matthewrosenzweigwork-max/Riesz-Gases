import HRS.MS.Fp81S21InitialMoments2
import HRS.MS.S21F_S07
import HRS.MS.S21L_S08
import HRS.MS.R2ChaosAux12
import HRS.MS.SuppU1

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open S45
open HRS (Euc MemCb cbNorm)
open HRS.Whole
open HRS.MS.R26T3

/-!
The thermal `s99_Bq_bound` contract (`R2SeAux7:224`) is: for every `N ≥ 2`,
`χ : Euc d → ℝ` of class `C²`, and `B₂` with
`‖fderiv ℝ (gradient χ) x‖ ≤ B₂`, there is one nonnegative constant `K`
such that the centered statistic
`N * (pairEnergy (commutatorKernel d s (gradient χ)) - its P_N mean)`
has integrable square with second moment at most `(K * B₂)²`, and is
integrable with absolute first moment at most `K * B₂`.  In S99, this uses
the thermal `s99_mom` producers at exponents 1 and 2.  Here the actual-law
producer `r26t3_static_moments` (`S21F_S07`) supplies the centered exponent-2
bound; `s21l_s08_comm_bounded` (`S21L_S08`) supplies the kernel envelope, and
the L¹ conclusion follows generically from Cauchy–Schwarz under the actual
probability law.  No thermal-only helper is used.
-/

/-- The initial-law centered commutator energy has the thermal S99 L²/L¹
moment interface, with constants uniform in `N` and the test `χ`. -/
theorem fp81s21_initial_Bq_bound
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    {R : Trajectory p δ} (E : InitialSteinEnv R) (hγ : 0 < p.γ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 2 ≤ N → ∀ {χ : Euc p.d → ℝ}, ContDiff ℝ 2 χ →
      ∀ {B2 : ℝ}, (∀ x, ‖fderiv ℝ (gradient χ) x‖ ≤ B2) →
        Integrable (fun X : EucConfig p.d N => (fp81s21_initialBq R χ N X) ^ 2)
          (r26t3_Q R N) ∧
        ∫ X, (fp81s21_initialBq R χ N X) ^ 2 ∂(r26t3_Q R N) ≤ (K * B2) ^ 2 ∧
        Integrable (fun X : EucConfig p.d N => fp81s21_initialBq R χ N X)
          (r26t3_Q R N) ∧
        ∫ X, |fp81s21_initialBq R χ N X| ∂(r26t3_Q R N) ≤ K * B2 := by
  obtain ⟨C, hC, hF, -, -⟩ := r26t3_static_moments hδ hδh R hγ 2 (by norm_num)
  let K : ℝ := max p.s 1 * C
  have hκ : 0 ≤ max p.s 1 := by
    exact le_trans (by norm_num) (le_max_right _ _)
  have hK : 0 ≤ K := mul_nonneg hκ hC
  refine ⟨K, hK, fun N hN χ hχ B2 hB2 => ?_⟩
  have hN1 : 1 ≤ N := by omega
  haveI hQ : IsProbabilityMeasure (r26t3_Q R N) := by
    rw [← E.law_eq N]
    exact (E.static N hN).prob
  haveI hμ : IsProbabilityMeasure (r26t3_mu R 0) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu E.reference.prob
  have hB20 : 0 ≤ B2 := (norm_nonneg _).trans (hB2 0)
  let Λ : ℝ≥0 := ⟨B2, hB20⟩
  have hv1 : ContDiff ℝ 1 (gradient χ) := s45_contDiff_gradient hχ
  have hvd : Differentiable ℝ (gradient χ) := hv1.differentiable one_ne_zero
  have hLip : LipschitzWith Λ (gradient χ) :=
    lipschitzWith_of_nnnorm_fderiv_le hvd (fun x => by
      have hx := hB2 x
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact hx)
  have hker0 := s21l_s08_comm_bounded p.s p.hs0 Λ (gradient χ) hLip
  have hker : IsBoundedPairKernel p.s (max p.s 1 * B2)
      (commutatorKernel p.d p.s (gradient χ)) := by
    change IsBoundedPairKernel p.s (max p.s 1 * (Λ : ℝ))
      (commutatorKernel p.d p.s (gradient χ))
    exact hker0
  have hraw := (hF (max p.s 1 * B2)
    (commutatorKernel p.d p.s (gradient χ)) hker) Unit.unit N hN
  let f : EucConfig p.d N → ℝ := fun X => fp81s21_initialBq R χ N X
  have hfm : Measurable f := by
    dsimp [f, fp81s21_initialBq]
    exact measurable_const.mul
      ((HRS.MS.Wr.wr9_measurable_pairEnergy
        (HRS.MS.Comm.comm_meas (s := p.s) (gradient χ) hv1.continuous.measurable)).sub
        measurable_const)
  have hnorm0 : eLpNorm f 2 (r26t3_Q R N) ≤
      ENNReal.ofReal (C * (max p.s 1 * B2)) := by
    simpa [f, fp81s21_initialBq] using hraw.2
  have hKB : K * B2 = C * (max p.s 1 * B2) := by
    dsimp [K]
    ring
  have hnorm : eLpNorm f 2 (r26t3_Q R N) ≤ ENNReal.ofReal (K * B2) := by
    rw [hKB]
    exact hnorm0
  have hKBN : 0 ≤ K * B2 := mul_nonneg hK hB20
  have hmem : MemLp f 2 (r26t3_Q R N) := hnorm.trans_lt ENNReal.ofReal_lt_top
  have hsqInt : Integrable (fun X => f X ^ 2) (r26t3_Q R N) := hmem.integrable_sq
  have hsq := HRS.MS.R2Chaos.s94_integral_sq_le_of_eLpNorm
    hfm.aestronglyMeasurable hKBN hnorm
  have hmem1 : MemLp f 1 (r26t3_Q R N) := hmem.mono_exponent (by norm_num)
  have hfInt : Integrable f (r26t3_Q R N) := memLp_one_iff_integrable.mp hmem1
  have hAbsMem : MemLp (fun X => |f X|) 2 (r26t3_Q R N) := hmem.abs
  have hv := variance_nonneg (fun X => |f X|) (r26t3_Q R N)
  rw [variance_eq_sub hAbsMem] at hv
  simp only [Pi.pow_apply] at hv
  have hAbsNonneg : 0 ≤ ∫ X, |f X| ∂(r26t3_Q R N) :=
    integral_nonneg (fun X => abs_nonneg (f X))
  have hSq : (∫ X, |f X| ∂(r26t3_Q R N)) ^ 2 ≤
      ∫ X, f X ^ 2 ∂(r26t3_Q R N) := by
    have heq : ∫ X, (|f X|) ^ 2 ∂(r26t3_Q R N) =
        ∫ X, f X ^ 2 ∂(r26t3_Q R N) := by
      congr 1
      funext X
      rw [sq_abs]
    rw [← heq]
    linarith
  have hroot := Real.le_sqrt_of_sq_le hSq
  have hfirst : ∫ X, |f X| ∂(r26t3_Q R N) ≤ K * B2 := by
    calc ∫ X, |f X| ∂(r26t3_Q R N)
        ≤ Real.sqrt (∫ X, f X ^ 2 ∂(r26t3_Q R N)) := hroot
      _ ≤ Real.sqrt ((K * B2) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = K * B2 := Real.sqrt_sq hKBN
  exact ⟨by simpa [f] using hsqInt, by simpa [f] using hsq,
    by simpa [f] using hfInt, by simpa [f] using hfirst⟩

/-- The actual feature vector has a summable family of coordinate L² bounds.
The coordinates are centered at the actual first marginal, and the feature
norms give the summable envelope in the index. -/
theorem fp81s21_initial_W_coordinate_L2
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    {R : Trajectory p δ} (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {φ : ℕ → Euc p.d → ℝ}
    (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 2 ≤ N →
      Summable (fun j => Real.sqrt (∫ X,
        (SeqL2.coord (featureVec φ (r26t3_marg R N) X) j) ^ 2 ∂(r26t3_Q R N))) ∧
      ∀ j : ℕ,
        Integrable (fun X =>
          (SeqL2.coord (featureVec φ (r26t3_marg R N) X) j) ^ 2) (r26t3_Q R N) ∧
        Real.sqrt (∫ X,
          (SeqL2.coord (featureVec φ (r26t3_marg R N) X) j) ^ 2 ∂(r26t3_Q R N)) ≤
            K * cbNorm (fp81s21_J1 p.d) (φ j) := by
  obtain ⟨K, hK, hY⟩ := fp81s21_initial_Y_L2 hδ hδh E hγ
  refine ⟨K, hK, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := by omega
  haveI hQ : IsProbabilityMeasure (r26t3_Q R N) := by
    rw [← E.law_eq N]
    exact (E.static N hN).prob
  haveI hν : IsProbabilityMeasure (r26t3_marg R N) := by
    change IsProbabilityMeasure (HRS.Whole.firstMarginal (r26t3_Q R N))
    exact S99.s99_nu_prob hN1
  let b : ℕ → ℝ := fun j => cbNorm (fp81s21_J1 p.d) (φ j)
  have hb0 : ∀ j, 0 ≤ b j := fun j => by dsimp [b]; exact HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hcoord : ∀ j X,
      SeqL2.coord (featureVec φ (r26t3_marg R N) X) j =
        s45_Yi N (φ j) (HRS.Whole.pair (r26t3_marg R N) (φ j)) X := by
    intro j X
    change SeqL2.coord (SeqL2.ofSeq (fun i =>
      Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical X) (φ i) -
        HRS.Whole.pair (r26t3_marg R N) (φ i)))) j = _
    rw [s45_coord_ofSeq (s45_feature_memℓp hN1 hφ X) j]
    rfl
  have hterms : ∀ j : ℕ,
      Integrable (fun X =>
        (SeqL2.coord (featureVec φ (r26t3_marg R N) X) j) ^ 2) (r26t3_Q R N) ∧
      Real.sqrt (∫ X,
        (SeqL2.coord (featureVec φ (r26t3_marg R N) X) j) ^ 2 ∂(r26t3_Q R N)) ≤ K * b j := by
    intro j
    have hbound := hY N hN (b j) (hb0 j) (φ j) (hφ.1 j).1.continuous.measurable (by
      intro x
      dsimp [b]
      exact HRS.MS.Tc5.tc5_cb_sup_le (hφ.1 j) x)
    have hi : Integrable (fun X =>
        (SeqL2.coord (featureVec φ (r26t3_marg R N) X) j) ^ 2) (r26t3_Q R N) := by
      simpa only [hcoord] using hbound.1
    have hsecond : ∫ X,
        (SeqL2.coord (featureVec φ (r26t3_marg R N) X) j) ^ 2 ∂(r26t3_Q R N) ≤
          (K * b j) ^ 2 := by
      simpa only [hcoord] using hbound.2
    have hs : Real.sqrt (∫ X,
        (SeqL2.coord (featureVec φ (r26t3_marg R N) X) j) ^ 2 ∂(r26t3_Q R N)) ≤ K * b j := by
      apply (Real.sqrt_le_sqrt hsecond).trans_eq
      exact Real.sqrt_sq (mul_nonneg hK (hb0 j))
    exact ⟨hi, hs⟩
  have hsum : Summable (fun j => Real.sqrt (∫ X,
      (SeqL2.coord (featureVec φ (r26t3_marg R N) X) j) ^ 2 ∂(r26t3_Q R N))) := by
    refine Summable.of_nonneg_of_le (fun j => Real.sqrt_nonneg _) (fun j => ?_)
      (hφ.2.mul_left K)
    exact (hterms j).2
  exact ⟨hsum, fun j => by simpa [b] using hterms j⟩

/-- The full initial feature vector is square-integrable in `SeqL2`, with a
uniform second-moment bound obtained by summing the coordinate variances. -/
theorem fp81s21_initial_W_vector_L2
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    {R : Trajectory p δ} (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {φ : ℕ → Euc p.d → ℝ}
    (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 2 ≤ N →
      MemLp (fun X : EucConfig p.d N => featureVec φ (r26t3_marg R N) X)
        2 (r26t3_Q R N) ∧
      ∫ X, ‖featureVec φ (r26t3_marg R N) X‖ ^ 2 ∂(r26t3_Q R N) ≤
        K ^ 2 * ∑' j, (cbNorm (fp81s21_J1 p.d) (φ j)) ^ 2 := by
  obtain ⟨K, hK, hcoord⟩ := fp81s21_initial_W_coordinate_L2 hδ hδh E hγ hφ
  refine ⟨K, hK, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := by omega
  haveI hQ : IsProbabilityMeasure (r26t3_Q R N) := by
    rw [← E.law_eq N]
    exact (E.static N hN).prob
  haveI hν : IsProbabilityMeasure (r26t3_marg R N) := by
    change IsProbabilityMeasure (HRS.Whole.firstMarginal (r26t3_Q R N))
    exact S99.s99_nu_prob hN1
  let W : EucConfig p.d N → SeqL2 := fun X => featureVec φ (r26t3_marg R N) X
  let b : ℕ → ℝ := fun j => cbNorm (fp81s21_J1 p.d) (φ j)
  have hb0 : ∀ j, 0 ≤ b j := fun j => by
    dsimp [b]
    exact HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hb2 : Summable (fun j => b j ^ 2) := by
    simpa [b] using S45.s45_summable_sq hb0 hφ.2
  have hcoordN := hcoord N hN
  have hIbound : ∀ j, ∫ X, (SeqL2.coord (W X) j) ^ 2 ∂(r26t3_Q R N) ≤
      (K * b j) ^ 2 := by
    intro j
    have hs := hcoordN.2 j |>.2
    have hI0 : 0 ≤ ∫ X, (SeqL2.coord (W X) j) ^ 2 ∂(r26t3_Q R N) :=
      integral_nonneg fun X => sq_nonneg _
    have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2
    rwa [Real.sq_sqrt hI0] at hsq
  have hsumI : Summable (fun j => ∫ X, (SeqL2.coord (W X) j) ^ 2
      ∂(r26t3_Q R N)) := by
    refine Summable.of_nonneg_of_le
      (fun j => integral_nonneg fun X => sq_nonneg _) hIbound ?_
    simpa [mul_pow] using hb2.mul_left (K ^ 2)
  let c : ℕ → EucConfig p.d N → ℝ := fun j X => (SeqL2.coord (W X) j) ^ 2
  have hcm : ∀ j, Measurable (c j) := by
    intro j
    dsimp [c, W]
    exact ((S45.s45_coord_continuous j).measurable.comp
      (S45.s45_feature_measurable hN1 hφ)).pow_const 2
  have hci : ∀ j, Integrable (c j) (r26t3_Q R N) := by
    intro j
    simpa [c] using (hcoordN.2 j).1
  have hsumNorm : Summable (fun j => ∫ X, ‖c j X‖ ∂(r26t3_Q R N)) := by
    apply hsumI.congr
    intro j
    rw [integral_congr_ae]
    filter_upwards with X
    dsimp [c]
    rw [abs_of_nonneg (sq_nonneg _)]
  have htsum : ∫ X, ∑' j, c j X ∂(r26t3_Q R N) =
      ∑' j, ∫ X, c j X ∂(r26t3_Q R N) :=
    (integral_tsum_of_summable_integral_norm hci hsumNorm).symm
  have hnormsq : ∀ X, ‖W X‖ ^ 2 = ∑' j, c j X := by
    intro X
    have h := HRS.Whole.lp_two_norm_sq
      (show lp (fun _ : ℕ => ℝ) 2 from W X)
    calc ‖W X‖ ^ 2 = ‖(show lp (fun _ : ℕ => ℝ) 2 from W X)‖ ^ 2 := rfl
      _ = ∑' j, ((show lp (fun _ : ℕ => ℝ) 2 from W X) j) ^ 2 := h
      _ = ∑' j, c j X := by
        apply tsum_congr
        intro j
        rfl
  have hWm : Measurable W := S45.s45_feature_measurable hN1 hφ
  have hI : Integrable (fun X => ‖W X‖ ^ 2) (r26t3_Q R N) := by
    have hS0 : 0 ≤ HRS.Whole.featureSum (fp81s21_J1 p.d) φ :=
      tsum_nonneg hb0
    refine Integrable.of_bound ((hWm.norm.pow_const 2).aestronglyMeasurable)
      ((2 * Real.sqrt N * HRS.Whole.featureSum (fp81s21_J1 p.d) φ) ^ 2) ?_
    filter_upwards with X
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hbnd := S45.s45_featureVec_norm_le hN1 hφ (ν := r26t3_marg R N) X
    exact pow_le_pow_left₀ (norm_nonneg _) hbnd 2
  have hmem : MemLp W 2 (r26t3_Q R N) :=
    (memLp_two_iff_integrable_sq_norm hWm.aestronglyMeasurable).2 hI
  have hsumUpper : Summable (fun j => (K * b j) ^ 2) := by
    simpa [mul_pow] using hb2.mul_left (K ^ 2)
  have htotal : ∫ X, ‖W X‖ ^ 2 ∂(r26t3_Q R N) =
      ∑' j, ∫ X, (SeqL2.coord (W X) j) ^ 2 ∂(r26t3_Q R N) := by
    calc ∫ X, ‖W X‖ ^ 2 ∂(r26t3_Q R N)
        = ∫ X, ∑' j, c j X ∂(r26t3_Q R N) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall (fun X => hnormsq X)
      _ = ∑' j, ∫ X, c j X ∂(r26t3_Q R N) := htsum
      _ = ∑' j, ∫ X, (SeqL2.coord (W X) j) ^ 2 ∂(r26t3_Q R N) := by
            apply tsum_congr
            intro j
            rfl
  refine ⟨hmem, ?_⟩
  rw [htotal]
  calc ∑' j, ∫ X, (SeqL2.coord (W X) j) ^ 2 ∂(r26t3_Q R N)
      ≤ ∑' j, (K * b j) ^ 2 := Summable.tsum_le_tsum hIbound hsumI hsumUpper
    _ = K ^ 2 * ∑' j, b j ^ 2 := by
      simp_rw [mul_pow]
      rw [← tsum_mul_left]


/-- The centered empirical response coefficients have pair-index summable L²
bounds.  The centering is their actual `Q_N` expectation, represented by the
first marginal using exchangeability. -/
theorem fp81s21_initial_A_centered_L2
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    {R : Trajectory p δ} (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {φ : ℕ → Euc p.d → ℝ}
    (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 2 ≤ N →
      Summable (fun q : ℕ × ℕ => Real.sqrt (∫ X,
        (Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical X)
            (InitialFamData.wF F q.1 q.2) -
          HRS.Whole.pair (r26t3_marg R N) (InitialFamData.wF F q.1 q.2))) ^ 2
          ∂(r26t3_Q R N))) ∧
      ∀ j k : ℕ,
        (∫ X, HRS.Whole.pair (HRS.Whole.empirical X)
            (InitialFamData.wF F j k) ∂(r26t3_Q R N) =
          HRS.Whole.pair (r26t3_marg R N) (InitialFamData.wF F j k)) ∧
        Integrable (fun X => (Real.sqrt N *
          (HRS.Whole.pair (HRS.Whole.empirical X) (InitialFamData.wF F j k) -
            HRS.Whole.pair (r26t3_marg R N) (InitialFamData.wF F j k))) ^ 2)
          (r26t3_Q R N) ∧
        Real.sqrt (∫ X, (Real.sqrt N *
          (HRS.Whole.pair (HRS.Whole.empirical X) (InitialFamData.wF F j k) -
            HRS.Whole.pair (r26t3_marg R N) (InitialFamData.wF F j k))) ^ 2
          ∂(r26t3_Q R N)) ≤
            K * (cbNorm (fp81s21_J1 p.d) (φ j) *
              cbNorm (fp81s21_J1 p.d) (φ k)) := by
  obtain ⟨KY, hKY, hY⟩ := fp81s21_initial_Y_L2 hδ hδh E hγ
  let D : ℝ := ((fp81s21_k0 p.d : ℝ) + 1) *
    2 ^ fp81s21_k0 p.d * (p.γ⁻¹ * F.K)
  let K : ℝ := KY * D
  have hD : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (mul_nonneg (inv_nonneg.2 hγ.le) F.hK)
  have hK : 0 ≤ K := mul_nonneg hKY hD
  let hb : ℕ → ℝ := fun j => cbNorm (fp81s21_J1 p.d) (φ j)
  have hb0 : ∀ j, 0 ≤ hb j := fun j => by
    dsimp [hb]
    exact HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hprod : Summable (fun q : ℕ × ℕ => hb q.1 * hb q.2) := by
    have hrows : ∀ j, Summable (fun k => hb j * hb k) := fun j => by
      simpa [hb] using hφ.2.mul_left (hb j)
    have hrowsS : Summable (fun j => ∑' k, hb j * hb k) := by
      have heq : ∀ j, (∑' k, hb j * hb k) = (∑' k, hb k) * hb j := by
        intro j
        rw [tsum_mul_left]
        ring
      have hs : Summable (fun j => (∑' k, hb k) * hb j) := by
        simpa [hb] using hφ.2.mul_left (∑' k, hb k)
      exact hs.congr fun j => (heq j).symm
    change Summable (Function.uncurry (fun j k : ℕ => hb j * hb k))
    exact (summable_prod_of_nonneg (f := Function.uncurry (fun j k => hb j * hb k))
      (fun q => mul_nonneg (hb0 q.1) (hb0 q.2))).2 ⟨hrows, hrowsS⟩
  have hWsup : ∀ j k x, |InitialFamData.wF F j k x| ≤ D * (hb j * hb k) := by
    intro j k x
    have hW := fp81s21_initial_wF_cb hφ.1 F hγ j k
    calc |InitialFamData.wF F j k x| ≤
          cbNorm (fp81s21_k0 p.d) (InitialFamData.wF F j k) :=
        HRS.MS.Tc5.tc5_cb_sup_le hW.1 x
      _ ≤ D * (hb j * hb k) := by
        calc cbNorm (fp81s21_k0 p.d) (InitialFamData.wF F j k) ≤
              ((fp81s21_k0 p.d : ℝ) + 1) * 2 ^ fp81s21_k0 p.d *
                (p.γ⁻¹ * F.K * cbNorm (fp81s21_J1 p.d) (φ j)) *
                  cbNorm (fp81s21_J1 p.d) (φ k) := hW.2
          _ = D * (hb j * hb k) := by dsimp [D, hb]; ring
  refine ⟨K, hK, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := by omega
  haveI hQ : IsProbabilityMeasure (r26t3_Q R N) := by
    rw [← E.law_eq N]
    exact (E.static N hN).prob
  haveI hν : IsProbabilityMeasure (r26t3_marg R N) := by
    change IsProbabilityMeasure (HRS.Whole.firstMarginal (r26t3_Q R N))
    exact S99.s99_nu_prob hN1
  have hEx : HRS.Whole.IsExchangeable (r26t3_Q R N) := by
    rw [← E.law_eq N]
    exact (E.static N hN).exch
  have hmean : ∀ j k : ℕ,
      ∫ X, HRS.Whole.pair (HRS.Whole.empirical X) (InitialFamData.wF F j k)
          ∂(r26t3_Q R N) =
        HRS.Whole.pair (r26t3_marg R N) (InitialFamData.wF F j k) := by
    intro j k
    have hW := fp81s21_initial_wF_cb hφ.1 F hγ j k
    change ∫ X, HRS.Whole.pair (HRS.Whole.empirical X) (InitialFamData.wF F j k)
        ∂(r26t3_Q R N) = HRS.Whole.pair
          (HRS.Whole.firstMarginal (r26t3_Q R N)) (InitialFamData.wF F j k)
    exact S45.s45_E_pair_empirical hN1 hEx hW.1.1.continuous.measurable
      (hWsup j k)
  have hterms : ∀ j k : ℕ,
      Integrable (fun X => (Real.sqrt N *
        (HRS.Whole.pair (HRS.Whole.empirical X) (InitialFamData.wF F j k) -
          HRS.Whole.pair (r26t3_marg R N) (InitialFamData.wF F j k))) ^ 2)
        (r26t3_Q R N) ∧
      Real.sqrt (∫ X, (Real.sqrt N *
        (HRS.Whole.pair (HRS.Whole.empirical X) (InitialFamData.wF F j k) -
          HRS.Whole.pair (r26t3_marg R N) (InitialFamData.wF F j k))) ^ 2
        ∂(r26t3_Q R N)) ≤ K * (hb j * hb k) := by
    intro j k
    have hW := fp81s21_initial_wF_cb hφ.1 F hγ j k
    have hB0 : 0 ≤ D * (hb j * hb k) := mul_nonneg hD (mul_nonneg (hb0 j) (hb0 k))
    have hYjk := hY N hN (D * (hb j * hb k)) hB0 (InitialFamData.wF F j k)
      hW.1.1.continuous.measurable (hWsup j k)
    have hi : Integrable (fun X => (Real.sqrt N *
        (HRS.Whole.pair (HRS.Whole.empirical X) (InitialFamData.wF F j k) -
          HRS.Whole.pair (r26t3_marg R N) (InitialFamData.wF F j k))) ^ 2)
        (r26t3_Q R N) := by
      simpa [s45_Yi] using hYjk.1
    have hs0 : Real.sqrt (∫ X, (Real.sqrt N *
        (HRS.Whole.pair (HRS.Whole.empirical X) (InitialFamData.wF F j k) -
          HRS.Whole.pair (r26t3_marg R N) (InitialFamData.wF F j k))) ^ 2
        ∂(r26t3_Q R N)) ≤ KY * (D * (hb j * hb k)) := by
      calc Real.sqrt (∫ X, (Real.sqrt N *
            (HRS.Whole.pair (HRS.Whole.empirical X) (InitialFamData.wF F j k) -
              HRS.Whole.pair (r26t3_marg R N) (InitialFamData.wF F j k))) ^ 2
            ∂(r26t3_Q R N))
          ≤ Real.sqrt ((KY * (D * (hb j * hb k))) ^ 2) := by
              simpa only [s45_Yi] using Real.sqrt_le_sqrt hYjk.2
        _ = KY * (D * (hb j * hb k)) :=
              Real.sqrt_sq (mul_nonneg hKY hB0)
    have hs : Real.sqrt (∫ X, (Real.sqrt N *
        (HRS.Whole.pair (HRS.Whole.empirical X) (InitialFamData.wF F j k) -
          HRS.Whole.pair (r26t3_marg R N) (InitialFamData.wF F j k))) ^ 2
        ∂(r26t3_Q R N)) ≤ K * (hb j * hb k) := by
      dsimp [K]
      calc _ ≤ KY * (D * (hb j * hb k)) := hs0
        _ = KY * D * (hb j * hb k) := by ring
    exact ⟨hi, hs⟩
  have hsum : Summable (fun q : ℕ × ℕ => Real.sqrt (∫ X,
      (Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical X)
          (InitialFamData.wF F q.1 q.2) -
        HRS.Whole.pair (r26t3_marg R N) (InitialFamData.wF F q.1 q.2))) ^ 2
        ∂(r26t3_Q R N))) := by
    refine Summable.of_nonneg_of_le (fun q => Real.sqrt_nonneg _) (fun q => ?_)
      (hprod.mul_left K)
    exact (hterms q.1 q.2).2
  exact ⟨hsum, fun j k => ⟨hmean j k, hterms j k⟩⟩

/-- The centered initial commutator coefficients have summable L² and L¹
feature envelopes.  These are the `initialBq` coefficients themselves, with
their exact `Q_N` centering. -/
theorem fp81s21_initial_B_centered_L2
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    {R : Trajectory p δ} (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {φ : ℕ → Euc p.d → ℝ}
    (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 2 ≤ N →
      Summable (fun j => Real.sqrt (∫ X,
        (fp81s21_initialBq R (F.χ j) N X) ^ 2 ∂(r26t3_Q R N))) ∧
      Summable (fun j => ∫ X, |fp81s21_initialBq R (F.χ j) N X| ∂(r26t3_Q R N)) ∧
      ∀ j : ℕ,
        Integrable (fun X => (fp81s21_initialBq R (F.χ j) N X) ^ 2)
          (r26t3_Q R N) ∧
        Real.sqrt (∫ X,
          (fp81s21_initialBq R (F.χ j) N X) ^ 2 ∂(r26t3_Q R N)) ≤
            K * cbNorm (fp81s21_J1 p.d) (φ j) ∧
        Integrable (fun X => fp81s21_initialBq R (F.χ j) N X) (r26t3_Q R N) ∧
        ∫ X, |fp81s21_initialBq R (F.χ j) N X| ∂(r26t3_Q R N) ≤
            K * cbNorm (fp81s21_J1 p.d) (φ j) := by
  obtain ⟨KB, hKB, hBq⟩ := fp81s21_initial_Bq_bound hδ hδh E hγ
  let K : ℝ := KB * F.K
  have hK : 0 ≤ K := mul_nonneg hKB F.hK
  let b : ℕ → ℝ := fun j => cbNorm (fp81s21_J1 p.d) (φ j)
  have hb0 : ∀ j, 0 ≤ b j := fun j => by
    dsimp [b]
    exact HRS.MS.Tc5.tc5_cb_nonneg _ _
  refine ⟨K, hK, fun N hN => ?_⟩
  have hterms : ∀ j : ℕ,
      Integrable (fun X => (fp81s21_initialBq R (F.χ j) N X) ^ 2)
        (r26t3_Q R N) ∧
      Real.sqrt (∫ X,
        (fp81s21_initialBq R (F.χ j) N X) ^ 2 ∂(r26t3_Q R N)) ≤ K * b j ∧
      Integrable (fun X => fp81s21_initialBq R (F.χ j) N X) (r26t3_Q R N) ∧
      ∫ X, |fp81s21_initialBq R (F.χ j) N X| ∂(r26t3_Q R N) ≤ K * b j := by
    intro j
    have hχ2 : ContDiff ℝ 2 (F.χ j) := (F.smooth j).of_le (by
      exact_mod_cast (show 2 ≤ fp81s21_k0 p.d + 1 by unfold fp81s21_k0; omega))
    have hB2 : ∀ x, ‖fderiv ℝ (gradient (F.χ j)) x‖ ≤ F.K * b j := by
      intro x
      exact (S45.s45_norm_fderiv_gradient hχ2 x).trans (F.deriv j x 1 (by
        unfold fp81s21_k0
        omega))
    have hmoment := hBq N hN (χ := F.χ j) hχ2 (B2 := F.K * b j) hB2
    have harg0 : 0 ≤ KB * (F.K * b j) :=
      mul_nonneg hKB (mul_nonneg F.hK (hb0 j))
    have hs : Real.sqrt (∫ X,
        (fp81s21_initialBq R (F.χ j) N X) ^ 2 ∂(r26t3_Q R N)) ≤ K * b j := by
      calc Real.sqrt (∫ X,
            (fp81s21_initialBq R (F.χ j) N X) ^ 2 ∂(r26t3_Q R N))
          ≤ Real.sqrt ((KB * (F.K * b j)) ^ 2) := Real.sqrt_le_sqrt hmoment.2.1
        _ = KB * (F.K * b j) := Real.sqrt_sq harg0
        _ = K * b j := by dsimp [K]; ring
    have hL1 : ∫ X, |fp81s21_initialBq R (F.χ j) N X| ∂(r26t3_Q R N) ≤ K * b j := by
      calc ∫ X, |fp81s21_initialBq R (F.χ j) N X| ∂(r26t3_Q R N)
          ≤ KB * (F.K * b j) := hmoment.2.2.2
        _ = K * b j := by dsimp [K]; ring
    exact ⟨hmoment.1, hs, hmoment.2.2.1, hL1⟩
  have hsum2 : Summable (fun j => Real.sqrt (∫ X,
      (fp81s21_initialBq R (F.χ j) N X) ^ 2 ∂(r26t3_Q R N))) := by
    refine Summable.of_nonneg_of_le (fun j => Real.sqrt_nonneg _) (fun j => ?_)
      (hφ.2.mul_left K)
    exact (hterms j).2.1
  have hsum1 : Summable (fun j => ∫ X,
      |fp81s21_initialBq R (F.χ j) N X| ∂(r26t3_Q R N)) := by
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg (fun X => abs_nonneg _))
      (fun j => ?_) (hφ.2.mul_left K)
    exact (hterms j).2.2.2
  exact ⟨hsum2, hsum1, hterms⟩

/-- Actual-law finite-rank approximation tails for pair energies, ported from
the `R2ActualFTail` field of S07.  It returns both uncentered and centered
`L^r` tails, uniformly over `N ≥ 2`. -/
theorem fp81s21_initial_F_tail
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (hγ : 0 < p.γ) (r : ℝ) (hr : 1 ≤ r)
    {B C₂ : ℝ} {h : Euc p.d → Euc p.d → ℝ}
    {hj : ℕ → Euc p.d → Euc p.d → ℝ}
    (hh : IsBoundedPairKernel p.s B h)
    (ha : IsRound2Approx p.s C₂ B (r26t3_mu R 0) h hj) :
    R2ActualFTail (fun _ : Unit => r26t3_mu R 0) r h hj
      (fun _ => r26t3_Q R) := by
  obtain ⟨C, hC, hF, hLinear, hTail⟩ :=
    r26t3_static_moments hδ hδh R hγ r hr
  exact hTail B C₂ h hj hh ha

/-!
Thermal source contract `s99_tail` (`R2SeAux29:53`): from a bounded kernel
`h`, produce an envelope constant `C₂` and finite-rank family `hj` satisfying
`IsRound2Approx`, then for every `ε > 0` obtain a feature-independent index
cutoff after which `∫ |N(F_N^{hj-h} - E F_N^{hj-h})| ≤ ε`, uniformly over
`N ≥ 2`.  The initial-law port uses the generic root approximation producer
`U1.round2_approximation_proof` and S07’s actual-law transfer.  It exports the
stronger `R2ActualFTail`: both centered and uncentered `L^r` tails, for any
finite `r ≥ 1`, uniformly over `N`.  The approximation step is generic; the
moment transfer is ported; no thermal equilibrium equation is used.
-/

/-- Produce the finite-rank approximation family and its actual-law `L^r`
tail certificate for any bounded initial-reference pair kernel. -/
theorem fp81s21_initial_F_tail_exists
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (hγ : 0 < p.γ) (r : ℝ) (hr : 1 ≤ r)
    {B : ℝ} {h : Euc p.d → Euc p.d → ℝ}
    (hh : IsBoundedPairKernel p.s B h) :
    ∃ C₂ : ℝ, ∃ hj : ℕ → Euc p.d → Euc p.d → ℝ,
      IsRound2Approx p.s C₂ B (r26t3_mu R 0) h hj ∧
      R2ActualFTail (fun _ : Unit => r26t3_mu R 0) r h hj
        (fun _ => r26t3_Q R) := by
  obtain ⟨M, L, hρ⟩ := s21f_round2Density_init hδ hδh R
  obtain ⟨C₂, hApprox⟩ := HRS.Whole.U1.round2_approximation_proof
    p.hd p.s p.hs0 p.hs
  obtain ⟨hj, ha⟩ := hApprox M L (R.ρ 0) hρ B h hh
  have ha' : IsRound2Approx p.s C₂ B (r26t3_mu R 0) h hj := by
    simpa [r26t3_mu] using ha
  exact ⟨C₂, hj, ha', fp81s21_initial_F_tail hδ hδh R hγ r hr hh ha'⟩

end HRS.Fp81.S21

end

#print axioms HRS.Fp81.S21.fp81s21_initial_Bq_bound
#print axioms HRS.Fp81.S21.fp81s21_initial_W_coordinate_L2
#print axioms HRS.Fp81.S21.fp81s21_initial_W_vector_L2
#print axioms HRS.Fp81.S21.fp81s21_initial_A_centered_L2
#print axioms HRS.Fp81.S21.fp81s21_initial_B_centered_L2
#print axioms HRS.Fp81.S21.fp81s21_initial_F_tail
#print axioms HRS.Fp81.S21.fp81s21_initial_F_tail_exists
