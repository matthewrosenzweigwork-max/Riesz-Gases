import HRS.MS.WsPrepI4
import HRS.Dynamics.InitialData

/-!
# S21T packet 5: the abstract `W_1` scheme and the i.i.d. middle leg

* `s21i_w1_scheme`: the three-leg triangle `ι_*μ → (ι e c)_*μ → (ι e c)_*γ → ι_*γ` of `s21h_w1_abstract` with an arbitrary middle bound
  `W_1(c_*μ, c_*γ) ≤ mid` and arbitrary projection tails `b`.
* `s21i_mid_iid`: for i.i.d. bounded centred summands `Y(x_i)` in a Hilbert space `E`, a centred Gaussian `γ` with the covariance of
  `Y#μ₀` and a coordinate map `c : E → ℝ^p` of norm `≤ 1`:
  `W_1(c_*(N^{-1/2}∑ Y(x_i)), c_*γ) ≤ 2ε√p + 2ε^{-2}(2+c₄/2) N^{-1/2} B³` (Gaussian smoothing + Lindeberg, `w1_iid_gauss`).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S21

open HRS.Whole HRS.MS.GenPath
open HRS (Euc cbNorm MemCb smoothDist)

variable {d : ℕ}

section Scheme

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [CompleteSpace X]

theorem s21i_w1_scheme (ι : E →L[ℝ] X) (μ γ : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure γ]
    {p : ℕ} (c : E →L[ℝ] EuclideanSpace ℝ (Fin p)) (e : EuclideanSpace ℝ (Fin p) →L[ℝ] E) (he : ‖e‖ ≤ 1)
    {b mid : ℝ≥0∞} (hμt : ∫⁻ v, ‖v - e (c v)‖ₑ ∂μ ≤ b) (hγt : ∫⁻ v, ‖v - e (c v)‖ₑ ∂γ ≤ b)
    (hmid : wassersteinE 1 (μ.map c) (γ.map c) ≤ mid) :
    wassersteinE 1 (μ.map ι) (γ.map ι) ≤ ENNReal.ofReal ‖ι‖ * (b + mid + b) := by
  have hcm : Measurable c := c.continuous.measurable
  have hem : Measurable e := e.continuous.measurable
  have hrm : Measurable (fun v => e (c v)) := hem.comp hcm
  haveI : IsProbabilityMeasure (μ.map ι) :=
    (Measure.isProbabilityMeasure_map_iff ι.continuous.measurable.aemeasurable).2 inferInstance
  haveI : IsProbabilityMeasure (γ.map ι) :=
    (Measure.isProbabilityMeasure_map_iff ι.continuous.measurable.aemeasurable).2 inferInstance
  haveI : IsProbabilityMeasure (μ.map (fun v => ι (e (c v)))) :=
    (Measure.isProbabilityMeasure_map_iff (ι.continuous.measurable.comp hrm).aemeasurable).2 inferInstance
  haveI : IsProbabilityMeasure (γ.map (fun v => ι (e (c v)))) :=
    (Measure.isProbabilityMeasure_map_iff (ι.continuous.measurable.comp hrm).aemeasurable).2 inferInstance
  haveI : IsProbabilityMeasure (μ.map c) :=
    (Measure.isProbabilityMeasure_map_iff hcm.aemeasurable).2 inferInstance
  haveI : IsProbabilityMeasure (γ.map c) :=
    (Measure.isProbabilityMeasure_map_iff hcm.aemeasurable).2 inferInstance
  have l1 := (s21h_leg_tail ι μ hrm hμt).1
  have l3 := (s21h_leg_tail ι γ hrm hγt).2
  have l2b := HRS.Main.wassersteinE_map_clm_le (ι.comp e) 1 le_rfl (μ.map c) (γ.map c)
  have eμ : (μ.map c).map (ι.comp e) = μ.map (fun v => ι (e (c v))) := by
    rw [Measure.map_map (ι.comp e).continuous.measurable hcm]; rfl
  have eγ : (γ.map c).map (ι.comp e) = γ.map (fun v => ι (e (c v))) := by
    rw [Measure.map_map (ι.comp e).continuous.measurable hcm]; rfl
  rw [eμ, eγ] at l2b
  have hn' : ‖ι.comp e‖ ≤ ‖ι‖ := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    calc ‖ι‖ * ‖e‖ ≤ ‖ι‖ * 1 := by gcongr
      _ = ‖ι‖ := mul_one _
  have tri := wassersteinE_triangle 1 le_rfl (μ.map ι) (μ.map (fun v => ι (e (c v)))) (γ.map ι)
  have tri2 := wassersteinE_triangle 1 le_rfl (μ.map (fun v => ι (e (c v))))
    (γ.map (fun v => ι (e (c v)))) (γ.map ι)
  have c2 : wassersteinE 1 (μ.map (fun v => ι (e (c v)))) (γ.map (fun v => ι (e (c v)))) ≤
      ENNReal.ofReal ‖ι‖ * mid :=
    l2b.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hn') hmid)
  calc wassersteinE 1 (μ.map ι) (γ.map ι)
      ≤ wassersteinE 1 (μ.map ι) (μ.map (fun v => ι (e (c v)))) +
        wassersteinE 1 (μ.map (fun v => ι (e (c v)))) (γ.map ι) := tri
    _ ≤ ENNReal.ofReal ‖ι‖ * b + (ENNReal.ofReal ‖ι‖ * mid + ENNReal.ofReal ‖ι‖ * b) :=
        add_le_add l1 (tri2.trans (add_le_add c2 l3))
    _ = ENNReal.ofReal ‖ι‖ * (b + mid + b) := by ring

end Scheme

section MidIid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem s21i_mid_iid {μ0 : Measure (Euc d)} [IsProbabilityMeasure μ0] (Y : Euc d → E) (hY : Measurable Y)
    {B : ℝ} (hYB : ∀ x, ‖Y x‖ ≤ B) (hmean : ∫ x, Y x ∂μ0 = 0) {N : ℕ} (hN : 1 ≤ N) (γ : Measure E)
    [IsGaussian γ] (hγ0 : ∫ z, id z ∂γ = 0)
    (hcov : ∀ x y, covarianceBilin γ x y = covarianceBilin (μ0.map Y) x y)
    {p : ℕ} (c : E →L[ℝ] EuclideanSpace ℝ (Fin p)) (hc : ‖c‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    wassersteinE 1 (((Measure.pi fun _ : Fin N => μ0).map
        (fun X : Fin N → Euc d => (Real.sqrt N)⁻¹ • ∑ i, Y (X i))).map c) (γ.map c) ≤
      ENNReal.ofReal (2 * ε * Real.sqrt p +
        2 / ε ^ 2 * ((2 + HRS.Yurinskii.c4 / 2) * ((Real.sqrt N)⁻¹ * B ^ 3))) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hYB 0)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  set ξ : Euc d → EuclideanSpace ℝ (Fin p) := fun x => (Real.sqrt N)⁻¹ • c (Y x) with hξ
  have hξm : Measurable ξ :=
    (Measurable.const_smul (c.continuous.measurable.comp hY) (Real.sqrt N)⁻¹ : Measurable fun x => (Real.sqrt N)⁻¹ • c (Y x))
  have hξB : ∀ x, ‖ξ x‖ ≤ (Real.sqrt N)⁻¹ * B := fun x => by
    rw [hξ, norm_smul, norm_inv, Real.norm_of_nonneg hsN.le]
    refine mul_le_mul_of_nonneg_left ((c.le_opNorm _).trans ?_) (by positivity)
    calc ‖c‖ * ‖Y x‖ ≤ 1 * B := mul_le_mul hc (hYB x) (norm_nonneg _) zero_le_one
      _ = B := one_mul B
  haveI hρp : IsProbabilityMeasure (μ0.map ξ) :=
    (Measure.isProbabilityMeasure_map_iff hξm.aemeasurable).2 inferInstance
  set ρ : Measure (EuclideanSpace ℝ (Fin p)) := μ0.map ξ with hρ
  have hYint : Integrable Y μ0 := Integrable.of_bound hY.aestronglyMeasurable B (ae_of_all _ hYB)
  have h0 : ∀ i, ∫ x, x i ∂ρ = 0 := by
    intro i
    rw [hρ, integral_map hξm.aemeasurable (by fun_prop : Measurable fun x : EuclideanSpace ℝ (Fin p) => x i).aestronglyMeasurable]
    set Li : E →L[ℝ] ℝ := (EuclideanSpace.proj i).comp (((Real.sqrt N)⁻¹ : ℝ) • c) with hLi
    have e1 : ∀ x, ξ x i = Li (Y x) := fun x => by simp [hLi, hξ]
    simp_rw [e1]
    rw [Li.integral_comp_comm hYint, hmean, map_zero]
  have h3 : Integrable (fun x : EuclideanSpace ℝ (Fin p) => ‖x‖ ^ 3) ρ := by
    rw [hρ]
    refine (integrable_map_measure (by fun_prop : Measurable fun x : EuclideanSpace ℝ (Fin p) => ‖x‖ ^ 3).aestronglyMeasurable
      hξm.aemeasurable).2 ?_
    refine Integrable.of_bound ((hξm.norm.pow_const 3).aestronglyMeasurable) (((Real.sqrt N)⁻¹ * B) ^ 3)
      (ae_of_all _ fun x => ?_)
    show ‖‖ξ x‖ ^ 3‖ ≤ _
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hξB x) 3
  have hw := HRS.InitialDataAux.w1_iid_gauss (N := N) ρ h0 h3 hε
  -- the particle law
  have hsm : Measurable (fun q : Fin N → EuclideanSpace ℝ (Fin p) => ∑ i, q i) :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  have hξi : Measurable (fun (X : Fin N → Euc d) (i : Fin N) => ξ (X i)) :=
    Measurable.of_eval fun i => hξm.comp (measurable_pi_apply i)
  have hSm : Measurable (fun X : Fin N → Euc d => (Real.sqrt N)⁻¹ • ∑ i, Y (X i)) :=
    (Finset.measurable_sum _ fun i _ => hY.comp (measurable_pi_apply i)).const_smul _
  have hlaw : ((Measure.pi fun _ : Fin N => μ0).map
      (fun X : Fin N → Euc d => (Real.sqrt N)⁻¹ • ∑ i, Y (X i))).map c =
      (Measure.pi fun _ : Fin N => ρ).map (fun q => ∑ i, q i) := by
    rw [Measure.map_map c.continuous.measurable hSm]
    have e : (c ∘ fun X : Fin N → Euc d => (Real.sqrt N)⁻¹ • ∑ i, Y (X i)) =
        (fun q : Fin N → EuclideanSpace ℝ (Fin p) => ∑ i, q i) ∘ (fun (X : Fin N → Euc d) (i : Fin N) => ξ (X i)) := by
      funext X
      simp [hξ, map_sum, map_smul, Finset.smul_sum]
    rw [e, ← Measure.map_map hsm hξi, Measure.pi_map_pi (fun i => hξm.aemeasurable)]
  -- the Gaussian side
  set w : Fin p → E := fun a => c.adjoint (EuclideanSpace.single a (1 : ℝ)) with hw'
  have hcw : c = s21gAw w := by
    refine ContinuousLinearMap.ext fun x => ?_
    ext a
    rw [s21gAw_apply]
    simp [hw', ContinuousLinearMap.adjoint_inner_left, EuclideanSpace.inner_single_left]
  obtain ⟨-, hG⟩ := s21g_fdd_gaussian γ hγ0 w
  have hGc : γ.map c = multivariateGaussian 0 (Matrix.of fun i j => covarianceBilin γ (w i) (w j)) :=
    (congrArg (fun f : E →L[ℝ] EuclideanSpace ℝ (Fin p) => γ.map f) hcw).trans hG
  haveI hμY : IsProbabilityMeasure (μ0.map Y) :=
    (Measure.isProbabilityMeasure_map_iff hY.aemeasurable).2 inferInstance
  have hYmem : MemLp id 2 (μ0.map Y) := by
    refine MemLp.of_bound aestronglyMeasurable_id B ?_
    have := (ae_map_iff (μ := μ0) hY.aemeasurable
      (p := fun v : E => ‖v‖ ≤ B) (isClosed_le continuous_norm continuous_const).measurableSet).2
      (ae_of_all _ hYB)
    exact this
  have hYmean : ∫ z, id z ∂(μ0.map Y) = 0 := by
    rw [integral_map hY.aemeasurable aestronglyMeasurable_id]
    exact hmean
  have hmat : (Matrix.of fun i j => covarianceBilin γ (w i) (w j)) =
      ∑ _i : Fin N, HRS.Yurinskii.momentMatrix ρ := by
    ext i j
    simp only [Matrix.of_apply, Matrix.sum_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, HRS.Yurinskii.momentMatrix]
    rw [hcov, covarianceBilin_apply hYmem, hYmean]
    simp only [id, sub_zero]
    rw [integral_map hY.aemeasurable (by fun_prop : AEStronglyMeasurable (fun z : E => inner ℝ (w i) z * inner ℝ (w j) z) (μ0.map Y)),
      hρ, integral_map hξm.aemeasurable (by fun_prop : Measurable fun x : EuclideanSpace ℝ (Fin p) => x i * x j).aestronglyMeasurable,
      ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    beta_reduce
    have e1 : inner ℝ (w i) (Y x) = c (Y x) i := by
      simp [hw', ContinuousLinearMap.adjoint_inner_left, EuclideanSpace.inner_single_left]
    have e2 : inner ℝ (w j) (Y x) = c (Y x) j := by
      simp [hw', ContinuousLinearMap.adjoint_inner_left, EuclideanSpace.inner_single_left]
    rw [e1, e2]
    simp only [hξ, PiLp.smul_apply, smul_eq_mul]
    have hr : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
    have hsN' : Real.sqrt N ≠ 0 := hsN.ne'
    calc c (Y x) i * c (Y x) j = (Real.sqrt N * Real.sqrt N) *
          ((Real.sqrt N)⁻¹ * c (Y x) i * ((Real.sqrt N)⁻¹ * c (Y x) j)) := by field_simp
      _ = _ := by rw [hr]
  rw [hlaw, hGc, hmat]
  refine hw.trans (ENNReal.ofReal_le_ofReal ?_)
  have hI : ∫ x, ‖x‖ ^ 3 ∂ρ ≤ ((Real.sqrt N)⁻¹ * B) ^ 3 := by
    rw [hρ, integral_map hξm.aemeasurable (by fun_prop : Measurable fun x : EuclideanSpace ℝ (Fin p) => ‖x‖ ^ 3).aestronglyMeasurable]
    calc ∫ x, ‖ξ x‖ ^ 3 ∂μ0 ≤ ∫ _x, ((Real.sqrt N)⁻¹ * B) ^ 3 ∂μ0 := by
          refine integral_mono_of_nonneg (ae_of_all _ fun x => by positivity) (integrable_const _)
            (ae_of_all _ fun x => pow_le_pow_left₀ (norm_nonneg _) (hξB x) 3)
      _ = ((Real.sqrt N)⁻¹ * B) ^ 3 := by simp
  have hNI : (N : ℝ) * ∫ x, ‖x‖ ^ 3 ∂ρ ≤ (Real.sqrt N)⁻¹ * B ^ 3 := by
    calc (N : ℝ) * ∫ x, ‖x‖ ^ 3 ∂ρ ≤ N * (((Real.sqrt N)⁻¹ * B) ^ 3) := mul_le_mul_of_nonneg_left hI hN0.le
      _ = (Real.sqrt N)⁻¹ * B ^ 3 := by
          have hr : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
          have hsN' : Real.sqrt N ≠ 0 := hsN.ne'
          calc (N : ℝ) * (((Real.sqrt N)⁻¹ * B) ^ 3) = (Real.sqrt N * Real.sqrt N) *
                (((Real.sqrt N)⁻¹ * B) ^ 3) := by rw [hr]
            _ = (Real.sqrt N)⁻¹ * B ^ 3 := by field_simp
  have hc4 : 0 ≤ HRS.Yurinskii.c4 := HRS.Yurinskii.c4_nonneg
  gcongr

end MidIid

end HRS.MS.S21
