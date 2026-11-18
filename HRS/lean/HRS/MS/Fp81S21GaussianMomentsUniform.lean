import HRS.MS.Fp81S21GaussianCovPhysical
import HRS.MS.S111K4J02E
import HRS.MS.R2ChaosAux12

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.S111K2
open HRS.MS.S111K4J01

/-!
Exact target headers (the D header is a specification, not an assumed lemma).
Both use origin-zero histories; all constants precede a and G. The supplied
coefficient/source certificates refer to the selected field, not a replacement.

D:
theorem fp81s21_uniform_gaussian_D_moments (p : Parameters) :
  ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
  ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
  ∀ E : r26t6_WeightedChart p.d (r26t6_coreOrder p.d) (r26t6_coreWeight p.d),
  ∀ MB : ℝ, 0 ≤ MB →
  ∃ c K MD : ℝ, 0 < c ∧ 0 ≤ K ∧ 0 ≤ MD ∧
  ∀ a : ℝ, ∀ ha : 0 ≤ a,
    Nonempty (r26t6_IntervalOperators E (r26t3_coeff R) p.T a c K) ∧
    ∀ O : r26t6_IntervalOperators E (r26t3_coeff R) p.T a c K,
    ∀ G : GaussianRealization R, ∀ qB : ℝ → G.Ω → r26t6_Coeff,
    Measurable (Function.uncurry qB) →
    (∀ u, 0 ≤ u → MemLp (qB u) 2 G.P ∧ (∫ ω, ‖qB u ω‖ ^ 2 ∂G.P) ≤ MB) →
    ∀ ξ : ℕ → G.Ω → ℝ, ∀ hξ : IsStdGaussianSeq G.P ξ,
    (∀ u, 0 ≤ u → ∀ j, HRS.MC.E213U13.InQ2 hξ (fun ω => qB u ω j)) →
    ∀ UB : G.Ω → Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) (a + p.T))),
    fp81s21_TimeL2Rep G.P qB MB 0 (a + p.T) UB →
    MemLp (fp81s21_gaussian_Dcum O (add_nonneg ha p.hT.le) UB (a + p.T)) 3 G.P ∧
    (∫ ω, ‖fp81s21_gaussian_Dcum O (add_nonneg ha p.hT.le) UB (a + p.T) ω‖ ^ 3 ∂G.P) ≤ MD

J: the complete header is fp81s21_uniform_gaussian_J_moments below.
Binder adjustments: expose the canonical family's uniform coefficient contract;
quantify over every compatible O and history rather than reselecting either.
D keeps hcoord explicit, as in the staged quadratic lift. hB0 is needed by
Dcum_physical for physical identification, not by the norm estimate itself.
-/

local instance fp81s21_moments_U_measSpace (H : ℝ) : MeasurableSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) H))) := borel _
local instance fp81s21_moments_U_borelSpace (H : ℝ) : BorelSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) H))) := ⟨rfl⟩

/-- The exponential history has uniformly bounded time mass. -/
private theorem fp81s21_age_mass_le (c a T : ℝ) (hc : 0 < c)
    (ha : 0 ≤ a) (hT : 0 ≤ T) :
    (∫ s in Icc (0 : ℝ) (a + T), s111k2_age c a s) ≤ T + c⁻¹ := by
  have hw : Continuous (s111k2_age c a) := by
    unfold s111k2_age
    fun_prop
  let f : ℝ → ℝ := fun s => Real.exp (-c * (a - s))
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hd (s : ℝ) : HasDerivAt (fun s => c⁻¹ * f s) (f s) s := by
    have harg : HasDerivAt (fun x : ℝ => -c * (a - x)) c s := by
      convert ((hasDerivAt_const s a).sub (hasDerivAt_id s)).const_mul (-c) using 1 <;> simp
    simpa [f, mul_assoc, mul_comm, mul_left_comm, hc.ne'] using
      ((Real.hasDerivAt_exp _).comp s harg).const_mul c⁻¹
  have hpre : (∫ s in (0 : ℝ)..a, s111k2_age c a s) =
      c⁻¹ * (1 - Real.exp (-c * a)) := by
    calc
      _ = ∫ s in (0 : ℝ)..a, f s := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le ha] at hs
        simp [s111k2_age, f, max_eq_left (sub_nonneg.mpr hs.2)]
      _ = c⁻¹ * f a - c⁻¹ * f 0 :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha
          (hf.const_mul c⁻¹).continuousOn (fun s _ => hd s)
          (hf.intervalIntegrable 0 a)
      _ = _ := by simp [f]; ring
  have hpost : (∫ s in a..(a + T), s111k2_age c a s) = T := by
    calc
      _ = ∫ _s in a..(a + T), (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le (le_add_of_nonneg_right hT)] at hs
        simp [s111k2_age, max_eq_right (sub_nonpos.mpr hs.1)]
      _ = T := by simp
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (add_nonneg ha hT),
    ← intervalIntegral.integral_add_adjacent_intervals
      (hw.intervalIntegrable 0 a) (hw.intervalIntegrable a (a + T)), hpre, hpost]
  nlinarith [mul_nonneg (inv_nonneg.mpr hc.le) (Real.exp_nonneg (-c * a))]

/-- Squaring age doubles its exponential rate, including the pre-window part. -/
private theorem fp81s21_age_sq_mass_le (c a T : ℝ) (hc : 0 < c)
    (ha : 0 ≤ a) (hT : 0 ≤ T) :
    (∫ s in Icc (0 : ℝ) (a + T), s111k2_age c a s ^ 2) ≤ T + (2 * c)⁻¹ := by
  have heq : (fun s => s111k2_age c a s ^ 2) = s111k2_age (2 * c) a := by
    funext s
    simp only [s111k2_age, ← Real.exp_nat_mul]
    congr 1
    ring
  rw [heq]
  exact fp81s21_age_mass_le (2 * c) a T (by positivity) ha hT

private theorem fp81s21_history_eq_timeCoeffOf
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (q : ℝ → Ω → r26t6_Coeff) (M H : ℝ) (hH : 0 ≤ H)
    (U : Ω → Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) H)))
    (hU : fp81s21_TimeL2Rep P q M 0 H U) :
    (fun ω => fp81s21_timeL2L1 H hH (U ω)) =ᵐ[P]
      timeCoeffOf H (Function.uncurry q) := by
  filter_upwards [hU.2.2.2] with ω hω
  have hm : MemLp (fun s => q s ω) 1 (volume.restrict (Icc (0 : ℝ) H)) := by
    simpa only [zero_add] using hω.1.mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  unfold timeCoeffOf
  split
  · rename_i h
    apply Lp.ext
    have heq : ⇑(U ω) =ᵐ[volume.restrict (Icc (0 : ℝ) H)] (fun s => q s ω) := by
      simpa only [zero_add] using hω.2
    exact (fp81s21_timeL2L1_ae H hH (U ω)).trans (heq.trans h.coeFn_toLp.symm)
  · rename_i h
    exact False.elim (h hm)

/-- Weighted covariance moments for the literal selected full history. -/
private theorem fp81s21_gaussian_J_moment_bound
    {d r : ℕ} {Pw : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {E : r26t6_WeightedChart d r Pw} {C : WholeCoeff d}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (q : ℝ → Ω → r26t6_Coeff) (M a T c K : ℝ)
    (hM : 0 ≤ M) (ha : 0 ≤ a) (hT : 0 ≤ T) (hc : 0 < c) (hK : 0 ≤ K)
    (hq : Measurable (Function.uncurry q))
    (hm : ∀ s, 0 ≤ s → MemLp (q s) 2 P ∧ (∫ ω, ‖q s ω‖ ^ 2 ∂P) ≤ M)
    (O : r26t6_IntervalOperators E C T a c K)
    (U : Ω → Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) (a + T))))
    (hU : fp81s21_TimeL2Rep P q M 0 (a + T) U) :
    MemLp (fp81s21_gaussian_Jcum O (add_nonneg ha hT) U (a + T)) 2 P ∧
    (∫ ω, ‖fp81s21_gaussian_Jcum O (add_nonneg ha hT) U (a + T) ω‖ ^ 2 ∂P) ≤
      (K * |2 * C.ν| * ((T + (2 * c)⁻¹) * Real.sqrt M)) ^ 2 := by
  have hs : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) (a + T)),
      eLpNorm (q s) 2 P ≤ ENNReal.ofReal (Real.sqrt M) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    rw [(hm s hs.1).1.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    simpa [Real.sqrt_eq_rpow] using ENNReal.ofReal_le_ofReal
      (Real.sqrt_le_sqrt (hm s hs.1).2)
  have hw := age_props (u := a) hc 2
  have hraw := k4j_L2_bound P (a + T) (Function.uncurry q) hq
    (fun _ => Real.sqrt M) (integrable_const _) (fun _ _ => Real.sqrt_nonneg _) hs
    (O.covariance 0 (a + T)) (a := 0) (b := a + T) le_rfl
    (add_nonneg ha hT) le_rfl (fun s => s111k2_age c a s ^ 2)
    hw.1 hw.2.1 hw.2.2 (K * |2 * C.ν|) (mul_nonneg hK (abs_nonneg _))
    (O.covariance_norm 0 (a + T) le_rfl (add_nonneg ha hT) le_rfl)
  have heq := fp81s21_history_eq_timeCoeffOf P q M (a + T) (add_nonneg ha hT) U hU
  have hJeq : fp81s21_gaussian_Jcum O (add_nonneg ha hT) U (a + T) =ᵐ[P]
      fun ω => O.covariance 0 (a + T) (timeCoeffOf (a + T) (Function.uncurry q) ω) :=
    heq.mono fun ω hω => congrArg (O.covariance 0 (a + T)) hω
  have hbound : eLpNorm (fp81s21_gaussian_Jcum O (add_nonneg ha hT) U (a + T)) 2 P ≤
      ENNReal.ofReal (K * |2 * C.ν| * ((T + (2 * c)⁻¹) * Real.sqrt M)) := by
    rw [eLpNorm_congr_ae hJeq]
    apply hraw.trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hK (abs_nonneg _))
    rw [integral_mul_const]
    exact mul_le_mul_of_nonneg_right (fp81s21_age_sq_mass_le c a T hc ha hT)
      (Real.sqrt_nonneg M)
  have hmem : MemLp (fp81s21_gaussian_Jcum O (add_nonneg ha hT) U (a + T)) 2 P :=
    hbound.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hmem, ?_⟩
  apply HRS.MS.R2Chaos.s94_integral_sq_le_of_eLpNorm hmem.aestronglyMeasurable.norm
    (by positivity)
  rwa [eLpNorm_norm _ hmem.aestronglyMeasurable]

/-- A common covariance moment constant for every realization and every
selected coefficient field with the given uniform moment contract. In the
retained canonical family, use `(canon.payload G).coefficients.weak_momentRep`.
This contract avoids requiring a new selection of the canonical family. -/
theorem fp81s21_uniform_gaussian_J_moments (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
    ∀ E : r26t6_WeightedChart p.d (r26t6_coreOrder p.d) (r26t6_coreWeight p.d),
    ∀ MG : ℝ, 0 ≤ MG →
    ∃ c K MJ : ℝ, 0 < c ∧ 0 ≤ K ∧ 0 ≤ MJ ∧
    ∀ a : ℝ, ∀ ha : 0 ≤ a,
      Nonempty (r26t6_IntervalOperators E (r26t3_coeff R) p.T a c K) ∧
      ∀ O : r26t6_IntervalOperators E (r26t3_coeff R) p.T a c K,
      ∀ G : GaussianRealization R, ∀ qG : ℝ → G.Ω → r26t6_Coeff,
      Measurable (Function.uncurry qG) →
      (∀ u, 0 ≤ u → MemLp (qG u) 2 G.P ∧ (∫ ω, ‖qG u ω‖ ^ 2 ∂G.P) ≤ MG) →
      ∀ UG : G.Ω → Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) (a + p.T))),
      fp81s21_TimeL2Rep G.P qG MG 0 (a + p.T) UG →
      MemLp (fp81s21_gaussian_Jcum O (add_nonneg ha p.hT.le) UG (a + p.T)) 2 G.P ∧
      (∫ ω, ‖fp81s21_gaussian_Jcum O (add_nonneg ha p.hT.le) UG (a + p.T) ω‖ ^ 2 ∂G.P) ≤ MJ := by
  obtain ⟨δ0, hδ0, hhalf, hoperators⟩ := fp81s21_moving_interval_operators p
  refine ⟨δ0, hδ0, hhalf, ?_⟩
  intro δ hδ hδle R E MG hMG
  obtain ⟨c, K, hc, hK, hO⟩ := hoperators δ hδ hδle R E
  refine ⟨c, K, (K * |2 * (r26t3_coeff R).ν| *
    ((p.T + (2 * c)⁻¹) * Real.sqrt MG)) ^ 2, hc, hK, sq_nonneg _, ?_⟩
  intro a ha
  refine ⟨hO a ha, ?_⟩
  intro O G qG hqG hm UG hUG
  exact fp81s21_gaussian_J_moment_bound G.P qG MG a p.T c K hMG ha p.hT.le hc hK
    hqG hm O UG hUG

private theorem fp81s21_lintegral_cube_jensen
    (μ : Measure ℝ) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ s, f s ∂μ) ^ 3 ≤ μ univ ^ 2 * ∫⁻ s, f s ^ 3 ∂μ := by
  have hpq : (3 : ℝ).HolderConjugate (3 / 2) := by
    rw [Real.holderConjugate_iff]
    norm_num
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf.aemeasurable
    (g := fun _ => 1) measurable_const.aemeasurable
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, one_mul] at h
  have hroot3 (x : ℝ≥0∞) : (x ^ (1 / 3 : ℝ)) ^ 3 = x := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hroot2 (x : ℝ≥0∞) : (x ^ (1 / (3 / 2) : ℝ)) ^ 3 = x ^ 2 := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hpow := pow_le_pow_left' h 3
  rw [mul_pow, hroot3, hroot2] at hpow
  simpa [ENNReal.rpow_ofNat, mul_comm] using hpow

/-- The weighted drift estimate from a uniform fourth moment of the selected
forcing. The drift is written out verbatim because the two staged physical
modules cannot be imported together (their generated local instance names
collide). No replacement history or projected forcing is used. -/
private theorem fp81s21_gaussian_D_moment_bound_of_fourth
    {d r : ℕ} {Pw : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {E : r26t6_WeightedChart d r Pw} {C : WholeCoeff d}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (q : ℝ → Ω → r26t6_Coeff) (M M4 a T c K : ℝ)
    (hM4 : 0 ≤ M4) (ha : 0 ≤ a) (hT : 0 ≤ T) (hc : 0 < c) (hK : 0 ≤ K)
    (hq : Measurable (Function.uncurry q))
    (hm : ∀ s, 0 ≤ s → MemLp (q s) 4 P ∧ (∫ ω, ‖q s ω‖ ^ 4 ∂P) ≤ M4)
    (O : r26t6_IntervalOperators E C T a c K)
    (U : Ω → Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) (a + T))))
    (hU : fp81s21_TimeL2Rep P q M 0 (a + T) U) :
    let D := fun ω => O.drift 0 (a + T) (fp81s21_timeL2L1 (a + T) (add_nonneg ha hT) (U ω))
    MemLp D 3 P ∧ (∫ ω, ‖D ω‖ ^ 3 ∂P) ≤ K ^ 3 * (T + c⁻¹) ^ 3 * (1 + M4) := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (a + T))
  let w : ℝ → ℝ := s111k2_age c a
  have hqm : Measurable (fun z : ℝ × Ω => q z.1 z.2) := hq
  have hw : Continuous w := by
    change Continuous (fun s => Real.exp (-c * max (a - s) 0))
    fun_prop
  have hw0 : ∀ s, 0 ≤ w s := fun s => (fp81s21_age_bounds hc.le s).1
  let ν := μ.withDensity (fun s => ENNReal.ofReal (w s))
  have hν : ν univ ≤ ENNReal.ofReal (T + c⁻¹) := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hw.integrableOn_Ioc (ae_of_all _ hw0)]
    apply ENNReal.ofReal_le_ofReal
    simpa only [integral_Icc_eq_integral_Ioc] using fp81s21_age_mass_le c a T hc ha hT
  have hq3 : ∀ s, 0 ≤ s → (∫⁻ ω, ‖q s ω‖ₑ ^ 3 ∂P) ≤ ENNReal.ofReal (1 + M4) := by
    intro s hs
    have h4 := (hm s hs).1
    have h3 : MemLp (q s) 3 P := h4.mono_exponent (by norm_num)
    have hle : (∫ ω, ‖q s ω‖ ^ 3 ∂P) ≤ 1 + M4 := by
      calc
        _ ≤ ∫ ω, (1 : ℝ) + ‖q s ω‖ ^ 4 ∂P := by
          apply integral_mono h3.integrable_norm_pow' ((integrable_const 1).add h4.integrable_norm_pow')
          intro ω
          change ‖q s ω‖ ^ 3 ≤ 1 + ‖q s ω‖ ^ 4
          by_cases hsmall : ‖q s ω‖ ≤ 1
          · have hpow := pow_le_pow_left₀ (norm_nonneg (q s ω)) hsmall 3
            nlinarith [pow_nonneg (norm_nonneg (q s ω)) 4]
          · have hpow := mul_le_mul_of_nonneg_right (le_of_not_ge hsmall)
              (pow_nonneg (norm_nonneg (q s ω)) 3)
            nlinarith
        _ = 1 + ∫ ω, ‖q s ω‖ ^ 4 ∂P := by
          rw [integral_add (integrable_const 1) h4.integrable_norm_pow']
          simp
        _ ≤ 1 + M4 := add_le_add_right (hm s hs).2 1
    have heq : ENNReal.ofReal (∫ ω, ‖q s ω‖ ^ 3 ∂P) = ∫⁻ ω, ‖q s ω‖ₑ ^ 3 ∂P := by
      rw [ofReal_integral_eq_lintegral_ofReal h3.integrable_norm_pow' (ae_of_all _ fun _ => by positivity)]
      simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    rw [← heq]
    exact ENNReal.ofReal_le_ofReal hle
  have hs : ∀ᵐ s ∂ν, (∫⁻ ω, ‖q s ω‖ₑ ^ 3 ∂P) ≤ ENNReal.ofReal (1 + M4) := by
    apply (withDensity_absolutelyContinuous μ _).ae_le
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hq3 s hs.1.le
  let F : Ω → R2X d T := fun ω => O.drift 0 (a + T) (timeCoeffOf (a + T) (Function.uncurry q) ω)
  have hpoint (ω : Ω) : ‖F ω‖ₑ ^ 3 ≤
      ENNReal.ofReal K ^ 3 * ν univ ^ 2 * ∫⁻ s, ‖q s ω‖ₑ ^ 3 ∂ν := by
    have h := k4j_slice_bound (a + T) (Function.uncurry q) hq (O.drift 0 (a + T))
      (a := 0) (b := a + T) le_rfl le_rfl w hw0 K hK
      (O.drift_norm 0 (a + T) le_rfl (add_nonneg ha hT) le_rfl) ω
    have heq : (∫⁻ s, ‖q s ω‖ₑ ∂ν) = ∫⁻ s, ENNReal.ofReal (w s) * ‖q s ω‖ₑ ∂μ :=
      lintegral_withDensity_eq_lintegral_mul μ hw.measurable.ennreal_ofReal
        (hq.comp measurable_prodMk_right).enorm
    change ‖F ω‖ₑ ≤ ENNReal.ofReal K * ∫⁻ s, ENNReal.ofReal (w s) * ‖q s ω‖ₑ ∂μ at h
    rw [← heq] at h
    calc
      _ ≤ (ENNReal.ofReal K * ∫⁻ s, ‖q s ω‖ₑ ∂ν) ^ 3 := pow_le_pow_left' h 3
      _ ≤ ENNReal.ofReal K ^ 3 * (ν univ ^ 2 * ∫⁻ s, ‖q s ω‖ₑ ^ 3 ∂ν) := by
        rw [mul_pow]
        exact mul_le_mul' le_rfl (fp81s21_lintegral_cube_jensen ν _ (hq.comp measurable_prodMk_right).enorm)
      _ = _ := by ring
  have hlin : (∫⁻ ω, ‖F ω‖ₑ ^ 3 ∂P) ≤ ENNReal.ofReal (K ^ 3 * (T + c⁻¹) ^ 3 * (1 + M4)) := by
    calc
      _ ≤ ∫⁻ ω, ENNReal.ofReal K ^ 3 * ν univ ^ 2 * ∫⁻ s, ‖q s ω‖ₑ ^ 3 ∂ν ∂P := lintegral_mono hpoint
      _ = ENNReal.ofReal K ^ 3 * ν univ ^ 2 * ∫⁻ s, ∫⁻ ω, ‖q s ω‖ₑ ^ 3 ∂P ∂ν := by
        rw [lintegral_const_mul _ ((hqm.enorm.pow_const 3).lintegral_prod_left')]
        congr 1
        exact lintegral_lintegral_swap (μ := P) (ν := ν)
          (f := fun ω s => ‖q s ω‖ₑ ^ 3)
          ((hqm.enorm.pow_const 3).comp measurable_swap).aemeasurable
      _ ≤ ENNReal.ofReal K ^ 3 * ν univ ^ 2 * (ENNReal.ofReal (1 + M4) * ν univ) := by
        apply mul_le_mul' le_rfl
        simpa using lintegral_mono_ae hs
      _ = ENNReal.ofReal K ^ 3 * ν univ ^ 3 * ENNReal.ofReal (1 + M4) := by ring
      _ ≤ ENNReal.ofReal K ^ 3 * ENNReal.ofReal (T + c⁻¹) ^ 3 * ENNReal.ofReal (1 + M4) := by gcongr
      _ = _ := by rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
                       ENNReal.ofReal_pow hK, ENNReal.ofReal_pow (by positivity)]
  let D := fun ω => O.drift 0 (a + T) (fp81s21_timeL2L1 (a + T) (add_nonneg ha hT) (U ω))
  have hDeq : D =ᵐ[P] F :=
    (fp81s21_history_eq_timeCoeffOf P q M (a + T) (add_nonneg ha hT) U hU).mono
      fun ω hω => congrArg (O.drift 0 (a + T)) hω
  have hDm : AEStronglyMeasurable D P :=
    ((O.drift 0 (a + T)).comp (fp81s21_timeL2L1 (a + T) (add_nonneg ha hT))).continuous.comp_aestronglyMeasurable
      hU.2.1.aestronglyMeasurable
  have hDlin : (∫⁻ ω, ‖D ω‖ₑ ^ 3 ∂P) ≤ ENNReal.ofReal (K ^ 3 * (T + c⁻¹) ^ 3 * (1 + M4)) := by
    rw [lintegral_congr_ae (hDeq.mono fun ω hω => by rw [hω])]
    exact hlin
  have hDmem : MemLp D 3 P := by
    change eLpNorm D 3 P < ⊤
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hDm]
    norm_num only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (hDlin.trans_lt ENNReal.ofReal_lt_top).ne
  refine ⟨hDmem, ?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).1
  rw [ofReal_integral_eq_lintegral_ofReal hDmem.integrable_norm_pow' (ae_of_all _ fun _ => by positivity)]
  simpa only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm] using hDlin

/-- Uniform drift moments from the uniform fourth-moment conclusion of the
staged Wick coefficient theorem. Its retained-source specialization (hcoord)
remains separate; this theorem does not assume a moment bound for D itself. -/
theorem fp81s21_uniform_gaussian_D_moments_of_fourth (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
    ∀ E : r26t6_WeightedChart p.d (r26t6_coreOrder p.d) (r26t6_coreWeight p.d),
    ∀ M4 : ℝ, 0 ≤ M4 →
    ∃ c K MD : ℝ, 0 < c ∧ 0 ≤ K ∧ 0 ≤ MD ∧
    ∀ a : ℝ, ∀ ha : 0 ≤ a,
      Nonempty (r26t6_IntervalOperators E (r26t3_coeff R) p.T a c K) ∧
      ∀ O : r26t6_IntervalOperators E (r26t3_coeff R) p.T a c K,
      ∀ G : GaussianRealization R, ∀ qB : ℝ → G.Ω → r26t6_Coeff,
      Measurable (Function.uncurry qB) →
      (∀ u, 0 ≤ u → MemLp (qB u) 4 G.P ∧ (∫ ω, ‖qB u ω‖ ^ 4 ∂G.P) ≤ M4) →
      ∀ MB : ℝ, ∀ UB : G.Ω → Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) (a + p.T))),
      fp81s21_TimeL2Rep G.P qB MB 0 (a + p.T) UB →
      let D := fun ω => O.drift 0 (a + p.T) (fp81s21_timeL2L1 (a + p.T) (add_nonneg ha p.hT.le) (UB ω))
      MemLp D 3 G.P ∧ (∫ ω, ‖D ω‖ ^ 3 ∂G.P) ≤ MD := by
  obtain ⟨δ0, hδ0, hhalf, hoperators⟩ := fp81s21_moving_interval_operators p
  refine ⟨δ0, hδ0, hhalf, ?_⟩
  intro δ hδ hδle R E M4 hM4
  obtain ⟨c, K, hc, hK, hO⟩ := hoperators δ hδ hδle R E
  have hT : 0 ≤ p.T := p.hT.le
  refine ⟨c, K, K ^ 3 * (p.T + c⁻¹) ^ 3 * (1 + M4), hc, hK, by positivity, ?_⟩
  intro a ha
  refine ⟨hO a ha, ?_⟩
  intro O G qB hqB hm MB UB hUB
  exact fp81s21_gaussian_D_moment_bound_of_fourth G.P qB MB M4 a p.T c K hM4 ha p.hT.le hc hK
    hqB hm O UB hUB

/-!
Completion boundary and consumer obligations:
* J uses the selected canonical field's `weak_momentRep`, with MG = MUG.
  AvgPackage_retained's particle M2 follows H and is not used here.
* The D specification at the top is NOT yet proved by this file. The exact
  remaining specialization is the following already-staged uniform estimate:

  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P],
  ∀ (qB : ℝ → Ω → r26t6_Coeff) (MB : ℝ), 0 ≤ MB →
  ∀ (ξ : ℕ → Ω → ℝ) (hξ : IsStdGaussianSeq P ξ),
    (∀ u, 0 ≤ u → MemLp (qB u) 2 P ∧ (∫ ω, ‖qB u ω‖ ^ 2 ∂P) ≤ MB) →
    (∀ u, 0 ≤ u → ∀ j, HRS.MC.E213U13.InQ2 hξ (fun ω => qB u ω j)) →
    ∀ u, 0 ≤ u → MemLp (qB u) 4 P ∧
      (∫ ω, ‖qB u ω‖ ^ 4 ∂P) ≤ 15 * MB ^ 2

  Proof route: apply fp81s21_InQ2_coeff_fourth at u and square the second
  moment inequality; then apply the D adapter with M4 = 15 * MB ^ 2.
  Estimate: 25–40 lines including the uniform wrapper. No new analytic
  estimate is needed. GaussianQuadraticHilbert.olean is absent from the
  prescribed round48 overlay; the authorized later checks list new files
  only. VersionGTime2.olean was likewise absent (the first import error).
* D is unfolded in the proved adapter: importing both GaussianDriftPhysical
  and GaussianCovPhysical fails on a duplicate generated local instance.
  The unfolded expression is exactly the definition of gaussian_Dcum at H.
* MB in the D adapter may follow a: only its representative agreement and
  measurability are used. M4, c, K, MD precede a and G. This does not assert
  that the unweighted time-class bound is uniform in the horizon.
* Physical interpretation still uses hB0 and the staged drift chart/orbit
  certificates. Same-source chaos still uses hcoord for the actual retained
  qB/qG, including their embeddings and retained-source identification.
-/

#print axioms fp81s21_age_mass_le
#print axioms fp81s21_age_sq_mass_le
#print axioms fp81s21_gaussian_J_moment_bound
#print axioms fp81s21_uniform_gaussian_J_moments
#print axioms fp81s21_gaussian_D_moment_bound_of_fourth
#print axioms fp81s21_uniform_gaussian_D_moments_of_fourth
end HRS.Fp81.S21
