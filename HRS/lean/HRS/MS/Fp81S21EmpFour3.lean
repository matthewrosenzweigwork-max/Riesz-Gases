import HRS.MS.Fp81S21EmpFour2

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

private theorem fp81s21_empFour_norm_integral_fourth_le
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {μ : Measure α}
    [IsFiniteMeasure μ] (f : α → E) (T : ℝ) (hT : 0 ≤ T)
    (hμ : μ.real Set.univ = T) (hf : Integrable f μ)
    (hfour : Integrable (fun x => ‖f x‖ ^ 4) μ) :
    ‖∫ x, f x ∂μ‖ ^ 4 ≤ T ^ 3 * ∫ x, ‖f x‖ ^ 4 ∂μ := by
  let g : α → ℝ := fun x => ‖f x‖
  have hgmeas : AEStronglyMeasurable g μ := hf.aestronglyMeasurable.norm
  have hgMem : MemLp g (4 : ℝ≥0∞) μ := by
    apply (integrable_norm_rpow_iff hgmeas (by norm_num) (by norm_num)).1
    simpa [g] using hfour
  have hpq : (4 : ℝ).HolderConjugate (4 / 3 : ℝ) :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hgMem4 : MemLp g (ENNReal.ofReal (4 : ℝ)) μ := by simpa using hgMem
  have hOneMem : MemLp (fun _ : α => (1 : ℝ))
      (ENNReal.ofReal (4 / 3 : ℝ)) μ := memLp_const 1
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall fun x => norm_nonneg (f x))
    (Filter.Eventually.of_forall fun _ => (by norm_num : (0 : ℝ) ≤ 1))
    hgMem4 hOneMem
  have hholder' :
      (∫ x, g x ∂μ) ≤
        (∫ x, ‖f x‖ ^ 4 ∂μ) ^ (1 / (4 : ℝ)) * T ^ (3 / 4 : ℝ) := by
    simpa [g, hμ, one_div] using hholder
  have hA : 0 ≤ ∫ x, ‖f x‖ ^ 4 ∂μ :=
    integral_nonneg (fun x => by positivity)
  have hrootA : ((∫ x, ‖f x‖ ^ 4 ∂μ) ^ (1 / (4 : ℝ))) ^ 4 =
      ∫ x, ‖f x‖ ^ 4 ∂μ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hA]
    norm_num
  have hrootT : (T ^ (3 / 4 : ℝ)) ^ 4 = T ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT]
    norm_num
  have hholder4 :
      (∫ x, g x ∂μ) ^ 4 ≤ T ^ 3 * ∫ x, ‖f x‖ ^ 4 ∂μ := by
    calc
      _ ≤ ((∫ x, ‖f x‖ ^ 4 ∂μ) ^ (1 / (4 : ℝ)) * T ^ (3 / 4 : ℝ)) ^ 4 :=
        pow_le_pow_left₀ (integral_nonneg (fun x => norm_nonneg (f x))) hholder' 4
      _ = T ^ 3 * ∫ x, ‖f x‖ ^ 4 ∂μ := by
        rw [mul_pow, hrootA, hrootT]
        ring
  calc
    _ ≤ (∫ x, g x ∂μ) ^ 4 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_integral_le_integral_norm f) 4
    _ ≤ T ^ 3 * ∫ x, ‖f x‖ ^ 4 ∂μ := hholder4

private theorem fp81s21_empFour_drift_jointMeas
    {Ω : Type*} [MeasurableSpace Ω]
    (N : ℕ) (qs qB0 : ℝ → Ω → r26t6_Coeff)
    (L : ℝ → r26t6_Coeff →L[ℝ] r26t6_Coeff)
    (hqs : Measurable (Function.uncurry qs))
    (hB0 : Measurable (Function.uncurry qB0))
    (hL : Measurable (fun z : ℝ × r26t6_Coeff => L z.1 z.2)) :
    Measurable (Function.uncurry (fp81s21_empFour_drift N L qs qB0)) := by
  have hpair : Measurable (fun z : ℝ × Ω => (z.1, qs z.1 z.2)) :=
    measurable_fst.prodMk hqs
  have hLqs : Measurable (fun z : ℝ × Ω => L z.1 (qs z.1 z.2)) :=
    hL.comp hpair
  have hcconst : Continuous (fun _ : r26t6_Coeff =>
      (Real.sqrt (N : ℝ))⁻¹) := continuous_const
  have hc : Continuous (fun z : r26t6_Coeff =>
      (Real.sqrt (N : ℝ))⁻¹ • z) := hcconst.smul continuous_id
  have hB : Measurable (fun z : ℝ × Ω =>
      (Real.sqrt (N : ℝ))⁻¹ • qB0 z.1 z.2) :=
    hc.measurable.comp hB0
  convert hLqs.sub hB using 1
  funext z
  rfl

/-- Uniform fixed-time sixth moments, joint measurability of the selected fields,
and the B3 joint-measurable operator yield the fourth moment of the time-integrated
empirical drift. The time integral is over the ordered interval `[s,t]`. -/
theorem fp81s21_empFour_integrated_drift_fourth
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N : ℕ) (hN : 2 ≤ N)
    (qs qB0 : ℝ → Ω → r26t6_Coeff)
    (L : ℝ → r26t6_Coeff →L[ℝ] r26t6_Coeff)
    (M6 CL : ℝ) (hM6 : 0 ≤ M6) (hCL : 0 ≤ CL)
    (hL : ∀ u, 0 ≤ u → ‖L u‖ ≤ CL)
    (hLjoint : Measurable (fun z : ℝ × r26t6_Coeff => L z.1 z.2))
    (hqsJoint : Measurable (Function.uncurry qs))
    (hB0Joint : Measurable (Function.uncurry qB0))
    (hqs : fp81s21_Six P qs M6) (hB0 : fp81s21_Six P qB0 M6) :
    ∀ H : ℝ, 0 < H → ∀ a : ℝ, 0 ≤ a →
      ∀ s t : Icc (0 : ℝ) H, s ≤ t →
        MemLp (fun ω => ∫ v in Icc (s : ℝ) (t : ℝ),
          fp81s21_empFour_drift N L qs qB0 (a + v) ω) 4 P ∧
        (∫ ω, ‖∫ v in Icc (s : ℝ) (t : ℝ),
          fp81s21_empFour_drift N L qs qB0 (a + v) ω‖ ^ 4 ∂P) ≤
          (8 * (CL ^ 4 + 1) * (1 + M6)) * |(t : ℝ) - s| ^ 4 := by
  intro H hH a ha s t hst
  let CD : ℝ := 8 * (CL ^ 4 + 1) * (1 + M6)
  have hCD : 0 ≤ CD := by
    dsimp [CD]
    positivity
  have hDtime := fp81s21_empFour_drift_fixedTime_fourth P N hN qs qB0 L
    M6 CL hM6 hCL hL hqs hB0
  have hDjoint := fp81s21_empFour_drift_jointMeas N qs qB0 L
    hqsJoint hB0Joint hLjoint
  let μ : Measure ℝ := volume.restrict (Icc (s : ℝ) (t : ℝ))
  haveI : IsFiniteMeasure μ := by
    dsimp [μ]
    infer_instance
  have hlen : 0 ≤ (t : ℝ) - s := sub_nonneg.mpr hst
  have hμmass : μ.real Set.univ = (t : ℝ) - s := by
    simp [μ, Measure.real_def, hst]
  let shift : ℝ × Ω → ℝ × Ω := fun z => (a + z.1, z.2)
  have hshift : Measurable shift :=
    (measurable_const.add measurable_fst).prodMk measurable_snd
  let f : ℝ × Ω → r26t6_Coeff := fun z =>
    fp81s21_empFour_drift N L qs qB0 (a + z.1) z.2
  have hfmeas : Measurable f := by
    change Measurable (fun z : ℝ × Ω =>
      fp81s21_empFour_drift N L qs qB0 (a + z.1) z.2)
    exact hDjoint.comp hshift
  let g : ℝ × Ω → ℝ := fun z => ‖f z‖ ^ 4
  have hgmeas : Measurable g := (measurable_norm.pow_const 4).comp hfmeas
  have hrowBound : ∀ᵐ v ∂μ, (∫ ω, g (v, ω) ∂P) ≤ CD := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    have huv : 0 ≤ a + v := add_nonneg ha (le_trans s.property.1 hv.1)
    have hfixed := hDtime (a + v) huv
    have heq : (∫ ω, g (v, ω) ∂P) =
        ∫ ω, ‖fp81s21_empFour_drift N L qs qB0 (a + v) ω‖ ^ 4 ∂P := by
      apply integral_congr_ae
      filter_upwards [] with ω
      rfl
    rw [heq]
    exact hfixed.2
  have hrowValueInt : Integrable (fun v => ∫ ω, g (v, ω) ∂P) μ := by
    refine (integrable_const CD).mono'
      (hgmeas.aestronglyMeasurable.integral_prod_right') ?_
    filter_upwards [hrowBound] with v hv
    have hnonneg : 0 ≤ ∫ ω, g (v, ω) ∂P :=
      integral_nonneg (fun ω => by positivity)
    rw [Real.norm_of_nonneg hnonneg]
    exact hv
  have hrowNormInt : Integrable (fun v => ∫ ω, ‖g (v, ω)‖ ∂P) μ := by
    have heq : (fun v => ∫ ω, ‖g (v, ω)‖ ∂P) =ᵐ[μ]
        (fun v => ∫ ω, g (v, ω) ∂P) := by
      filter_upwards [] with v
      congr 1
      funext ω
      exact Real.norm_of_nonneg (by positivity)
    exact hrowValueInt.congr heq.symm
  have hsection : ∀ᵐ v ∂μ, Integrable (fun ω => g (v, ω)) P := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    have huv : 0 ≤ a + v := add_nonneg ha (le_trans s.property.1 hv.1)
    have hfixed := hDtime (a + v) huv
    simpa [g, f] using hfixed.1
  have hGprod : Integrable g (μ.prod P) :=
    (integrable_prod_iff hgmeas.aestronglyMeasurable).2 ⟨hsection, hrowNormInt⟩
  have hfnormfour : Integrable (fun z => ‖f z‖ ^ 4) (μ.prod P) := by
    simpa [g] using hGprod
  have hfnorm : Integrable (fun z => ‖f z‖) (μ.prod P) := by
    have hle := integrable_norm_pow_of_le hfmeas.aestronglyMeasurable
      (by norm_num : 1 ≤ 4) hfnormfour
    simpa using hle
  have hFprod : Integrable f (μ.prod P) :=
    (integrable_norm_iff hfmeas.aestronglyMeasurable).mp hfnorm
  have htimePath : ∀ᵐ ω ∂P, Integrable (fun v => f (v, ω)) μ :=
    hFprod.prod_left_ae
  have htimeFourth : ∀ᵐ ω ∂P, Integrable (fun v => g (v, ω)) μ :=
    hGprod.prod_left_ae
  have hIntAe : AEStronglyMeasurable (fun ω => ∫ v, f (v, ω) ∂μ) P :=
    hFprod.integral_prod_right.aestronglyMeasurable
  have hmomentAe : AEStronglyMeasurable
      (fun ω => ‖∫ v, f (v, ω) ∂μ‖ ^ 4) P :=
    (continuous_pow 4).comp_aestronglyMeasurable
      (continuous_norm.comp_aestronglyMeasurable hIntAe)
  have hpathBound : ∀ᵐ ω ∂P,
      ‖∫ v, f (v, ω) ∂μ‖ ^ 4 ≤
        ((t : ℝ) - s) ^ 3 * ∫ v, g (v, ω) ∂μ := by
    filter_upwards [htimePath, htimeFourth] with ω hpath hfour
    have hJ := fp81s21_empFour_norm_integral_fourth_le
      (fun v => f (v, ω)) ((t : ℝ) - s) hlen hμmass hpath (by simpa [g, f] using hfour)
    simpa [g] using hJ
  have hmomentInt : Integrable (fun ω => ‖∫ v, f (v, ω) ∂μ‖ ^ 4) P := by
    refine (hGprod.integral_prod_right.const_mul (((t : ℝ) - s) ^ 3)).mono'
      hmomentAe ?_
    filter_upwards [hpathBound] with ω hω
    have hleft : 0 ≤ ‖∫ v, f (v, ω) ∂μ‖ ^ 4 := by positivity
    have hright : 0 ≤ ((t : ℝ) - s) ^ 3 * ∫ v, g (v, ω) ∂μ :=
      mul_nonneg (by positivity) (integral_nonneg (fun v => by positivity))
    rw [Real.norm_of_nonneg hleft]
    exact hω
  have hmem : MemLp (fun ω => ∫ v, f (v, ω) ∂μ) 4 P := by
    exact (integrable_norm_rpow_iff
      (hFprod.integral_prod_right).aestronglyMeasurable (by norm_num) (by norm_num)).1
      (by simpa using hmomentInt)
  have hmomentBound :
      (∫ ω, ‖∫ v, f (v, ω) ∂μ‖ ^ 4 ∂P) ≤ CD * ((t : ℝ) - s) ^ 4 := by
    calc
      _ ≤ ∫ ω, ((t : ℝ) - s) ^ 3 * (∫ v, g (v, ω) ∂μ) ∂P :=
        integral_mono_ae hmomentInt (hGprod.integral_prod_right.const_mul (((t : ℝ) - s) ^ 3))
          hpathBound
      _ = ((t : ℝ) - s) ^ 3 *
          (∫ ω, ∫ v, g (v, ω) ∂μ ∂P) := by rw [integral_const_mul]
      _ = ((t : ℝ) - s) ^ 3 *
          (∫ v, ∫ ω, g (v, ω) ∂P ∂μ) := by
        rw [← integral_integral_swap hGprod]
      _ ≤ ((t : ℝ) - s) ^ 3 * (CD * ((t : ℝ) - s)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc
          _ ≤ ∫ v, CD ∂μ :=
            integral_mono_ae hrowValueInt (integrable_const CD) hrowBound
          _ = CD * ((t : ℝ) - s) := by
            simp [hμmass, integral_const, smul_eq_mul, mul_comm]
      _ = CD * ((t : ℝ) - s) ^ 4 := by ring
  refine ⟨?_, ?_⟩
  · simpa [μ, f] using hmem
  · simpa [μ, f, abs_of_nonneg hlen] using hmomentBound

/-- A uniform B8 assembly. The process package is explicit because the final
B6-ii vector identity and B7 martingale estimate are supplied as hypotheses;
the same selected strong representatives are retained in the conclusion. -/
theorem fp81s21_empirical_fourth_increments_uniform_from_components
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (M6 CL Cm : ℝ) (hM6 : 0 ≤ M6) (hCL : 0 ≤ CL) (hCm : 0 ≤ Cm)
    (L : ℝ → r26t6_Coeff →L[ℝ] r26t6_Coeff)
    (hL : ∀ u, 0 ≤ u → ‖L u‖ ≤ CL)
    (hLjoint : Measurable (fun z : ℝ × r26t6_Coeff => L z.1 z.2))
    (hdata : ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N,
      ∃ qs qB0 m : ℝ → A.Ω → r26t6_Coeff,
        Measurable (Function.uncurry qs) ∧
        Measurable (Function.uncurry qB0) ∧
        fp81s21_Six A.P qs M6 ∧ fp81s21_Six A.P qB0 M6 ∧
        (∀ a : ℝ, 0 ≤ a → ∀ H : ℝ, 0 < H →
          ∀ᵐ ω ∂A.P, ∀ s t : Icc (0 : ℝ) H, s ≤ t →
            fp81s21_gaussian_chartEmbed p Es E (qs (a + t) ω) -
              fp81s21_gaussian_chartEmbed p Es E (qs (a + s) ω) =
            (∫ v in Icc (s : ℝ) (t : ℝ),
              fp81s21_empFour_drift N L qs qB0 (a + v) ω) +
              (m (a + t) ω - m (a + s) ω)) ∧
        (∀ H : ℝ, 0 < H → ∀ a : ℝ, 0 ≤ a →
          ∀ s t : Icc (0 : ℝ) H,
            MemLp (fun ω => m (a + t) ω - m (a + s) ω) 4 A.P ∧
            (∫ ω, ‖m (a + t) ω - m (a + s) ω‖ ^ 4 ∂A.P) ≤
              Cm * |(t : ℝ) - s| ^ 2)) :
    ∀ H : ℝ, 0 < H → ∃ Cη : ℝ, 0 ≤ Cη ∧
      ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N,
        ∃ qs qB0 m : ℝ → A.Ω → r26t6_Coeff,
          Measurable (Function.uncurry qs) ∧
          Measurable (Function.uncurry qB0) ∧
          fp81s21_Six A.P qs M6 ∧ fp81s21_Six A.P qB0 M6 ∧
          (∀ a : ℝ, 0 ≤ a → ∀ H' : ℝ, 0 < H' →
            ∀ᵐ ω ∂A.P, ∀ s t : Icc (0 : ℝ) H', s ≤ t →
              fp81s21_gaussian_chartEmbed p Es E (qs (a + t) ω) -
                fp81s21_gaussian_chartEmbed p Es E (qs (a + s) ω) =
              (∫ v in Icc (s : ℝ) (t : ℝ),
                fp81s21_empFour_drift N L qs qB0 (a + v) ω) +
                (m (a + t) ω - m (a + s) ω)) ∧
          (∀ H' : ℝ, 0 < H' → ∀ a : ℝ, 0 ≤ a →
            ∀ s t : Icc (0 : ℝ) H',
              MemLp (fun ω => m (a + t) ω - m (a + s) ω) 4 A.P ∧
              (∫ ω, ‖m (a + t) ω - m (a + s) ω‖ ^ 4 ∂A.P) ≤
                Cm * |(t : ℝ) - s| ^ 2) ∧
          fp81s21_Inc4 A.P
            (fun u ω => fp81s21_gaussian_chartEmbed p Es E (qs u ω)) H Cη := by
  intro H hH
  let CD : ℝ := 8 * (CL ^ 4 + 1) * (1 + M6)
  let Cη : ℝ := 8 * (CD * H ^ 2 + Cm)
  have hCD : 0 ≤ CD := by dsimp [CD]; positivity
  have hCη : 0 ≤ Cη := by dsimp [Cη, CD]; positivity
  refine ⟨Cη, hCη, ?_⟩
  intro N hN A
  obtain ⟨qs, qB0, m, hqsJoint, hB0Joint, hqsSix, hB0Six, hB6ii, hB7⟩ :=
    hdata N hN A
  have hDrift : ∀ H' : ℝ, 0 < H' → ∀ a : ℝ, 0 ≤ a →
      ∀ s t : Icc (0 : ℝ) H', s ≤ t →
        MemLp (fun ω => ∫ v in Icc (s : ℝ) (t : ℝ),
          fp81s21_empFour_drift N L qs qB0 (a + v) ω) 4 A.P ∧
        (∫ ω, ‖∫ v in Icc (s : ℝ) (t : ℝ),
          fp81s21_empFour_drift N L qs qB0 (a + v) ω‖ ^ 4 ∂A.P) ≤
          CD * |(t : ℝ) - s| ^ 4 := by
    intro H' hH' a ha s t hst
    simpa [CD] using fp81s21_empFour_integrated_drift_fourth A.P N hN
      qs qB0 L M6 CL hM6 hCL hL hLjoint hqsJoint hB0Joint hqsSix hB0Six
      H' hH' a ha s t hst
  have hInc := fp81s21_empirical_fourth_increments_from_components
    p R N A Es E qs qB0 m L CD Cm hCD hCm hB6ii hDrift hB7
  have hIncH := hInc H hH
  exact ⟨qs, qB0, m, hqsJoint, hB0Joint, hqsSix, hB0Six, hB6ii, hB7,
    hIncH⟩

#print axioms HRS.Fp81.S21.fp81s21_empFour_integrated_drift_fourth
#print axioms HRS.Fp81.S21.fp81s21_empirical_fourth_increments_uniform_from_components

end HRS.Fp81.S21
