import HRS.MS.Fp81S21GaussTimeRep3

/-! Bochner means commute with coefficient time-section classes. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

local instance fp81s21_jointT2_measSpace (H : ℝ) : MeasurableSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := borel _
local instance fp81s21_jointT2_borelSpace (H : ℝ) : BorelSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := ⟨rfl⟩

private theorem fp81s21_TimeL2Rep_product_memLp
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (q : ℝ → Ω → r26t6_Coeff) (M a H : ℝ)
    (U : Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)))
    (hq : Measurable (Function.uncurry q))
    (hcore : fp81s21_TimeL2Rep P q M a H U) :
    MemLp (fun z : ℝ × Ω => q (a + z.1) z.2) 2
      ((volume.restrict (Set.Icc (0 : ℝ) H)).prod P) := by
  let dt : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) H)
  let g : ℝ × Ω → r26t6_Coeff := fun z => q (a + z.1) z.2
  have hg : Measurable g :=
    hq.comp ((measurable_const.add measurable_fst).prodMk measurable_snd)
  have hU2 : Integrable (fun ω => ‖U ω‖ ^ 2) P :=
    (memLp_two_iff_integrable_sq_norm hcore.2.1.aestronglyMeasurable).1 hcore.2.1
  have hsections : ∀ᵐ ω ∂P, Integrable (fun t => ‖g (t, ω)‖ ^ 2) dt := by
    filter_upwards [hcore.2.2.2] with ω hω
    exact (memLp_two_iff_integrable_sq_norm
      (hg.comp (measurable_prodMk_right (y := ω))).aestronglyMeasurable).1 hω.1
  have hnormEq : ∀ᵐ ω ∂P,
      ‖U ω‖ ^ 2 = ∫ t, ‖g (t, ω)‖ ^ 2 ∂dt := by
    filter_upwards [hcore.2.2.2] with ω hω
    calc
      ‖U ω‖ ^ 2 = inner ℝ (U ω) (U ω) := (real_inner_self_eq_norm_sq _).symm
      _ = ∫ t, inner ℝ ((U ω : ℝ → r26t6_Coeff) t)
            ((U ω : ℝ → r26t6_Coeff) t) ∂dt := L2.inner_def _ _
      _ = ∫ t, ‖g (t, ω)‖ ^ 2 ∂dt := by
        apply integral_congr_ae
        filter_upwards [hω.2] with t ht
        rw [real_inner_self_eq_norm_sq, ht]
  have houter : Integrable (fun ω => ∫ t, ‖g (t, ω)‖ ^ 2 ∂dt) P :=
    hU2.congr (hnormEq.mono fun _ h => h)
  let f : Ω × ℝ → ℝ := fun z => ‖g (z.2, z.1)‖ ^ 2
  have hf : Measurable f := by
    exact (hg.comp measurable_swap).norm.pow_const 2
  have hswap : Integrable f (P.prod dt) := by
    apply (integrable_prod_iff hf.aestronglyMeasurable).2
    refine ⟨hsections, ?_⟩
    simpa [f] using houter
  have hsq : Integrable (fun z : ℝ × Ω => ‖g z‖ ^ 2) (dt.prod P) := by
    convert hswap.swap using 1
    ext z
    simp [f]
  exact (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).2 hsq

/-- The Bochner mean of a `TimeL2Rep` is represented by the pointwise
Bochner mean of its jointly measurable time section. -/
theorem fp81s21_TimeL2Rep_mean_section
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (q : ℝ → Ω → r26t6_Coeff) (M a H : ℝ)
    (U : Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)))
    (hq : Measurable (Function.uncurry q))
    (hcore : fp81s21_TimeL2Rep P q M a H U) :
    (⇑(∫ ω, U ω ∂P) : ℝ → r26t6_Coeff) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) H)]
      (fun t => ∫ ω, q (a + t) ω ∂P) := by
  let dt : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) H)
  let g : ℝ × Ω → r26t6_Coeff := fun z => q (a + z.1) z.2
  let qbar : ℝ → r26t6_Coeff := fun t => ∫ ω, g (t, ω) ∂P
  have hg : Measurable g :=
    hq.comp ((measurable_const.add measurable_fst).prodMk measurable_snd)
  have hgMem : MemLp g 2 (dt.prod P) :=
    fp81s21_TimeL2Rep_product_memLp P q M a H U hq hcore
  have hgsq : Integrable (fun z : ℝ × Ω => ‖g z‖ ^ 2) (dt.prod P) :=
    (memLp_two_iff_integrable_sq_norm hgMem.aestronglyMeasurable).1 hgMem
  have hgL1 : MemLp g 1 (dt.prod P) :=
    hgMem.mono_exponent (p := (1 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) (by norm_num)
  have hgInt : Integrable g (dt.prod P) := memLp_one_iff_integrable.mp hgL1
  have hbarInt : Integrable qbar dt := by
    exact hgInt.integral_prod_left
  have hsecMem : ∀ᵐ t ∂dt, MemLp (fun ω => g (t, ω)) 2 P := by
    filter_upwards [hgsq.prod_right_ae] with t ht
    exact (memLp_two_iff_integrable_sq_norm
      (hg.comp (measurable_prodMk_left (x := t))).aestronglyMeasurable).2 ht
  have hmeanBound : ∀ᵐ t ∂dt,
      ‖qbar t‖ ^ 2 ≤ ∫ ω, ‖g (t, ω)‖ ^ 2 ∂P := by
    filter_upwards [hsecMem] with t ht
    have htnorm : MemLp (fun ω => ‖g (t, ω)‖) (ENNReal.ofReal (2 : ℝ)) P := by
      simpa using ht.norm
    have hconst : MemLp (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) P :=
      memLp_const 1
    have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := P) Real.HolderConjugate.two_two
      (Filter.Eventually.of_forall fun ω => norm_nonneg (g (t, ω)))
      (Filter.Eventually.of_forall fun _ => (by norm_num : 0 ≤ (1 : ℝ)))
      htnorm hconst
    have hholder' :
        ∫ ω, ‖g (t, ω)‖ ∂P ≤ Real.sqrt (∫ ω, ‖g (t, ω)‖ ^ 2 ∂P) := by
      simpa [Real.sqrt_eq_rpow, Real.rpow_two] using hholder
    have hA : 0 ≤ ∫ ω, ‖g (t, ω)‖ ^ 2 ∂P :=
      integral_nonneg (fun ω => sq_nonneg ‖g (t, ω)‖)
    have hnorm : ‖qbar t‖ ≤ Real.sqrt (∫ ω, ‖g (t, ω)‖ ^ 2 ∂P) := by
      calc
        ‖qbar t‖ = ‖∫ ω, g (t, ω) ∂P‖ := rfl
        _ ≤ ∫ ω, ‖g (t, ω)‖ ∂P := norm_integral_le_integral_norm _
        _ ≤ Real.sqrt (∫ ω, ‖g (t, ω)‖ ^ 2 ∂P) := hholder'
    have hnorm_nonneg : 0 ≤ ‖qbar t‖ := norm_nonneg _
    nlinarith [Real.sq_sqrt hA,
      sq_nonneg (Real.sqrt (∫ ω, ‖g (t, ω)‖ ^ 2 ∂P) - ‖qbar t‖)]
  have hbarSqASM : AEStronglyMeasurable (fun t => ‖qbar t‖ ^ 2) dt := by
    have hn : AEStronglyMeasurable (fun t => ‖qbar t‖) dt :=
      hbarInt.norm.aestronglyMeasurable
    convert hn.mul hn using 1 <;> ext t <;> simp [pow_two]
  have hbarSq : Integrable (fun t => ‖qbar t‖ ^ 2) dt := by
    apply Integrable.mono' (hgsq.integral_prod_left) hbarSqASM
    filter_upwards [hmeanBound] with t ht
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖qbar t‖)] using ht
  have hbarMem : MemLp qbar 2 dt :=
    (memLp_two_iff_integrable_sq_norm hbarInt.aestronglyMeasurable).2 hbarSq
  have hU1 : Integrable U P :=
    memLp_one_iff_integrable.mp
      (hcore.2.1.mono_exponent (p := (1 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) (by norm_num))
  have hmean : (∫ ω, U ω ∂P) = hbarMem.toLp qbar := by
    apply ext_inner_left ℝ
    intro φ
    let fφ : ℝ × Ω → r26t6_Coeff := fun z => φ z.1
    have hφsq : Integrable (fun t => ‖φ t‖ ^ 2) dt :=
      (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable φ)).1 (Lp.memLp φ)
    have hφliftSq : Integrable (fun z : ℝ × Ω => ‖φ z.1‖ ^ 2) (dt.prod P) := by
      simpa using hφsq.comp_fst P
    have hφliftMem : MemLp fφ 2 (dt.prod P) := by
      exact (memLp_two_iff_integrable_sq_norm
        ((Lp.aestronglyMeasurable φ).comp_fst)).2 hφliftSq
    let φLp : Lp r26t6_Coeff 2 (dt.prod P) := hφliftMem.toLp fφ
    let gLp : Lp r26t6_Coeff 2 (dt.prod P) := hgMem.toLp g
    have hFbase : Integrable (fun z => inner ℝ (φLp z) (gLp z)) (dt.prod P) :=
      L2.integrable_inner φLp gLp
    have hFrep :
        (fun z : ℝ × Ω => inner ℝ (φ z.1) (g z)) =ᵐ[dt.prod P]
          (fun z => inner ℝ (φLp z) (gLp z)) := by
      filter_upwards [hφliftMem.coeFn_toLp, hgMem.coeFn_toLp] with z hφ hg'
      rw [hφ, hg']
    have hF : Integrable (fun z : ℝ × Ω => inner ℝ (φ z.1) (g z)) (dt.prod P) :=
      hFbase.congr hFrep.symm
    calc
      inner ℝ φ (∫ ω, U ω ∂P) = ∫ ω, inner ℝ φ (U ω) ∂P :=
        (integral_inner hU1 φ).symm
      _ = ∫ ω, ∫ t, inner ℝ (φ t) (g (t, ω)) ∂dt ∂P := by
        apply integral_congr_ae
        filter_upwards [hcore.2.2.2] with ω hω
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hω.2] with t ht
        rw [ht]
      _ = ∫ z, inner ℝ (φ z.1) (g z) ∂(dt.prod P) :=
        (integral_prod_symm _ hF).symm
      _ = ∫ t, ∫ ω, inner ℝ (φ t) (g (t, ω)) ∂P ∂dt :=
        integral_prod _ hF
      _ = ∫ t, inner ℝ (φ t) (qbar t) ∂dt := by
        apply integral_congr_ae
        filter_upwards [hgInt.prod_right_ae] with t ht
        exact integral_inner ht (φ t)
      _ = inner ℝ φ (hbarMem.toLp qbar) := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hbarMem.coeFn_toLp] with t ht
        rw [ht.symm]
  have hcoe := Lp.ext_iff.mp hmean
  exact hcoe.trans hbarMem.coeFn_toLp

/-- A `MomentRep` supplies the measurable field and its time-class witness;
its Bochner mean is represented by the pointwise coefficient mean. -/
theorem fp81s21_MomentRep_mean_section
    {d r : ℕ} {Pw : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (E : r26t6_WeightedChart d r Pw) (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : ℝ → Ω → (Euc d → ℝ) → ℝ)
    (q : ℝ → Ω → r26t6_Coeff) (M a H : ℝ)
    (hrep : fp81s21_MomentRep E P Q q M)
    (ha : 0 ≤ a) (hH : 0 ≤ H) :
    ∃ U : Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)),
      fp81s21_TimeL2Rep P q M a H U ∧
      (⇑(∫ ω, U ω ∂P) : ℝ → r26t6_Coeff) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) H)]
        (fun t => ∫ ω, q (a + t) ω ∂P) := by
  obtain ⟨U, hU⟩ := fp81s21_MomentRep_time_section E P Q q M a H hrep ha hH
  exact ⟨U, hU, fp81s21_TimeL2Rep_mean_section P q M a H U hrep.1 hU⟩

/-- Packet 30's canonical Gaussian time representative has the same
Bochner-mean/time-section compatibility for its selected coefficient field. -/
theorem fp81s21_gaussian_canonical_time_mean_section
    (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (result : fp81s21_gaussian_canonical_time_result p Es E)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ result.delta₀)
    (R : Trajectory p δ) (G : GaussianRealization R)
    (a : ℝ) (ha : 0 ≤ a) (H : ℝ) (hH : 0 < H) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∃ qs : ℝ → G.Ω → r26t6_Coeff,
      ∃ U : G.Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)),
        fp81s21_TimeL2Rep G.P (fp81s21_gaussian_embedFamily p Es E qs) M a H U ∧
        (⇑(∫ ω, U ω ∂G.P) : ℝ → r26t6_Coeff) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) H)]
          (fun t => ∫ ω, fp81s21_gaussian_embedFamily p Es E qs (a + t) ω ∂G.P) := by
  obtain ⟨M, hM, hrealizations⟩ := result.realizations δ hδ hδle R
  obtain ⟨qs, hpayload⟩ := hrealizations G
  obtain ⟨U, hTimeRep, _⟩ := hpayload.time_representation a ha H hH
  have hcore : fp81s21_TimeL2Rep G.P
      (fp81s21_gaussian_embedFamily p Es E qs) M a H U := by
    refine ⟨hTimeRep.1, hTimeRep.2.1, hTimeRep.2.2.1, ?_⟩
    filter_upwards [hTimeRep.2.2.2] with ω hω
    refine ⟨hω.1, ?_⟩
    filter_upwards [hω.2] with t ht
    exact ht.1
  exact ⟨M, hM, qs, U, hcore,
    fp81s21_TimeL2Rep_mean_section G.P
      (fp81s21_gaussian_embedFamily p Es E qs) M a H U
      hpayload.coefficients.weak_momentRep.1 hcore⟩

#print axioms HRS.Fp81.S21.fp81s21_TimeL2Rep_mean_section
#print axioms HRS.Fp81.S21.fp81s21_MomentRep_mean_section
#print axioms HRS.Fp81.S21.fp81s21_gaussian_canonical_time_mean_section

end HRS.Fp81.S21
