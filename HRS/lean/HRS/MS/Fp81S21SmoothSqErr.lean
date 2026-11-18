import HRS.MS.Fp81S21AvgOp
import HRS.MS.Fp81S21RankKernel3

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.Fp81.S21

abbrev fp81s21_SmoothUH (H : ℝ) :=
  Lp HRS.MS.R26T6.r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) H))

abbrev fp81s21_SmoothCH (H : ℝ) :=
  ContinuousMap (Icc (0 : ℝ) H) HRS.MS.R26T6.r26t6_Coeff

local instance fp81s21_smoothIntervalMeasureSpace (H : ℝ) :
    MeasureSpace (Icc (0 : ℝ) H) :=
  ⟨Measure.comap (Subtype.val : Icc (0 : ℝ) H → ℝ) volume⟩

local instance fp81s21_smoothIntervalIsFiniteMeasure (H : ℝ) :
    IsFiniteMeasure (volume : Measure (Icc (0 : ℝ) H)) := by
  refine ⟨?_⟩
  rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet, Real.volume_Icc]
  exact ENNReal.ofReal_lt_top

/-- Clamp a real time to the closed interval `[0,H]`. -/
noncomputable def fp81s21_smoothClamp (H : ℝ) (hH : 0 < H) :
    C(ℝ, Icc (0 : ℝ) H) :=
  ⟨fun t => ⟨max 0 (min H t),
      ⟨le_max_left _ _, max_le_iff.mpr ⟨hH.le, min_le_left _ _⟩⟩⟩,
    (continuous_const.max (continuous_const.min continuous_id)).subtype_mk
      (fun t => ⟨le_max_left _ _, max_le_iff.mpr ⟨hH.le, min_le_left _ _⟩⟩)⟩

theorem fp81s21_smoothClamp_apply_of_mem
    (H : ℝ) (hH : 0 < H) (t : Icc (0 : ℝ) H) :
    fp81s21_smoothClamp H hH t = t := by
  apply Subtype.ext
  simp [fp81s21_smoothClamp, max_eq_right t.property.1, min_eq_right t.property.2]

/-- The clamp sends restricted Lebesgue measure to Lebesgue measure on the subtype. -/
theorem fp81s21_smoothClamp_measurePreserving (H : ℝ) (hH : 0 < H) :
    MeasurePreserving (fp81s21_smoothClamp H hH)
      (volume.restrict (Icc (0 : ℝ) H)) volume := by
  refine ⟨(fp81s21_smoothClamp H hH).continuous.measurable, ?_⟩
  have hcoe : (volume : Measure (Icc (0 : ℝ) H)).map
      (Subtype.val : Icc (0 : ℝ) H → ℝ) = volume.restrict (Icc (0 : ℝ) H) :=
    MeasurableSet.map_coe_volume measurableSet_Icc
  rw [← hcoe, Measure.map_map (fp81s21_smoothClamp H hH).continuous.measurable
    continuous_subtype_val.measurable]
  have hcomp : (fp81s21_smoothClamp H hH) ∘ (Subtype.val : Icc (0 : ℝ) H → ℝ) = id := by
    funext t
    exact fp81s21_smoothClamp_apply_of_mem H hH t
  rw [hcomp, Measure.map_id]

/-- Put a continuous path on `[0,H]` into the L² space over the restricted measure. -/
noncomputable def fp81s21_smoothPathToL2 (H : ℝ) (hH : 0 < H) :
    fp81s21_SmoothCH H →L[ℝ] fp81s21_SmoothUH H := by
  letI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  exact (Lp.compMeasurePreservingₗᵢ (𝕜 := ℝ) (p := (2 : ℝ≥0∞))
      (fp81s21_smoothClamp H hH)
      (fp81s21_smoothClamp_measurePreserving H hH)).toContinuousLinearMap.comp
    (ContinuousMap.toLp (E := HRS.MS.R26T6.r26t6_Coeff)
      (p := (2 : ℝ≥0∞)) (μ := (volume : Measure (Icc (0 : ℝ) H))) (𝕜 := ℝ))

/-- The L² class of a continuous path has that path as its restricted representative. -/
theorem fp81s21_smoothPathToL2_coe
    (H : ℝ) (hH : 0 < H) (X : fp81s21_SmoothCH H) :
    (fp81s21_smoothPathToL2 H hH X : ℝ →ₘ[volume.restrict (Icc (0 : ℝ) H)]
      HRS.MS.R26T6.r26t6_Coeff) =ᵐ[volume.restrict (Icc (0 : ℝ) H)]
        fun t => X (fp81s21_smoothClamp H hH t) := by
  letI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  let f := ContinuousMap.toLp (E := HRS.MS.R26T6.r26t6_Coeff)
    (p := (2 : ℝ≥0∞)) (μ := (volume : Measure (Icc (0 : ℝ) H))) (𝕜 := ℝ) X
  have hcomp := Lp.coeFn_compMeasurePreserving f
    (fp81s21_smoothClamp_measurePreserving H hH)
  change (Lp.compMeasurePreserving (fp81s21_smoothClamp H hH)
      (fp81s21_smoothClamp_measurePreserving H hH) f :
        Lp HRS.MS.R26T6.r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) H))) =ᵐ[
          volume.restrict (Icc (0 : ℝ) H)] _ at hcomp
  have hcoe : ∀ᵐ y ∂(volume : Measure (Icc (0 : ℝ) H)), f y = X y :=
    ContinuousMap.coeFn_toLp (E := HRS.MS.R26T6.r26t6_Coeff)
      (p := (2 : ℝ≥0∞)) (μ := (volume : Measure (Icc (0 : ℝ) H))) (𝕜 := ℝ) X
  have hfilter : ae ((volume.restrict (Icc (0 : ℝ) H)).map
      (fp81s21_smoothClamp H hH)) = ae (volume : Measure (Icc (0 : ℝ) H)) :=
    congrArg ae (fp81s21_smoothClamp_measurePreserving H hH).map_eq
  have hcoeMap : ∀ᵐ y ∂((volume.restrict (Icc (0 : ℝ) H)).map
      (fp81s21_smoothClamp H hH)), f y = X y := hfilter.symm ▸ hcoe
  have hclass : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) H)),
      f (fp81s21_smoothClamp H hH t) = X (fp81s21_smoothClamp H hH t) :=
    (Measure.tendsto_ae_map
      (fp81s21_smoothClamp H hH).continuous.measurable.aemeasurable).eventually hcoeMap
  filter_upwards [hcomp, hclass] with t h₁ h₂
  change (fp81s21_smoothPathToL2 H hH X : ℝ →ₘ[volume.restrict (Icc (0 : ℝ) H)]
      HRS.MS.R26T6.r26t6_Coeff) t = _ at h₁
  change f (fp81s21_smoothClamp H hH t) = _ at h₂
  exact h₁.trans h₂

/-- Deterministic uniform error for clipped averaging of a Hölder path.
The clipped interval has radius at most `h_k`, which gives the constant `B*h_k^(1/8)`. -/
theorem fp81s21_avgOperator_holder_error
    (H : ℝ) (hH : 0 < H) (k : ℕ) (X : fp81s21_SmoothCH H)
    (B : ℝ) (hB : 0 ≤ B)
    (hX : ∀ s t : Icc (0 : ℝ) H,
      ‖X s - X t‖ ≤ B * |(s : ℝ) - t| ^ (1 / 8 : ℝ)) :
    ‖fp81s21_avgOperator H hH k (fp81s21_smoothPathToL2 H hH X) - X‖ ≤
      B * (fp81s21_avgHalfWidth H k) ^ (1 / 8 : ℝ) := by
  have hhalf : 0 < fp81s21_avgHalfWidth H k := by
    unfold fp81s21_avgHalfWidth
    apply div_pos hH
    exact_mod_cast (show 0 < k + 2 by omega)
  apply (ContinuousMap.norm_le _
    (mul_nonneg hB (Real.rpow_nonneg hhalf.le _))).2
  intro t
  change ‖(fp81s21_avgOperator H hH k
      (fp81s21_smoothPathToL2 H hH X)) t - X t‖ ≤ _
  let l := fp81s21_avgLeft H k (t : ℝ)
  let r := fp81s21_avgRight H k (t : ℝ)
  let I : Set ℝ := Icc l r
  have hgeom := fp81s21_avgInterval_geometry H hH k (t : ℝ) t.property
  have hIpos : 0 < r - l := by simpa [l, r] using hgeom.1
  have hIle : I ⊆ Icc (0 : ℝ) H := by simpa [I, l, r] using hgeom.2.2
  have hmass : (volume.restrict I).real Set.univ = r - l := by
    change ((volume.restrict I) Set.univ).toReal = _
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    simp [I, l, r, hIpos.le]
  have hrep := fp81s21_smoothPathToL2_coe H hH X
  have hrepI :
      (fp81s21_smoothPathToL2 H hH X : ℝ →ₘ[volume.restrict (Icc (0 : ℝ) H)]
        HRS.MS.R26T6.r26t6_Coeff) =ᵐ[volume.restrict I]
          fun x => X (fp81s21_smoothClamp H hH x) := by
    have hrestr := ae_restrict_of_ae (s := I) hrep
    have hμ : (volume.restrict (Icc (0 : ℝ) H)).restrict I = volume.restrict I := by
      exact Measure.restrict_restrict_of_subset hIle
    rw [hμ] at hrestr
    exact hrestr
  have hint := integral_congr_ae hrepI
  have hsum : (fp81s21_avgOperator H hH k
      (fp81s21_smoothPathToL2 H hH X)) t =
      (r - l)⁻¹ • ∫ x in I, X (fp81s21_smoothClamp H hH x) ∂volume := by
    rw [fp81s21_avgOperator_apply H hH k
      (fp81s21_smoothPathToL2 H hH X) t]
    change (r - l)⁻¹ • ∫ x in I,
        (fp81s21_smoothPathToL2 H hH X : ℝ →ₘ[volume.restrict (Icc (0 : ℝ) H)]
          HRS.MS.R26T6.r26t6_Coeff) x ∂volume = _
    exact congrArg (fun z => (r - l)⁻¹ • z) hint
  rw [hsum]
  have hclt : fp81s21_smoothClamp H hH (t : ℝ) = t :=
    fp81s21_smoothClamp_apply_of_mem H hH t
  have hrad : ∀ x ∈ I, |x - (t : ℝ)| ≤ fp81s21_avgHalfWidth H k := by
    intro x hx
    have hleft : (t : ℝ) - fp81s21_avgHalfWidth H k ≤ l := by
      dsimp [l, fp81s21_avgLeft]
      exact le_max_right _ _
    have hright : r ≤ (t : ℝ) + fp81s21_avgHalfWidth H k := by
      dsimp [r, fp81s21_avgRight]
      exact min_le_right _ _
    rw [abs_le]
    constructor
    · dsimp [I] at hx
      calc
        -(fp81s21_avgHalfWidth H k) = ((t : ℝ) - fp81s21_avgHalfWidth H k) - t := by ring
        _ ≤ x - t := sub_le_sub_right (le_trans hleft hx.1) _
    · dsimp [I] at hx
      linarith [hright, hx.2]
  have hpow : ∀ x ∈ I,
      |x - (t : ℝ)| ^ (1 / 8 : ℝ) ≤
        (fp81s21_avgHalfWidth H k) ^ (1 / 8 : ℝ) := by
    intro x hx
    exact Real.rpow_le_rpow (abs_nonneg _) (hrad x hx) (by norm_num)
  have hconst : 0 ≤ B * (fp81s21_avgHalfWidth H k) ^ (1 / 8 : ℝ) :=
    mul_nonneg hB (Real.rpow_nonneg hhalf.le _)
  have hdiff : ∀ x ∈ I,
      ‖X (fp81s21_smoothClamp H hH x) - X t‖ ≤
        B * (fp81s21_avgHalfWidth H k) ^ (1 / 8 : ℝ) := by
    intro x hx
    have hxI : x ∈ Icc (0 : ℝ) H := hIle hx
    have hxcl : fp81s21_smoothClamp H hH x = ⟨x, hxI⟩ := by
      apply Subtype.ext
      simp [fp81s21_smoothClamp, max_eq_right hxI.1, min_eq_right hxI.2]
    rw [hxcl]
    calc
      ‖X ⟨x, hxI⟩ - X t‖ ≤ B * |x - (t : ℝ)| ^ (1 / 8 : ℝ) := hX _ _
      _ ≤ B * (fp81s21_avgHalfWidth H k) ^ (1 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_left (hpow x hx) hB
  have hmass' : volume.real I = r - l := by
    simp [I, Real.volume_Icc, hIpos.le]
  have hXint : IntegrableOn (fun x : ℝ => X (fp81s21_smoothClamp H hH x)) I volume :=
    (X.continuous.comp (fp81s21_smoothClamp H hH).continuous).continuousOn.integrableOn_compact
      (by simpa [I] using isCompact_Icc)
  have hconstint : IntegrableOn (fun _ : ℝ => X t) I volume :=
    integrableOn_const (C := X t) (by simpa [I] using isCompact_Icc.measure_ne_top)
      enorm_ne_top
  have hsubint :
      ∫ x in I, (X (fp81s21_smoothClamp H hH x) - X t) ∂volume =
        (∫ x in I, X (fp81s21_smoothClamp H hH x) ∂volume) - (r - l) • X t := by
    calc
      ∫ x in I, (X (fp81s21_smoothClamp H hH x) - X t) ∂volume =
          (∫ x in I, X (fp81s21_smoothClamp H hH x) ∂volume) -
            (∫ x in I, X t ∂volume) := integral_sub hXint hconstint
      _ = (∫ x in I, X (fp81s21_smoothClamp H hH x) ∂volume) -
            (r - l) • X t := by rw [integral_const, hmass]
  have hnum := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := I)
    (isCompact_Icc.measure_lt_top (μ := volume)) hdiff
  rw [hsubint, hmass'] at hnum
  have hbase : ‖(r - l)⁻¹ •
      ((∫ x in I, X (fp81s21_smoothClamp H hH x) ∂volume) - (r - l) • X t)‖ ≤
      B * (fp81s21_avgHalfWidth H k) ^ (1 / 8 : ℝ) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hIpos.le)]
    calc
      (r - l)⁻¹ * ‖(∫ x in I, X (fp81s21_smoothClamp H hH x) ∂volume) -
          (r - l) • X t‖ ≤ (r - l)⁻¹ *
          (B * (fp81s21_avgHalfWidth H k) ^ (1 / 8 : ℝ) * (r - l)) :=
        mul_le_mul_of_nonneg_left hnum (inv_nonneg.mpr hIpos.le)
      _ = B * (fp81s21_avgHalfWidth H k) ^ (1 / 8 : ℝ) := by
        field_simp [ne_of_gt hIpos]
  have hdiffavg : (r - l)⁻¹ •
      ((∫ x in I, X (fp81s21_smoothClamp H hH x) ∂volume) - (r - l) • X t) =
      (r - l)⁻¹ • ∫ x in I, X (fp81s21_smoothClamp H hH x) ∂volume - X t := by
    rw [smul_sub, smul_smul]
    congr 1
    field_simp [ne_of_gt hIpos]
    simp
  change ‖(r - l)⁻¹ • ∫ x in I, X (fp81s21_smoothClamp H hH x) ∂volume - X t‖ ≤ _
  rw [← hdiffavg]
  exact hbase

/-- Mean-square smoothing error for a measurable random continuous path with an
integrable squared Hölder envelope. -/
theorem fp81s21_avgOperator_SqErr
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H D : ℝ) (hH : 0 < H) (hD : 0 ≤ D) (k : ℕ)
    (X : Ω → fp81s21_SmoothCH H) (B : Ω → ℝ)
    (hXm : Measurable X) (hBm : Measurable B)
    (hB0 : ∀ ω, 0 ≤ B ω)
    (hBint : Integrable (fun ω => B ω ^ 2) P)
    (hBD : (∫ ω, B ω ^ 2 ∂P) ≤ D)
    (hHolder : ∀ᵐ ω ∂P, ∀ s t : Icc (0 : ℝ) H,
      ‖X ω s - X ω t‖ ≤ B ω * |(s : ℝ) - t| ^ (1 / 8 : ℝ)) :
    fp81s21_SqErr P X
      (fun ω => fp81s21_avgOperator H hH k
        (fp81s21_smoothPathToL2 H hH (X ω)))
      (Real.sqrt D * (fp81s21_avgHalfWidth H k) ^ (1 / 8 : ℝ) : ℝ) := by
  let q : ℝ := (fp81s21_avgHalfWidth H k) ^ (1 / 8 : ℝ)
  have hhalf : 0 < fp81s21_avgHalfWidth H k := by
    unfold fp81s21_avgHalfWidth
    apply div_pos hH
    exact_mod_cast (show 0 < k + 2 by omega)
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact Real.rpow_nonneg (le_of_lt hhalf) _
  have hq2 : 0 ≤ q ^ 2 := sq_nonneg q
  have hDomInt : Integrable (fun ω => q ^ 2 * B ω ^ 2) P := by
    simpa [mul_comm] using hBint.const_mul (q ^ 2)
  have hAvgMeas : Measurable (fun ω => fp81s21_avgOperator H hH k
      (fp81s21_smoothPathToL2 H hH (X ω))) :=
    ((fp81s21_avgOperator H hH k).continuous.comp
      (fp81s21_smoothPathToL2 H hH).continuous).measurable.comp hXm
  have hErrMeas : Measurable (fun ω =>
      ‖X ω - fp81s21_avgOperator H hH k
        (fp81s21_smoothPathToL2 H hH (X ω))‖ ^ 2) :=
    (hXm.sub hAvgMeas).norm.pow_const 2
  have hBound : ∀ᵐ ω ∂P,
      ‖X ω - fp81s21_avgOperator H hH k
        (fp81s21_smoothPathToL2 H hH (X ω))‖ ^ 2 ≤ q ^ 2 * B ω ^ 2 := by
    filter_upwards [hHolder] with ω hω
    have hdet := fp81s21_avgOperator_holder_error H hH k (X ω) (B ω)
      (hB0 ω) (hω)
    have hnorm : ‖X ω - fp81s21_avgOperator H hH k
        (fp81s21_smoothPathToL2 H hH (X ω))‖ ≤ B ω * q := by
      rw [norm_sub_rev]
      simpa [q] using hdet
    have hsq : ‖X ω - fp81s21_avgOperator H hH k
        (fp81s21_smoothPathToL2 H hH (X ω))‖ ^ 2 ≤ (B ω * q) ^ 2 := by
      have hx := norm_nonneg (X ω - fp81s21_avgOperator H hH k
        (fp81s21_smoothPathToL2 H hH (X ω)))
      have hy := mul_nonneg (hB0 ω) hq0
      nlinarith [sq_nonneg (‖X ω - fp81s21_avgOperator H hH k
        (fp81s21_smoothPathToL2 H hH (X ω))‖ - B ω * q)]
    calc
      ‖X ω - fp81s21_avgOperator H hH k
          (fp81s21_smoothPathToL2 H hH (X ω))‖ ^ 2 ≤ (B ω * q) ^ 2 := hsq
      _ = q ^ 2 * B ω ^ 2 := by ring
  have hErrInt : Integrable (fun ω =>
      ‖X ω - fp81s21_avgOperator H hH k
        (fp81s21_smoothPathToL2 H hH (X ω))‖ ^ 2) P :=
    hDomInt.mono_nonneg hErrMeas.aestronglyMeasurable
      (ae_of_all P fun ω => sq_nonneg _ ) hBound
  change Integrable (fun ω =>
      ‖X ω - fp81s21_avgOperator H hH k
        (fp81s21_smoothPathToL2 H hH (X ω))‖ ^ 2) P ∧
    (∫ ω, ‖X ω - fp81s21_avgOperator H hH k
        (fp81s21_smoothPathToL2 H hH (X ω))‖ ^ 2 ∂P) ≤
      (Real.sqrt D * (fp81s21_avgHalfWidth H k) ^ (1 / 8 : ℝ)) ^ 2
  refine ⟨hErrInt, ?_⟩
  calc
    (∫ ω, ‖X ω - fp81s21_avgOperator H hH k
        (fp81s21_smoothPathToL2 H hH (X ω))‖ ^ 2 ∂P) ≤
      ∫ ω, q ^ 2 * B ω ^ 2 ∂P := integral_mono_ae hErrInt hDomInt hBound
    _ = q ^ 2 * (∫ ω, B ω ^ 2 ∂P) := by rw [integral_const_mul]
    _ ≤ q ^ 2 * D := mul_le_mul_of_nonneg_left hBD hq2
    _ = (Real.sqrt D * (fp81s21_avgHalfWidth H k) ^ (1 / 8 : ℝ)) ^ 2 := by
      simp only [q, mul_pow, Real.sq_sqrt hD]
      ring

/-- The shared smoothing error profile tends to zero as the averaging radius shrinks. -/
theorem fp81s21_smoothSqErrProfile_tendsto
    (H D : ℝ) (hH : 0 < H) (hD : 0 ≤ D) :
    Tendsto (fun k : ℕ => Real.sqrt D *
      (fp81s21_avgHalfWidth H k) ^ (1 / 8 : ℝ)) atTop (𝓝 0) := by
  have hden : Tendsto (fun k : ℕ => (k : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hwidth : Tendsto (fun k : ℕ => fp81s21_avgHalfWidth H k) atTop (𝓝 0) := by
    unfold fp81s21_avgHalfWidth
    exact tendsto_const_nhds.div_atTop hden
  have hpow : Tendsto (fun k : ℕ =>
      (fp81s21_avgHalfWidth H k) ^ (1 / 8 : ℝ)) atTop (𝓝 0) := by
    have hpow' := (Real.continuousAt_rpow_const 0 (1 / 8 : ℝ)
      (Or.inr (by norm_num))).tendsto.comp hwidth
    change Tendsto (fun k : ℕ =>
      (fp81s21_avgHalfWidth H k) ^ (1 / 8 : ℝ)) atTop
      (𝓝 (0 ^ (1 / 8 : ℝ))) at hpow'
    simpa using hpow'
  simpa using (tendsto_const_nhds.mul hpow)


/-- Two laws with the same envelope-energy bound share one smoothing error profile. -/
theorem fp81s21_avgOperator_SqErr_pair
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    (H D : ℝ) (hH : 0 < H) (hD : 0 ≤ D) (k : ℕ)
    (X₁ : Ω₁ → fp81s21_SmoothCH H) (B₁ : Ω₁ → ℝ)
    (hX₁ : Measurable X₁) (hB₁m : Measurable B₁)
    (hB₁0 : ∀ ω, 0 ≤ B₁ ω)
    (hB₁int : Integrable (fun ω => B₁ ω ^ 2) P₁)
    (hB₁D : (∫ ω, B₁ ω ^ 2 ∂P₁) ≤ D)
    (hHolder₁ : ∀ᵐ ω ∂P₁, ∀ s t : Icc (0 : ℝ) H,
      ‖X₁ ω s - X₁ ω t‖ ≤ B₁ ω * |(s : ℝ) - t| ^ (1 / 8 : ℝ))
    (X₂ : Ω₂ → fp81s21_SmoothCH H) (B₂ : Ω₂ → ℝ)
    (hX₂ : Measurable X₂) (hB₂m : Measurable B₂)
    (hB₂0 : ∀ ω, 0 ≤ B₂ ω)
    (hB₂int : Integrable (fun ω => B₂ ω ^ 2) P₂)
    (hB₂D : (∫ ω, B₂ ω ^ 2 ∂P₂) ≤ D)
    (hHolder₂ : ∀ᵐ ω ∂P₂, ∀ s t : Icc (0 : ℝ) H,
      ‖X₂ ω s - X₂ ω t‖ ≤ B₂ ω * |(s : ℝ) - t| ^ (1 / 8 : ℝ)) :
    fp81s21_SqErr P₁ X₁
      (fun ω => fp81s21_avgOperator H hH k
        (fp81s21_smoothPathToL2 H hH (X₁ ω)))
      (Real.sqrt D * (fp81s21_avgHalfWidth H k) ^ (1 / 8 : ℝ) : ℝ) ∧
    fp81s21_SqErr P₂ X₂
      (fun ω => fp81s21_avgOperator H hH k
        (fp81s21_smoothPathToL2 H hH (X₂ ω)))
      (Real.sqrt D * (fp81s21_avgHalfWidth H k) ^ (1 / 8 : ℝ) : ℝ) := by
  exact
    ⟨fp81s21_avgOperator_SqErr P₁ H D hH hD k X₁ B₁ hX₁ hB₁m
        hB₁0 hB₁int hB₁D hHolder₁,
      fp81s21_avgOperator_SqErr P₂ H D hH hD k X₂ B₂ hX₂ hB₂m
        hB₂0 hB₂int hB₂D hHolder₂⟩


#print axioms fp81s21_smoothClamp_apply_of_mem
#print axioms fp81s21_smoothClamp_measurePreserving
#print axioms fp81s21_smoothPathToL2_coe
#print axioms fp81s21_avgOperator_holder_error
#print axioms fp81s21_avgOperator_SqErr
#print axioms fp81s21_avgOperator_SqErr_pair
#print axioms fp81s21_smoothSqErrProfile_tendsto

end HRS.Fp81.S21
