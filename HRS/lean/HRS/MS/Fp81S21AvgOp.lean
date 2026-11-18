import HRS.MS.Fp81S21TimeShift2

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace HRS.Fp81.S21

abbrev fp81s21_UH (H : ℝ) :=
  Lp HRS.MS.R26T6.r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) H))

abbrev fp81s21_CH (H : ℝ) :=
  ContinuousMap (Icc (0 : ℝ) H) HRS.MS.R26T6.r26t6_Coeff

def fp81s21_avgHalfWidth (H : ℝ) (k : ℕ) : ℝ :=
  H / ((k : ℝ) + 2)

def fp81s21_avgLeft (H : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  max 0 (t - fp81s21_avgHalfWidth H k)

def fp81s21_avgRight (H : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  min H (t + fp81s21_avgHalfWidth H k)

/-- The clipped averaging interval has positive length at least H / (k + 2). -/
theorem fp81s21_avgInterval_geometry
    (H : ℝ) (hH : 0 < H) (k : ℕ) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) H) :
    0 < fp81s21_avgRight H k t - fp81s21_avgLeft H k t ∧
      fp81s21_avgHalfWidth H k ≤
        fp81s21_avgRight H k t - fp81s21_avgLeft H k t ∧
      Icc (fp81s21_avgLeft H k t) (fp81s21_avgRight H k t) ⊆ Icc (0 : ℝ) H := by
  have hk : (1 : ℝ) ≤ (k : ℝ) + 2 := by
    exact_mod_cast (show 1 ≤ k + 2 by omega)
  have hh : 0 < fp81s21_avgHalfWidth H k := by
    unfold fp81s21_avgHalfWidth
    exact div_pos hH (by linarith)
  have hhH : fp81s21_avgHalfWidth H k ≤ H := by
    unfold fp81s21_avgHalfWidth
    rw [div_le_iff₀ (by linarith : 0 < (k : ℝ) + 2)]
    nlinarith
  have ht0 : 0 ≤ t := ht.1
  have htH : t ≤ H := ht.2
  have hlen : fp81s21_avgHalfWidth H k ≤
      fp81s21_avgRight H k t - fp81s21_avgLeft H k t := by
    by_cases hkt : fp81s21_avgHalfWidth H k ≤ t
    · have hleftEq : fp81s21_avgLeft H k t =
          t - fp81s21_avgHalfWidth H k := by
        change max 0 (t - fp81s21_avgHalfWidth H k) = _
        exact max_eq_right (sub_nonneg.mpr hkt)
      have htle : t ≤ fp81s21_avgRight H k t := by
        unfold fp81s21_avgRight
        exact le_min htH (by linarith)
      rw [hleftEq]
      linarith
    · have hleftEq : fp81s21_avgLeft H k t = 0 := by
        change max 0 (t - fp81s21_avgHalfWidth H k) = _
        apply max_eq_left
        linarith
      have hhR : fp81s21_avgHalfWidth H k ≤ fp81s21_avgRight H k t := by
        unfold fp81s21_avgRight
        exact le_min hhH (by linarith)
      rw [hleftEq]
      linarith
  have hleft : 0 ≤ fp81s21_avgLeft H k t := le_max_left _ _
  have hright : fp81s21_avgRight H k t ≤ H := min_le_left _ _
  refine ⟨lt_of_lt_of_le hh hlen, hlen, ?_⟩
  intro x hx
  exact ⟨hleft.trans hx.1, hx.2.trans hright⟩

/-- View an L² time history as a globally defined L¹ function, zero outside [0,H]. -/
noncomputable def fp81s21_avgExtendedL1 (H : ℝ) (_hH : 0 ≤ H) :
    fp81s21_UH H →L[ℝ]
      Lp HRS.MS.R26T6.r26t6_Coeff 1 (volume : Measure ℝ) :=
  (fp81s21_zeroExtendL1 HRS.MS.R26T6.r26t6_Coeff volume
    (Icc (0 : ℝ) H) measurableSet_Icc).comp
    (fp81s21_l2ToL1 HRS.MS.R26T6.r26t6_Coeff
      (volume.restrict (Icc (0 : ℝ) H)))

/-- Integrate an L¹ function over a fixed measurable interval. -/
noncomputable def fp81s21_avgSetIntegral (a b : ℝ) :
    Lp HRS.MS.R26T6.r26t6_Coeff 1 (volume : Measure ℝ) →L[ℝ]
      HRS.MS.R26T6.r26t6_Coeff := by
  letI : Fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩
  exact (MeasureTheory.L1.integralCLM
      (α := ℝ) (E := HRS.MS.R26T6.r26t6_Coeff)
      (μ := volume.restrict (Icc a b))).comp
    (LpToLpRestrictCLM ℝ HRS.MS.R26T6.r26t6_Coeff ℝ
      volume 1 (Icc a b))

/-- Evaluation of the fixed-interval integral map is the Bochner set integral. -/
theorem fp81s21_avgSetIntegral_apply (a b : ℝ)
    (g : Lp HRS.MS.R26T6.r26t6_Coeff 1 (volume : Measure ℝ)) :
    fp81s21_avgSetIntegral a b g =
      ∫ x in Icc a b, (g : ℝ →ₘ[volume] HRS.MS.R26T6.r26t6_Coeff) x ∂volume := by
  let s : Set ℝ := Icc a b
  have hgint : Integrable (fun x : ℝ =>
      (g : ℝ →ₘ[volume] HRS.MS.R26T6.r26t6_Coeff) x)
      (volume.restrict s) :=
    memLp_one_iff_integrable.mp ((Lp.memLp g).restrict s)
  have hclass : LpToLpRestrictCLM ℝ HRS.MS.R26T6.r26t6_Coeff ℝ
      volume 1 s g = hgint.toL1 (fun x : ℝ =>
        (g : ℝ →ₘ[volume] HRS.MS.R26T6.r26t6_Coeff) x) := by
    apply Lp.ext
    filter_upwards [LpToLpRestrictCLM_coeFn ℝ s g, hgint.coeFn_toL1] with x hx₁ hx₂
    exact hx₁.trans hx₂.symm
  change (MeasureTheory.L1.integralCLM
      (α := ℝ) (E := HRS.MS.R26T6.r26t6_Coeff)
      (μ := volume.restrict s))
      (LpToLpRestrictCLM ℝ HRS.MS.R26T6.r26t6_Coeff ℝ volume 1 s g) = _
  rw [← MeasureTheory.L1.integral_eq, hclass]
  exact (MeasureTheory.integral_eq _ hgint).symm

def fp81s21_avgPrimitive
    (g : Lp HRS.MS.R26T6.r26t6_Coeff 1 (volume : Measure ℝ)) (x : ℝ) :
    HRS.MS.R26T6.r26t6_Coeff :=
  ∫ s in (0 : ℝ)..x, (g : ℝ →ₘ[volume] HRS.MS.R26T6.r26t6_Coeff) s ∂volume

theorem fp81s21_avgPrimitive_continuous
    (g : Lp HRS.MS.R26T6.r26t6_Coeff 1 (volume : Measure ℝ)) :
    Continuous (fp81s21_avgPrimitive g) := by
  have hgint : Integrable
      (fun x : ℝ => (g : ℝ →ₘ[volume] HRS.MS.R26T6.r26t6_Coeff) x) volume :=
    memLp_one_iff_integrable.mp (Lp.memLp g)
  exact hgint.continuous_primitive 0

theorem fp81s21_avgSetIntegral_eq_primitive_sub
    (g : Lp HRS.MS.R26T6.r26t6_Coeff 1 (volume : Measure ℝ))
    (a b : ℝ) (hab : a ≤ b) :
    fp81s21_avgSetIntegral a b g =
      fp81s21_avgPrimitive g b - fp81s21_avgPrimitive g a := by
  rw [fp81s21_avgSetIntegral_apply]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  have hgint : Integrable
      (fun x : ℝ => (g : ℝ →ₘ[volume] HRS.MS.R26T6.r26t6_Coeff) x) volume :=
    memLp_one_iff_integrable.mp (Lp.memLp g)
  have h0a : IntervalIntegrable
      (fun x : ℝ => (g : ℝ →ₘ[volume] HRS.MS.R26T6.r26t6_Coeff) x) volume 0 a :=
    hgint.intervalIntegrable
  have hab' : IntervalIntegrable
      (fun x : ℝ => (g : ℝ →ₘ[volume] HRS.MS.R26T6.r26t6_Coeff) x) volume a b :=
    hgint.intervalIntegrable
  have hsum := intervalIntegral.integral_add_adjacent_intervals h0a hab'
  change (∫ x in a..b, (g : ℝ →ₘ[volume] HRS.MS.R26T6.r26t6_Coeff) x ∂volume) = _
  unfold fp81s21_avgPrimitive
  have hsub : (∫ x in (0 : ℝ)..b,
      (g : ℝ →ₘ[volume] HRS.MS.R26T6.r26t6_Coeff) x ∂volume) -
      (∫ x in (0 : ℝ)..a,
        (g : ℝ →ₘ[volume] HRS.MS.R26T6.r26t6_Coeff) x ∂volume) =
      ∫ x in a..b, (g : ℝ →ₘ[volume] HRS.MS.R26T6.r26t6_Coeff) x ∂volume := by
    rw [sub_eq_iff_eq_add]
    simpa [add_comm] using hsum.symm
  exact hsub.symm

def fp81s21_avgValue (H : ℝ) (hH : 0 ≤ H) (k : ℕ)
    (f : fp81s21_UH H) (t : ℝ) : HRS.MS.R26T6.r26t6_Coeff :=
  (fp81s21_avgRight H k t - fp81s21_avgLeft H k t)⁻¹ •
    fp81s21_avgSetIntegral (fp81s21_avgLeft H k t) (fp81s21_avgRight H k t)
      (fp81s21_avgExtendedL1 H hH f)

/-- The interval integral built from the restriction of the L² input to the clipped window. -/
noncomputable def fp81s21_avgLocalIntegralCLM
    (H : ℝ) (hH : 0 ≤ H) (k : ℕ) (t : ℝ) :
    fp81s21_UH H →L[ℝ] HRS.MS.R26T6.r26t6_Coeff := by
  letI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  letI : Fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩
  let μH := volume.restrict (Icc (0 : ℝ) H)
  let s := Icc (fp81s21_avgLeft H k t) (fp81s21_avgRight H k t)
  exact (MeasureTheory.L1.integralCLM
      (α := ℝ) (E := HRS.MS.R26T6.r26t6_Coeff) (μ := μH.restrict s)).comp
    ((fp81s21_l2ToL1 HRS.MS.R26T6.r26t6_Coeff (μH.restrict s)).comp
      (LpToLpRestrictCLM ℝ HRS.MS.R26T6.r26t6_Coeff ℝ μH 2 s))

theorem fp81s21_avgLocalIntegral_norm_le
    (H : ℝ) (hH : 0 < H) (k : ℕ) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) H) (f : fp81s21_UH H) :
    ‖fp81s21_avgLocalIntegralCLM H (le_of_lt hH) k t f‖ ≤
      Real.sqrt (fp81s21_avgRight H k t - fp81s21_avgLeft H k t) * ‖f‖ := by
  letI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  letI : Fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩
  let μH := volume.restrict (Icc (0 : ℝ) H)
  let s := Icc (fp81s21_avgLeft H k t) (fp81s21_avgRight H k t)
  let μs := μH.restrict s
  let f₂ : Lp HRS.MS.R26T6.r26t6_Coeff 2 μs :=
    LpToLpRestrictCLM ℝ HRS.MS.R26T6.r26t6_Coeff ℝ μH 2 s f
  let f₁ := fp81s21_l2ToL1 HRS.MS.R26T6.r26t6_Coeff μs f₂
  have hgeom := fp81s21_avgInterval_geometry H hH k t ht
  have hmass : (μs Set.univ).toReal =
      fp81s21_avgRight H k t - fp81s21_avgLeft H k t := by
    change ((volume.restrict (Icc (0 : ℝ) H)).restrict s Set.univ).toReal = _
    rw [Measure.restrict_restrict_of_subset hgeom.2.2]
    simp [Measure.restrict_apply_univ, Real.volume_Icc, hgeom.1.le]
  have hrestrict : ‖f₂‖ ≤ ‖f‖ := by
    change ‖((Lp.memLp f).restrict s).toLp f‖ ≤ ‖f‖
    exact norm_Lp_toLp_restrict_le s f
  calc
    ‖fp81s21_avgLocalIntegralCLM H (le_of_lt hH) k t f‖ =
        ‖MeasureTheory.L1.integral f₁‖ := by
          simp [fp81s21_avgLocalIntegralCLM, f₁, f₂, μH, μs, s,
            ContinuousLinearMap.comp_apply, MeasureTheory.L1.integral_eq]
    _ ≤ ‖f₁‖ := MeasureTheory.L1.norm_integral_le f₁
    _ ≤ Real.sqrt (μs Set.univ).toReal * ‖f₂‖ := by
      calc
        ‖f₁‖ ≤ ‖fp81s21_l2ToL1 HRS.MS.R26T6.r26t6_Coeff μs‖ * ‖f₂‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ Real.sqrt (μs Set.univ).toReal * ‖f₂‖ :=
          mul_le_mul_of_nonneg_right
            (fp81s21_l2ToL1_norm_le HRS.MS.R26T6.r26t6_Coeff μs)
            (norm_nonneg _)
    _ ≤ Real.sqrt (fp81s21_avgRight H k t - fp81s21_avgLeft H k t) * ‖f‖ := by
      rw [hmass]
      exact mul_le_mul_of_nonneg_left hrestrict (Real.sqrt_nonneg _)

theorem fp81s21_avgValue_eq_localMean
    (H : ℝ) (hH : 0 < H) (k : ℕ) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) H) (f : fp81s21_UH H) :
    fp81s21_avgValue H (le_of_lt hH) k f t =
      (fp81s21_avgRight H k t - fp81s21_avgLeft H k t)⁻¹ •
        fp81s21_avgLocalIntegralCLM H (le_of_lt hH) k t f := by
  letI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  letI : Fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩
  let μH := volume.restrict (Icc (0 : ℝ) H)
  let s := Icc (fp81s21_avgLeft H k t) (fp81s21_avgRight H k t)
  let μs := μH.restrict s
  let u := fp81s21_l2ToL1 HRS.MS.R26T6.r26t6_Coeff μH f
  let g := fp81s21_avgExtendedL1 H (le_of_lt hH) f
  let f₂ : Lp HRS.MS.R26T6.r26t6_Coeff 2 μs :=
    LpToLpRestrictCLM ℝ HRS.MS.R26T6.r26t6_Coeff ℝ μH 2 s f
  let f₁ := fp81s21_l2ToL1 HRS.MS.R26T6.r26t6_Coeff μs f₂
  have hgeom := fp81s21_avgInterval_geometry H hH k t ht
  have hmeasure : μs = volume.restrict s := by
    dsimp [μs, μH, s]
    exact Measure.restrict_restrict_of_subset hgeom.2.2
  have hz : g =ᵐ[μs] (u : ℝ →ₘ[μH] HRS.MS.R26T6.r26t6_Coeff) := by
    have hzero := fp81s21_zeroExtendL1_ae HRS.MS.R26T6.r26t6_Coeff
      volume (Icc (0 : ℝ) H) measurableSet_Icc u
    have hzero' : g =ᵐ[volume.restrict s]
        (Icc (0 : ℝ) H).indicator u := ae_restrict_of_ae hzero
    rw [← hmeasure] at hzero'
    filter_upwards [hzero', ae_restrict_mem (show MeasurableSet s by
      dsimp [s]
      exact measurableSet_Icc)] with x hx hxs
    calc
      g x = (Icc (0 : ℝ) H).indicator u x := hx
      _ = u x := by simp [Set.indicator, hgeom.2.2 hxs]
  have hu : (u : ℝ →ₘ[μH] HRS.MS.R26T6.r26t6_Coeff) =ᵐ[μs] f :=
    ae_restrict_of_ae (fp81s21_l2ToL1_ae HRS.MS.R26T6.r26t6_Coeff μH f)
  have hf₂ : f₂ =ᵐ[μs] f :=
    LpToLpRestrictCLM_coeFn ℝ s f
  have hf₁ : f₁ =ᵐ[μs] f₂ :=
    fp81s21_l2ToL1_ae HRS.MS.R26T6.r26t6_Coeff μs f₂
  have hrep : g =ᵐ[μs] f₁ := by
    filter_upwards [hz, hu, hf₂, hf₁] with x hzx hux hf₂x hf₁x
    calc
      g x = u x := hzx
      _ = f x := hux
      _ = f₂ x := hf₂x.symm
      _ = f₁ x := hf₁x.symm
  have hglobal : fp81s21_avgSetIntegral
      (fp81s21_avgLeft H k t) (fp81s21_avgRight H k t) g =
      ∫ x, (g : ℝ →ₘ[volume] HRS.MS.R26T6.r26t6_Coeff) x ∂μs := by
    rw [fp81s21_avgSetIntegral_apply]
    change (∫ x, (g : ℝ →ₘ[volume] HRS.MS.R26T6.r26t6_Coeff) x ∂
      (volume.restrict s)) = _
    rw [← hmeasure]
  have hlocal : fp81s21_avgLocalIntegralCLM H (le_of_lt hH) k t f =
      ∫ x, (f₁ : ℝ →ₘ[μs] HRS.MS.R26T6.r26t6_Coeff) x ∂μs := by
    change (MeasureTheory.L1.integralCLM
      (α := ℝ) (E := HRS.MS.R26T6.r26t6_Coeff) (μ := μs)) f₁ = _
    have hf₁int : Integrable
        (fun x : ℝ => (f₁ : ℝ →ₘ[μs] HRS.MS.R26T6.r26t6_Coeff) x) μs :=
      memLp_one_iff_integrable.mp (Lp.memLp f₁)
    have hclass : hf₁int.toL1
        (fun x : ℝ => (f₁ : ℝ →ₘ[μs] HRS.MS.R26T6.r26t6_Coeff) x) = f₁ := by
      apply Lp.ext
      exact hf₁int.coeFn_toL1
    rw [← MeasureTheory.L1.integral_eq, ← hclass]
    exact (MeasureTheory.integral_eq _ hf₁int).symm.trans
      (MeasureTheory.L1.integral_of_fun_eq_integral hf₁int).symm
  have hinterval : fp81s21_avgSetIntegral
      (fp81s21_avgLeft H k t) (fp81s21_avgRight H k t) g =
        fp81s21_avgLocalIntegralCLM H (le_of_lt hH) k t f := by
    calc
      _ = ∫ x, (g : ℝ →ₘ[volume] HRS.MS.R26T6.r26t6_Coeff) x ∂μs := hglobal
      _ = ∫ x, (f₁ : ℝ →ₘ[μs] HRS.MS.R26T6.r26t6_Coeff) x ∂μs :=
        integral_congr_ae hrep
      _ = _ := hlocal.symm
  unfold fp81s21_avgValue
  exact congrArg (fun z : HRS.MS.R26T6.r26t6_Coeff =>
    (fp81s21_avgRight H k t - fp81s21_avgLeft H k t)⁻¹ • z) hinterval

theorem fp81s21_avgValue_norm_le
    (H : ℝ) (hH : 0 < H) (k : ℕ) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) H) (f : fp81s21_UH H) :
    ‖fp81s21_avgValue H (le_of_lt hH) k f t‖ ≤
      Real.sqrt (((k : ℝ) + 2) / H) * ‖f‖ := by
  let ℓ := fp81s21_avgRight H k t - fp81s21_avgLeft H k t
  let h := fp81s21_avgHalfWidth H k
  have hgeom := fp81s21_avgInterval_geometry H hH k t ht
  have hℓ : 0 < ℓ := by simpa [ℓ] using hgeom.1
  have hh : 0 < h := by
    simp [h, fp81s21_avgHalfWidth]
    exact div_pos hH (by positivity)
  have hfactor : ℓ⁻¹ * Real.sqrt ℓ = Real.sqrt (ℓ⁻¹) := by
    calc
      ℓ⁻¹ * Real.sqrt ℓ = Real.sqrt ℓ / ℓ := by ring
      _ = (Real.sqrt ℓ)⁻¹ := Real.sqrt_div_self
      _ = Real.sqrt (ℓ⁻¹) := (Real.sqrt_inv ℓ).symm
  have hrecip : ℓ⁻¹ ≤ h⁻¹ := by
    simpa [ℓ, h] using one_div_le_one_div_of_le hh hgeom.2.1
  have hroot : Real.sqrt (ℓ⁻¹) ≤ Real.sqrt (h⁻¹) :=
    Real.sqrt_le_sqrt hrecip
  have hconst : h⁻¹ = ((k : ℝ) + 2) / H := by
    dsimp [h, fp81s21_avgHalfWidth]
    field_simp [ne_of_gt hH]
  rw [fp81s21_avgValue_eq_localMean H hH k t ht f]
  calc
    ‖ℓ⁻¹ • fp81s21_avgLocalIntegralCLM H (le_of_lt hH) k t f‖ =
        ℓ⁻¹ * ‖fp81s21_avgLocalIntegralCLM H (le_of_lt hH) k t f‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hℓ.le)]
    _ ≤ ℓ⁻¹ *
        (Real.sqrt ℓ * ‖f‖) :=
      mul_le_mul_of_nonneg_left
        (fp81s21_avgLocalIntegral_norm_le H hH k t ht f)
        (inv_nonneg.mpr hℓ.le)
    _ = Real.sqrt (ℓ⁻¹) * ‖f‖ := by rw [← mul_assoc, hfactor]
    _ ≤ Real.sqrt (h⁻¹) * ‖f‖ :=
      mul_le_mul_of_nonneg_right hroot (norm_nonneg _)
    _ = Real.sqrt (((k : ℝ) + 2) / H) * ‖f‖ := by rw [hconst]

theorem fp81s21_avgValue_continuousOn
    (H : ℝ) (hH : 0 < H) (k : ℕ) (f : fp81s21_UH H) :
    ContinuousOn (fp81s21_avgValue H (le_of_lt hH) k f) (Icc (0 : ℝ) H) := by
  let g := fp81s21_avgExtendedL1 H (le_of_lt hH) f
  have hprim : Continuous (fp81s21_avgPrimitive g) :=
    fp81s21_avgPrimitive_continuous g
  have hleft : Continuous (fp81s21_avgLeft H k) :=
    continuous_const.max (continuous_id.sub continuous_const)
  have hright : Continuous (fp81s21_avgRight H k) :=
    continuous_const.min (continuous_id.add continuous_const)
  have hlen : Continuous
      (fun t : ℝ => fp81s21_avgRight H k t - fp81s21_avgLeft H k t) :=
    hright.sub hleft
  have hnum : Continuous (fun t : ℝ =>
      fp81s21_avgPrimitive g (fp81s21_avgRight H k t) -
        fp81s21_avgPrimitive g (fp81s21_avgLeft H k t)) :=
    (hprim.comp hright).sub (hprim.comp hleft)
  have hlenInvOn : ContinuousOn
      (fun t : ℝ => (fp81s21_avgRight H k t - fp81s21_avgLeft H k t)⁻¹)
      (Icc (0 : ℝ) H) :=
    hlen.continuousOn.inv₀ (fun t ht => by
      exact ne_of_gt (fp81s21_avgInterval_geometry H hH k t ht).1)
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun t : Icc (0 : ℝ) H =>
    fp81s21_avgValue H (le_of_lt hH) k f (t : ℝ))
  have hlenR : Continuous (fun t : Icc (0 : ℝ) H =>
      (fp81s21_avgRight H k (t : ℝ) - fp81s21_avgLeft H k (t : ℝ))⁻¹) :=
    continuousOn_iff_continuous_domRestrict.mp hlenInvOn
  have hnumR : Continuous (fun t : Icc (0 : ℝ) H =>
      fp81s21_avgPrimitive g (fp81s21_avgRight H k (t : ℝ)) -
        fp81s21_avgPrimitive g (fp81s21_avgLeft H k (t : ℝ))) :=
    hnum.comp continuous_subtype_val
  have hrepr : (fun t : Icc (0 : ℝ) H =>
      fp81s21_avgValue H (le_of_lt hH) k f (t : ℝ)) =
      (fun t : Icc (0 : ℝ) H => (fp81s21_avgRight H k (t : ℝ) -
        fp81s21_avgLeft H k (t : ℝ))⁻¹ •
          (fp81s21_avgPrimitive g (fp81s21_avgRight H k (t : ℝ)) -
            fp81s21_avgPrimitive g (fp81s21_avgLeft H k (t : ℝ)))) := by
    funext t
    have hgeom := fp81s21_avgInterval_geometry H hH k (t : ℝ) t.property
    change (fp81s21_avgRight H k (t : ℝ) - fp81s21_avgLeft H k (t : ℝ))⁻¹ •
        fp81s21_avgSetIntegral (fp81s21_avgLeft H k (t : ℝ))
          (fp81s21_avgRight H k (t : ℝ)) g = _
    apply congrArg (fun z : HRS.MS.R26T6.r26t6_Coeff =>
      (fp81s21_avgRight H k (t : ℝ) - fp81s21_avgLeft H k (t : ℝ))⁻¹ • z)
    exact fp81s21_avgSetIntegral_eq_primitive_sub g
      (fp81s21_avgLeft H k (t : ℝ)) (fp81s21_avgRight H k (t : ℝ))
      (by linarith [hgeom.1])
  rw [hrepr]
  exact hlenR.smul hnumR

/-- The clipped average as a continuous function on the closed time interval. -/
noncomputable def fp81s21_avgOutput
    (H : ℝ) (hH : 0 < H) (k : ℕ) (f : fp81s21_UH H) : fp81s21_CH H :=
  ⟨fun t => fp81s21_avgValue H (le_of_lt hH) k f (t : ℝ),
    continuousOn_iff_continuous_domRestrict.mp
      (fp81s21_avgValue_continuousOn H hH k f)⟩

/-- The normalized clipped averaging map is linear before its norm bound is attached. -/
def fp81s21_avgOperatorLinear
    (H : ℝ) (hH : 0 < H) (k : ℕ) :
    fp81s21_UH H →ₗ[ℝ] fp81s21_CH H where
  toFun := fp81s21_avgOutput H hH k
  map_add' f g := by
    apply ContinuousMap.ext
    intro t
    change fp81s21_avgValue H (le_of_lt hH) k (f + g) (t : ℝ) =
      fp81s21_avgValue H (le_of_lt hH) k f (t : ℝ) +
        fp81s21_avgValue H (le_of_lt hH) k g (t : ℝ)
    rw [fp81s21_avgValue_eq_localMean H hH k (t : ℝ) t.property (f + g),
      fp81s21_avgValue_eq_localMean H hH k (t : ℝ) t.property f,
      fp81s21_avgValue_eq_localMean H hH k (t : ℝ) t.property g]
    simp only [ContinuousLinearMap.map_add, smul_add]
  map_smul' c f := by
    apply ContinuousMap.ext
    intro t
    change fp81s21_avgValue H (le_of_lt hH) k (c • f) (t : ℝ) =
      c • fp81s21_avgValue H (le_of_lt hH) k f (t : ℝ)
    rw [fp81s21_avgValue_eq_localMean H hH k (t : ℝ) t.property (c • f),
      fp81s21_avgValue_eq_localMean H hH k (t : ℝ) t.property f]
    simp only [ContinuousLinearMap.map_smul, smul_smul, mul_comm]

/-- The bounded clipped averaging operator into continuous time histories. -/
noncomputable def fp81s21_avgOperator
    (H : ℝ) (hH : 0 < H) (k : ℕ) :
    fp81s21_UH H →L[ℝ] fp81s21_CH H :=
  (fp81s21_avgOperatorLinear H hH k).mkContinuous
    (Real.sqrt (((k : ℝ) + 2) / H)) (by
      intro f
      have hbound_nonneg :
          0 ≤ Real.sqrt (((k : ℝ) + 2) / H) * ‖f‖ :=
        mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
      apply (ContinuousMap.norm_le (fp81s21_avgOutput H hH k f)
        hbound_nonneg).2
      intro t
      exact fp81s21_avgValue_norm_le H hH k (t : ℝ) t.property f)

theorem fp81s21_avgOperator_opNorm_le (H : ℝ) (hH : 0 < H) (k : ℕ) :
    ‖fp81s21_avgOperator H hH k‖ ≤ Real.sqrt (((k : ℝ) + 2) / H) :=
  LinearMap.mkContinuous_norm_le (fp81s21_avgOperatorLinear H hH k)
    (by positivity) _

/-- The local integral is the Bochner integral of the L² representative on the clipped window. -/
theorem fp81s21_avgLocalIntegral_eq_setIntegral
    (H : ℝ) (hH : 0 < H) (k : ℕ) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) H) (f : fp81s21_UH H) :
    fp81s21_avgLocalIntegralCLM H (le_of_lt hH) k t f =
      ∫ x in Icc (fp81s21_avgLeft H k t) (fp81s21_avgRight H k t),
        (f : ℝ →ₘ[volume.restrict (Icc (0 : ℝ) H)]
          HRS.MS.R26T6.r26t6_Coeff) x ∂volume := by
  let μH := volume.restrict (Icc (0 : ℝ) H)
  let s := Icc (fp81s21_avgLeft H k t) (fp81s21_avgRight H k t)
  let μs := μH.restrict s
  let f₂ : Lp HRS.MS.R26T6.r26t6_Coeff 2 μs :=
    LpToLpRestrictCLM ℝ HRS.MS.R26T6.r26t6_Coeff ℝ μH 2 s f
  let f₁ := fp81s21_l2ToL1 HRS.MS.R26T6.r26t6_Coeff μs f₂
  have hgeom := fp81s21_avgInterval_geometry H hH k t ht
  have hmeasure : μs = volume.restrict s := by
    dsimp [μs, μH, s]
    exact Measure.restrict_restrict_of_subset hgeom.2.2
  have hrep : (f₁ : ℝ →ₘ[μs] HRS.MS.R26T6.r26t6_Coeff) =ᵐ[μs]
      (f : ℝ →ₘ[μH] HRS.MS.R26T6.r26t6_Coeff) := by
    filter_upwards [fp81s21_l2ToL1_ae HRS.MS.R26T6.r26t6_Coeff μs f₂,
      LpToLpRestrictCLM_coeFn ℝ s f] with x hx₁ hx₂
    exact hx₁.trans hx₂
  have hf₁int : Integrable
      (fun x : ℝ => (f₁ : ℝ →ₘ[μs] HRS.MS.R26T6.r26t6_Coeff) x) μs :=
    memLp_one_iff_integrable.mp (Lp.memLp f₁)
  have hlocal :
      fp81s21_avgLocalIntegralCLM H (le_of_lt hH) k t f =
        ∫ x, (f₁ : ℝ →ₘ[μs] HRS.MS.R26T6.r26t6_Coeff) x ∂μs := by
    change (MeasureTheory.L1.integralCLM
      (α := ℝ) (E := HRS.MS.R26T6.r26t6_Coeff) (μ := μs)) f₁ = _
    have hclass : hf₁int.toL1
        (fun x : ℝ => (f₁ : ℝ →ₘ[μs] HRS.MS.R26T6.r26t6_Coeff) x) = f₁ := by
      apply Lp.ext
      exact hf₁int.coeFn_toL1
    rw [← MeasureTheory.L1.integral_eq, ← hclass]
    exact (MeasureTheory.integral_eq _ hf₁int).symm.trans
      (MeasureTheory.L1.integral_of_fun_eq_integral hf₁int).symm
  calc
    fp81s21_avgLocalIntegralCLM H (le_of_lt hH) k t f =
        ∫ x, (f₁ : ℝ →ₘ[μs] HRS.MS.R26T6.r26t6_Coeff) x ∂μs := hlocal
    _ = ∫ x, (f : ℝ →ₘ[μH] HRS.MS.R26T6.r26t6_Coeff) x ∂μs :=
      integral_congr_ae hrep
    _ = ∫ x in Icc (fp81s21_avgLeft H k t) (fp81s21_avgRight H k t),
          (f : ℝ →ₘ[volume.restrict (Icc (0 : ℝ) H)]
            HRS.MS.R26T6.r26t6_Coeff) x ∂volume := by
      rw [hmeasure]

/-- Pointwise normalized Bochner integral formula for the operator. -/
theorem fp81s21_avgOperator_apply
    (H : ℝ) (hH : 0 < H) (k : ℕ) (f : fp81s21_UH H)
    (t : Icc (0 : ℝ) H) :
    (fp81s21_avgOperator H hH k f) t =
      (fp81s21_avgRight H k (t : ℝ) - fp81s21_avgLeft H k (t : ℝ))⁻¹ •
        ∫ x in Icc (fp81s21_avgLeft H k (t : ℝ))
          (fp81s21_avgRight H k (t : ℝ)),
          (f : ℝ →ₘ[volume.restrict (Icc (0 : ℝ) H)]
            HRS.MS.R26T6.r26t6_Coeff) x ∂volume := by
  change fp81s21_avgValue H (le_of_lt hH) k f (t : ℝ) = _
  rw [fp81s21_avgValue_eq_localMean H hH k (t : ℝ) t.property f,
    fp81s21_avgLocalIntegral_eq_setIntegral H hH k (t : ℝ) t.property f]

/-- A single sequence of clipped normalized averages with the sharp stated norm bounds. -/
theorem fp81s21_exists_avgOperators (H : ℝ) (hH : 0 < H) :
    ∃ S : ℕ → fp81s21_UH H →L[ℝ] fp81s21_CH H,
      (∀ k, ‖S k‖ ≤ Real.sqrt (((k : ℝ) + 2) / H)) ∧
      (∀ k (f : fp81s21_UH H) (t : Icc (0 : ℝ) H),
        (S k f) t =
          (fp81s21_avgRight H k (t : ℝ) - fp81s21_avgLeft H k (t : ℝ))⁻¹ •
            ∫ x in Icc (fp81s21_avgLeft H k (t : ℝ))
              (fp81s21_avgRight H k (t : ℝ)),
              (f : ℝ →ₘ[volume.restrict (Icc (0 : ℝ) H)]
                HRS.MS.R26T6.r26t6_Coeff) x ∂volume) := by
  refine ⟨fun k => fp81s21_avgOperator H hH k, ?_, ?_⟩
  · intro k
    exact fp81s21_avgOperator_opNorm_le H hH k
  · intro k f t
    exact fp81s21_avgOperator_apply H hH k f t

#print axioms fp81s21_avgInterval_geometry
#print axioms fp81s21_avgSetIntegral_apply
#print axioms fp81s21_avgPrimitive_continuous
#print axioms fp81s21_avgSetIntegral_eq_primitive_sub
#print axioms fp81s21_avgValue_continuousOn
#print axioms fp81s21_avgLocalIntegral_norm_le
#print axioms fp81s21_avgValue_eq_localMean
#print axioms fp81s21_avgValue_norm_le
#print axioms fp81s21_avgOutput
#print axioms fp81s21_avgOperatorLinear
#print axioms fp81s21_avgOperator
#print axioms fp81s21_avgOperator_opNorm_le
#print axioms fp81s21_avgLocalIntegral_eq_setIntegral
#print axioms fp81s21_avgOperator_apply
#print axioms fp81s21_exists_avgOperators

end HRS.Fp81.S21
