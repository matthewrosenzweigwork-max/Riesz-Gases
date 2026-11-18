import HRS.MS.Fp81S21DriftBV5
import HRS.MS.Fp81S21TimeShift2
import HRS.MS.Fp81S21BVImg
import HRS.MC.E213U3C
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import HRS.Energy.StaticLimitGauss

/-! L² recent-history inputs transported into the closed BV drift and covariance carriers. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 64000
noncomputable section

open MeasureTheory Set TopologicalSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

/-- The L² coefficient history on a finite interval. -/
abbrev fp81s21_L2History (H : ℝ) :=
  Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) H))

/-- The interval L² coefficient source is separable: its measure is separable and
its coefficient Hilbert space is separable. -/
instance fp81s21_L2History_separable (H : ℝ) :
    SeparableSpace (fp81s21_L2History H) := by
  letI : IsSeparable (volume.restrict (Icc (0 : ℝ) H)) := inferInstance
  letI : SeparableSpace r26t6_Coeff :=
    HRS.StaticLimitAux.separable_lp (ι := ℕ)
  letI : SecondCountableTopology (fp81s21_L2History H) := inferInstance
  exact SecondCountableTopology.to_separableSpace

/-- Geometry for the recent window: the clipped duration lies in the L² horizon,
while the translated endpoint is exactly the physical endpoint `a + p.T`. -/
structure fp81s21_RecentBVGeometry (p : Parameters) (a : ℝ) (ha : 0 ≤ a)
    (L : ℝ) (hL : 0 < L) where
  horizon_nonneg : 0 ≤ L + p.T
  start_nonneg : 0 ≤ max (a - L) 0
  duration_nonneg : 0 ≤ a - max (a - L) 0 + p.T
  duration_le_horizon : a - max (a - L) 0 + p.T ≤ L + p.T
  endpoint_eq : max (a - L) 0 + (a - max (a - L) 0 + p.T) = a + p.T

theorem fp81s21_recentBV_geometry (p : Parameters) (a : ℝ) (ha : 0 ≤ a)
    (L : ℝ) (hL : 0 < L) : fp81s21_RecentBVGeometry p a ha L hL := by
  have hH : 0 ≤ L + p.T := by linarith [p.hT.le]
  have hb : 0 ≤ max (a - L) 0 := le_max_right _ _
  have hwindow := fp81s21_recentWindowRestriction ha hL p.hT
  have hshift : 0 ≤ a - max (a - L) 0 := by simpa using hwindow.1
  have hTmem : p.T ∈ Icc (0 : ℝ) p.T := ⟨p.hT.le, le_rfl⟩
  have hend := hwindow.2 p.T hTmem
  refine ⟨hH, hb, ?_, hend.1.2, ?_⟩
  · linarith [hshift, p.hT.le]
  · ring

private theorem fp81s21_recentL2BV_comp_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : Parameters) (a : ℝ) (ha : 0 ≤ a) (L : ℝ) (hL : 0 < L)
    (hH : 0 ≤ L + p.T)
    (A : r26t6_TimeCoeff (a + p.T) →L[ℝ]
      fp81s21_BV0 (E := E) hH)
    (K : ℝ) (hK : 0 ≤ K) (hA : ‖A‖ ≤ K) :
    ‖A.comp ((fp81s21_recentShift p a ha L hL).comp
      (fp81s21_timeL2L1 (L + p.T) hH))‖ ≤ K * Real.sqrt (L + p.T) := by
  have hR : ‖fp81s21_recentShift p a ha L hL‖ ≤ 1 :=
    fp81s21_recentShift_bound p a ha L hL
  have hQ : ‖fp81s21_timeL2L1 (L + p.T) hH‖ ≤ Real.sqrt (L + p.T) :=
    fp81s21_timeL2L1_bound (L + p.T) hH
  have hprod :
      ‖fp81s21_recentShift p a ha L hL‖ *
        ‖fp81s21_timeL2L1 (L + p.T) hH‖ ≤ 1 * Real.sqrt (L + p.T) :=
    mul_le_mul hR hQ (norm_nonneg _) (by norm_num)
  have htail :
      ‖(fp81s21_recentShift p a ha L hL).comp
        (fp81s21_timeL2L1 (L + p.T) hH)‖ ≤ 1 * Real.sqrt (L + p.T) :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans hprod
  calc
    ‖A.comp ((fp81s21_recentShift p a ha L hL).comp
        (fp81s21_timeL2L1 (L + p.T) hH))‖ ≤
        ‖A‖ * ‖(fp81s21_recentShift p a ha L hL).comp
          (fp81s21_timeL2L1 (L + p.T) hH)‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ K * (1 * Real.sqrt (L + p.T)) :=
      mul_le_mul hA htail (norm_nonneg _) hK
    _ = K * Real.sqrt (L + p.T) := by ring

/-- The recent-history drift map from L² coefficients to cumulative BV paths. -/
noncomputable def fp81s21_D2
    {d r : ℕ} {Pw : ℝ} {E : r26t6_WeightedChart d r Pw} {C : WholeCoeff d}
    (p : Parameters) (a : ℝ) (ha : 0 ≤ a) (L : ℝ) (hL : 0 < L)
    (c0 B : ℝ) (O : r26t6_IntervalOperators E C p.T a c0 B)
    (hB : 0 ≤ B) (hc : 0 ≤ c0) :
    fp81s21_L2History (L + p.T) →L[ℝ]
      fp81s21_BV0 (E := R2X d p.T)
        (fp81s21_recentBV_geometry p a ha L hL).horizon_nonneg := by
  let g := fp81s21_recentBV_geometry p a ha L hL
  exact (fp81s21_driftBV O g.horizon_nonneg g.start_nonneg g.duration_nonneg
      g.duration_le_horizon (le_of_eq g.endpoint_eq) hB hc).comp
    ((fp81s21_recentShift p a ha L hL).comp
      (fp81s21_timeL2L1 (L + p.T) g.horizon_nonneg))

/-- The recent-history covariance map into the projective tensor-valued BV paths. -/
noncomputable def fp81s21_J2
    {d r : ℕ} {Pw : ℝ} {E : r26t6_WeightedChart d r Pw} {C : WholeCoeff d}
    (p : Parameters) (a : ℝ) (ha : 0 ≤ a) (L : ℝ) (hL : 0 < L)
    (c0 B : ℝ) (O : r26t6_IntervalOperators E C p.T a c0 B)
    (hB : 0 ≤ B) (hc : 0 ≤ c0) :
    fp81s21_L2History (L + p.T) →L[ℝ]
      fp81s21_BV0 (E := projTensor (R2X d p.T) 2)
        (fp81s21_recentBV_geometry p a ha L hL).horizon_nonneg := by
  let g := fp81s21_recentBV_geometry p a ha L hL
  exact (fp81s21_covarianceBV O g.horizon_nonneg g.start_nonneg g.duration_nonneg
      g.duration_le_horizon (le_of_eq g.endpoint_eq) hB hc).comp
    ((fp81s21_recentShift p a ha L hL).comp
      (fp81s21_timeL2L1 (L + p.T) g.horizon_nonneg))

theorem fp81s21_D2_norm_le
    {d r : ℕ} {Pw : ℝ} {E : r26t6_WeightedChart d r Pw} {C : WholeCoeff d}
    (p : Parameters) (a : ℝ) (ha : 0 ≤ a) (L : ℝ) (hL : 0 < L)
    (c0 B : ℝ) (O : r26t6_IntervalOperators E C p.T a c0 B)
    (hB : 0 ≤ B) (hc : 0 ≤ c0) :
    ‖fp81s21_D2 p a ha L hL c0 B O hB hc‖ ≤ B * Real.sqrt (L + p.T) := by
  let g := fp81s21_recentBV_geometry p a ha L hL
  have hbnd := fp81s21_recentL2BV_comp_norm_le p a ha L hL g.horizon_nonneg
    (fp81s21_driftBV O g.horizon_nonneg g.start_nonneg g.duration_nonneg
      g.duration_le_horizon (le_of_eq g.endpoint_eq) hB hc)
    B hB (fp81s21_driftBV_norm_le O g.horizon_nonneg g.start_nonneg
      g.duration_nonneg g.duration_le_horizon (le_of_eq g.endpoint_eq) hB hc)
  simpa [fp81s21_D2] using hbnd

theorem fp81s21_J2_norm_le
    {d r : ℕ} {Pw : ℝ} {E : r26t6_WeightedChart d r Pw} {C : WholeCoeff d}
    (p : Parameters) (a : ℝ) (ha : 0 ≤ a) (L : ℝ) (hL : 0 < L)
    (c0 B : ℝ) (O : r26t6_IntervalOperators E C p.T a c0 B)
    (hB : 0 ≤ B) (hc : 0 ≤ c0) :
    ‖fp81s21_J2 p a ha L hL c0 B O hB hc‖ ≤
      B * |2 * C.ν| * Real.sqrt (L + p.T) := by
  let g := fp81s21_recentBV_geometry p a ha L hL
  have hK : 0 ≤ B * |2 * C.ν| := mul_nonneg hB (abs_nonneg _)
  have hbnd := fp81s21_recentL2BV_comp_norm_le p a ha L hL g.horizon_nonneg
    (fp81s21_covarianceBV O g.horizon_nonneg g.start_nonneg g.duration_nonneg
      g.duration_le_horizon (le_of_eq g.endpoint_eq) hB hc)
    (B * |2 * C.ν|) hK
    (fp81s21_covarianceBV_norm_le O g.horizon_nonneg g.start_nonneg
      g.duration_nonneg g.duration_le_horizon (le_of_eq g.endpoint_eq) hB hc)
  simpa [fp81s21_J2, mul_assoc] using hbnd

theorem fp81s21_D2_apply
    {d r : ℕ} {Pw : ℝ} {E : r26t6_WeightedChart d r Pw} {C : WholeCoeff d}
    (p : Parameters) (a : ℝ) (ha : 0 ≤ a) (L : ℝ) (hL : 0 < L)
    (c0 B : ℝ) (O : r26t6_IntervalOperators E C p.T a c0 B)
    (hB : 0 ≤ B) (hc : 0 ≤ c0)
    (f : fp81s21_L2History (L + p.T)) (s : Icc (0 : ℝ) (L + p.T)) :
    fp81s21_bvPath (fp81s21_recentBV_geometry p a ha L hL).horizon_nonneg
      (fp81s21_D2 p a ha L hL c0 B O hB hc f) s =
      O.drift (max (a - L) 0)
        (max (a - L) 0 + min (s : ℝ) (a - max (a - L) 0 + p.T))
        (fp81s21_recentShift p a ha L hL
          (fp81s21_timeL2L1 (L + p.T)
            (fp81s21_recentBV_geometry p a ha L hL).horizon_nonneg f)) := by
  let g := fp81s21_recentBV_geometry p a ha L hL
  simpa [fp81s21_D2, ContinuousLinearMap.comp_apply] using
    (fp81s21_driftBV_apply O g.horizon_nonneg g.start_nonneg g.duration_nonneg
      g.duration_le_horizon (le_of_eq g.endpoint_eq) hB hc
      (fp81s21_recentShift p a ha L hL
        (fp81s21_timeL2L1 (L + p.T) g.horizon_nonneg f)) s)

theorem fp81s21_J2_apply
    {d r : ℕ} {Pw : ℝ} {E : r26t6_WeightedChart d r Pw} {C : WholeCoeff d}
    (p : Parameters) (a : ℝ) (ha : 0 ≤ a) (L : ℝ) (hL : 0 < L)
    (c0 B : ℝ) (O : r26t6_IntervalOperators E C p.T a c0 B)
    (hB : 0 ≤ B) (hc : 0 ≤ c0)
    (f : fp81s21_L2History (L + p.T)) (s : Icc (0 : ℝ) (L + p.T)) :
    fp81s21_bvPath (fp81s21_recentBV_geometry p a ha L hL).horizon_nonneg
      (fp81s21_J2 p a ha L hL c0 B O hB hc f) s =
      O.covariance (max (a - L) 0)
        (max (a - L) 0 + min (s : ℝ) (a - max (a - L) 0 + p.T))
        (fp81s21_recentShift p a ha L hL
          (fp81s21_timeL2L1 (L + p.T)
            (fp81s21_recentBV_geometry p a ha L hL).horizon_nonneg f)) := by
  let g := fp81s21_recentBV_geometry p a ha L hL
  simpa [fp81s21_J2, ContinuousLinearMap.comp_apply] using
    (fp81s21_covarianceBV_apply O g.horizon_nonneg g.start_nonneg g.duration_nonneg
      g.duration_le_horizon (le_of_eq g.endpoint_eq) hB hc
      (fp81s21_recentShift p a ha L hL
        (fp81s21_timeL2L1 (L + p.T) g.horizon_nonneg f)) s)

/-- Closed drift image carrier generated by the L² history map. -/
noncomputable def fp81s21_VD
    {d r : ℕ} {Pw : ℝ} {E : r26t6_WeightedChart d r Pw} {C : WholeCoeff d}
    (p : Parameters) (a : ℝ) (ha : 0 ≤ a) (L : ℝ) (hL : 0 < L)
    (c0 B : ℝ) (O : r26t6_IntervalOperators E C p.T a c0 B)
    (hB : 0 ≤ B) (hc : 0 ≤ c0) :
    Submodule ℝ (fp81s21_BV0 (E := R2X d p.T)
      (fp81s21_recentBV_geometry p a ha L hL).horizon_nonneg) :=
  fp81s21_bvImage (fp81s21_recentBV_geometry p a ha L hL).horizon_nonneg
    (fp81s21_D2 p a ha L hL c0 B O hB hc)

/-- Closed covariance image carrier generated by the L² history map. -/
noncomputable def fp81s21_VJ
    {d r : ℕ} {Pw : ℝ} {E : r26t6_WeightedChart d r Pw} {C : WholeCoeff d}
    (p : Parameters) (a : ℝ) (ha : 0 ≤ a) (L : ℝ) (hL : 0 < L)
    (c0 B : ℝ) (O : r26t6_IntervalOperators E C p.T a c0 B)
    (hB : 0 ≤ B) (hc : 0 ≤ c0) :
    Submodule ℝ (fp81s21_BV0 (E := projTensor (R2X d p.T) 2)
      (fp81s21_recentBV_geometry p a ha L hL).horizon_nonneg) :=
  fp81s21_bvImage (fp81s21_recentBV_geometry p a ha L hL).horizon_nonneg
    (fp81s21_J2 p a ha L hL c0 B O hB hc)

noncomputable def fp81s21_VDtransport
    {d r : ℕ} {Pw : ℝ} {E : r26t6_WeightedChart d r Pw} {C : WholeCoeff d}
    (p : Parameters) (a : ℝ) (ha : 0 ≤ a) (L : ℝ) (hL : 0 < L)
    (c0 B : ℝ) (O : r26t6_IntervalOperators E C p.T a c0 B)
    (hB : 0 ≤ B) (hc : 0 ≤ c0) :
    fp81s21_L2History (L + p.T) →L[ℝ]
      fp81s21_VD p a ha L hL c0 B O hB hc :=
  fp81s21_bvTransport (fp81s21_recentBV_geometry p a ha L hL).horizon_nonneg
    (fp81s21_D2 p a ha L hL c0 B O hB hc)

noncomputable def fp81s21_VJtransport
    {d r : ℕ} {Pw : ℝ} {E : r26t6_WeightedChart d r Pw} {C : WholeCoeff d}
    (p : Parameters) (a : ℝ) (ha : 0 ≤ a) (L : ℝ) (hL : 0 < L)
    (c0 B : ℝ) (O : r26t6_IntervalOperators E C p.T a c0 B)
    (hB : 0 ≤ B) (hc : 0 ≤ c0) :
    fp81s21_L2History (L + p.T) →L[ℝ]
      fp81s21_VJ p a ha L hL c0 B O hB hc :=
  fp81s21_bvTransport (fp81s21_recentBV_geometry p a ha L hL).horizon_nonneg
    (fp81s21_J2 p a ha L hL c0 B O hB hc)

theorem fp81s21_VD_complete
    {d r : ℕ} {Pw : ℝ} {E : r26t6_WeightedChart d r Pw} {C : WholeCoeff d}
    (p : Parameters) (a : ℝ) (ha : 0 ≤ a) (L : ℝ) (hL : 0 < L)
    (c0 B : ℝ) (O : r26t6_IntervalOperators E C p.T a c0 B)
    (hB : 0 ≤ B) (hc : 0 ≤ c0) :
    CompleteSpace (fp81s21_VD p a ha L hL c0 B O hB hc) := by
  unfold fp81s21_VD
  infer_instance

theorem fp81s21_VJ_complete
    {d r : ℕ} {Pw : ℝ} {E : r26t6_WeightedChart d r Pw} {C : WholeCoeff d}
    (p : Parameters) (a : ℝ) (ha : 0 ≤ a) (L : ℝ) (hL : 0 < L)
    (c0 B : ℝ) (O : r26t6_IntervalOperators E C p.T a c0 B)
    (hB : 0 ≤ B) (hc : 0 ≤ c0) :
    CompleteSpace (fp81s21_VJ p a ha L hL c0 B O hB hc) := by
  unfold fp81s21_VJ
  letI : CompleteSpace (projTensor (R2X d p.T) 2) :=
    (HRS.MC.E213U3.u3_isClosed_proj (R2X d p.T) 2).completeSpace_coe
  infer_instance

theorem fp81s21_VD_separable
    {d r : ℕ} {Pw : ℝ} {E : r26t6_WeightedChart d r Pw} {C : WholeCoeff d}
    (p : Parameters) (a : ℝ) (ha : 0 ≤ a) (L : ℝ) (hL : 0 < L)
    (c0 B : ℝ) (O : r26t6_IntervalOperators E C p.T a c0 B)
    (hB : 0 ≤ B) (hc : 0 ≤ c0) :
    SeparableSpace (fp81s21_VD p a ha L hL c0 B O hB hc) := by
  unfold fp81s21_VD
  infer_instance

theorem fp81s21_VJ_separable
    {d r : ℕ} {Pw : ℝ} {E : r26t6_WeightedChart d r Pw} {C : WholeCoeff d}
    (p : Parameters) (a : ℝ) (ha : 0 ≤ a) (L : ℝ) (hL : 0 < L)
    (c0 B : ℝ) (O : r26t6_IntervalOperators E C p.T a c0 B)
    (hB : 0 ≤ B) (hc : 0 ≤ c0) :
    SeparableSpace (fp81s21_VJ p a ha L hL c0 B O hB hc) := by
  unfold fp81s21_VJ
  infer_instance

theorem fp81s21_VDtransport_coe
    {d r : ℕ} {Pw : ℝ} {E : r26t6_WeightedChart d r Pw} {C : WholeCoeff d}
    (p : Parameters) (a : ℝ) (ha : 0 ≤ a) (L : ℝ) (hL : 0 < L)
    (c0 B : ℝ) (O : r26t6_IntervalOperators E C p.T a c0 B)
    (hB : 0 ≤ B) (hc : 0 ≤ c0) (f : fp81s21_L2History (L + p.T)) :
    ((fp81s21_VDtransport p a ha L hL c0 B O hB hc f :
      fp81s21_VD p a ha L hL c0 B O hB hc) :
      fp81s21_BV0 (E := R2X d p.T)
        (fp81s21_recentBV_geometry p a ha L hL).horizon_nonneg) =
      fp81s21_D2 p a ha L hL c0 B O hB hc f :=
  fp81s21_bvTransport_coe _ _ _

theorem fp81s21_VJtransport_coe
    {d r : ℕ} {Pw : ℝ} {E : r26t6_WeightedChart d r Pw} {C : WholeCoeff d}
    (p : Parameters) (a : ℝ) (ha : 0 ≤ a) (L : ℝ) (hL : 0 < L)
    (c0 B : ℝ) (O : r26t6_IntervalOperators E C p.T a c0 B)
    (hB : 0 ≤ B) (hc : 0 ≤ c0) (f : fp81s21_L2History (L + p.T)) :
    ((fp81s21_VJtransport p a ha L hL c0 B O hB hc f :
      fp81s21_VJ p a ha L hL c0 B O hB hc) :
      fp81s21_BV0 (E := projTensor (R2X d p.T) 2)
        (fp81s21_recentBV_geometry p a ha L hL).horizon_nonneg) =
      fp81s21_J2 p a ha L hL c0 B O hB hc f :=
  fp81s21_bvTransport_coe _ _ _

theorem fp81s21_VDtransport_difference
    {d r : ℕ} {Pw : ℝ} {E : r26t6_WeightedChart d r Pw} {C : WholeCoeff d}
    (p : Parameters) (a : ℝ) (ha : 0 ≤ a) (L : ℝ) (hL : 0 < L)
    (c0 B : ℝ) (O : r26t6_IntervalOperators E C p.T a c0 B)
    (hB : 0 ≤ B) (hc : 0 ≤ c0) (f g : fp81s21_L2History (L + p.T)) :
    ‖fp81s21_VDtransport p a ha L hL c0 B O hB hc f -
      fp81s21_VDtransport p a ha L hL c0 B O hB hc g‖ ≤
      B * Real.sqrt (L + p.T) * ‖f - g‖ := by
  calc
    _ ≤ ‖fp81s21_D2 p a ha L hL c0 B O hB hc‖ * ‖f - g‖ :=
      fp81s21_bvTransport_difference
        (fp81s21_recentBV_geometry p a ha L hL).horizon_nonneg
        (fp81s21_D2 p a ha L hL c0 B O hB hc) f g
    _ ≤ (B * Real.sqrt (L + p.T)) * ‖f - g‖ :=
      mul_le_mul_of_nonneg_right (fp81s21_D2_norm_le p a ha L hL c0 B O hB hc)
        (norm_nonneg _)

theorem fp81s21_VJtransport_difference
    {d r : ℕ} {Pw : ℝ} {E : r26t6_WeightedChart d r Pw} {C : WholeCoeff d}
    (p : Parameters) (a : ℝ) (ha : 0 ≤ a) (L : ℝ) (hL : 0 < L)
    (c0 B : ℝ) (O : r26t6_IntervalOperators E C p.T a c0 B)
    (hB : 0 ≤ B) (hc : 0 ≤ c0) (f g : fp81s21_L2History (L + p.T)) :
    ‖fp81s21_VJtransport p a ha L hL c0 B O hB hc f -
      fp81s21_VJtransport p a ha L hL c0 B O hB hc g‖ ≤
      B * |2 * C.ν| * Real.sqrt (L + p.T) * ‖f - g‖ := by
  calc
    _ ≤ ‖fp81s21_J2 p a ha L hL c0 B O hB hc‖ * ‖f - g‖ :=
      fp81s21_bvTransport_difference
        (fp81s21_recentBV_geometry p a ha L hL).horizon_nonneg
        (fp81s21_J2 p a ha L hL c0 B O hB hc) f g
    _ ≤ (B * |2 * C.ν| * Real.sqrt (L + p.T)) * ‖f - g‖ :=
      mul_le_mul_of_nonneg_right (fp81s21_J2_norm_le p a ha L hL c0 B O hB hc)
        (norm_nonneg _)

#print axioms fp81s21_L2History_separable
#print axioms fp81s21_recentBV_geometry
#print axioms fp81s21_D2
#print axioms fp81s21_J2
#print axioms fp81s21_D2_norm_le
#print axioms fp81s21_J2_norm_le
#print axioms fp81s21_D2_apply
#print axioms fp81s21_J2_apply
#print axioms fp81s21_VD
#print axioms fp81s21_VJ
#print axioms fp81s21_VDtransport
#print axioms fp81s21_VJtransport
#print axioms fp81s21_VD_complete
#print axioms fp81s21_VJ_complete
#print axioms fp81s21_VD_separable
#print axioms fp81s21_VJ_separable
#print axioms fp81s21_VDtransport_coe
#print axioms fp81s21_VJtransport_coe
#print axioms fp81s21_VDtransport_difference
#print axioms fp81s21_VJtransport_difference

end HRS.Fp81.S21
end
