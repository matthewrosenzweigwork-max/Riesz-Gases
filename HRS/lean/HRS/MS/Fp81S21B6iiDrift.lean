import HRS.MS.Fp81S21B6iiEmp4
import HRS.MS.Fp81S21TimeRep3

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter
open scoped ENNReal RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

/-- The finite-particle normalization in the drift equation. -/
def fp81s21_b6ii_cN (N : ℕ) : ℝ := (Real.sqrt (N : ℝ))⁻¹

/-- The coefficient-space drift formed from the weighted adjoint and the raw
quadratic-field representative. -/
def fp81s21_b6ii_D {Ω : Type*} (L : ℝ → r26t6_Coeff →L[ℝ] r26t6_Coeff)
    (N : ℕ) (qη qB0 : ℝ → Ω → r26t6_Coeff) :
    ℝ → Ω → r26t6_Coeff := fun v ω =>
      L v (qη v ω) - fp81s21_b6ii_cN N • qB0 v ω

/-- The coefficient-space drift is Bochner integrable on every translated
compact time slab. The same uniform second-moment bound is used for the
empirical and raw quadratic representatives. -/
theorem fp81s21_b6ii_product_drift_integrable
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ) (N : ℕ)
    (hN : 2 ≤ N) (A : Particle R N)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (qη qB0 : ℝ → A.Ω → r26t6_Coeff) (M2 CL a H : ℝ)
    (L : ℝ → r26t6_Coeff →L[ℝ] r26t6_Coeff)
    (hL : Measurable (fun z : ℝ × r26t6_Coeff => L z.1 z.2))
    (hM2 : 0 ≤ M2) (hCL : ∀ u, 0 ≤ u → ‖L u‖ ≤ CL)
    (ha : 0 ≤ a) (hH : 0 < H)
    (hηrep : fp81s21_MomentRep Es A.P
      (fp81s21_particleEmpField R N A) qη M2)
    (hBrep : fp81s21_MomentRep E A.P
      (fp81s21_particleQuadRawField R N A) qB0 M2) :
    Integrable
      (fun z : ℝ × A.Ω => fp81s21_b6ii_D L N qη qB0 (a + z.1) z.2)
      ((volume.restrict (Set.Icc 0 H)).prod A.P) := by
  let dt : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) H)
  let ν : Measure (ℝ × A.Ω) := dt.prod A.P
  let gη : ℝ × A.Ω → r26t6_Coeff := fun z => qη (a + z.1) z.2
  let gB : ℝ × A.Ω → r26t6_Coeff := fun z => qB0 (a + z.1) z.2
  haveI : IsFiniteMeasure dt := by infer_instance
  haveI : IsFiniteMeasure ν := by infer_instance
  have hηlp := fp81s21_MomentRep_time_product Es A.P
    (fp81s21_particleEmpField R N A) qη M2 a H hηrep ha hH.le
  have hBlp := fp81s21_MomentRep_time_product E A.P
    (fp81s21_particleQuadRawField R N A) qB0 M2 a H hBrep ha hH.le
  have hηint : Integrable gη ν := by
    have hi := hηlp.1.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    simpa [gη, ν, dt] using hi
  have hBint : Integrable gB ν := by
    have hi := hBlp.1.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    simpa [gB, ν, dt] using hi
  have hηmeas : Measurable gη := by
    change Measurable (Function.uncurry qη ∘
      (fun z : ℝ × A.Ω => (a + z.1, z.2)))
    exact hηrep.1.comp ((measurable_const.add measurable_fst).prodMk measurable_snd)
  have hBmeas : Measurable gB := by
    change Measurable (Function.uncurry qB0 ∘
      (fun z : ℝ × A.Ω => (a + z.1, z.2)))
    exact hBrep.1.comp ((measurable_const.add measurable_fst).prodMk measurable_snd)
  have hLηmeas : Measurable (fun z : ℝ × A.Ω =>
      L (a + z.1) (qη (a + z.1) z.2)) := by
    exact hL.comp ((measurable_const.add measurable_fst).prodMk hηmeas)
  have htime : ∀ᵐ z ∂ν, z.1 ∈ Set.Icc (0 : ℝ) H := by
    exact (Measure.quasiMeasurePreserving_fst
      (μ := dt) (ν := A.P)).ae (ae_restrict_mem measurableSet_Icc)
  have hLηint : Integrable
      (fun z : ℝ × A.Ω => L (a + z.1) (qη (a + z.1) z.2)) ν := by
    refine Integrable.mono' (hηint.norm.const_mul CL) hLηmeas.aestronglyMeasurable ?_
    filter_upwards [htime] with z hz
    calc
      ‖L (a + z.1) (qη (a + z.1) z.2)‖ ≤
          ‖L (a + z.1)‖ * ‖qη (a + z.1) z.2‖ :=
        (L (a + z.1)).le_opNorm _
      _ ≤ CL * ‖qη (a + z.1) z.2‖ :=
        mul_le_mul_of_nonneg_right (hCL _ (add_nonneg ha hz.1))
          (norm_nonneg _)
  have hcN : 0 ≤ fp81s21_b6ii_cN N :=
    inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hBscaled : Integrable
      (fun z : ℝ × A.Ω => fp81s21_b6ii_cN N • qB0 (a + z.1) z.2) ν := by
    change Integrable (fp81s21_b6ii_cN N • gB) ν
    exact Integrable.smul (fp81s21_b6ii_cN N) hBint
  have hsub : Integrable
      (fun z : ℝ × A.Ω =>
        L (a + z.1) (qη (a + z.1) z.2) -
          fp81s21_b6ii_cN N • qB0 (a + z.1) z.2) ν := hLηint.sub hBscaled
  simpa [fp81s21_b6ii_D, ν, dt] using hsub

#print axioms fp81s21_b6ii_product_drift_integrable
end HRS.Fp81.S21
end
