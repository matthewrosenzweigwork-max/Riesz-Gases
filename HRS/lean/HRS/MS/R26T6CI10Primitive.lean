import HRS.MS.R26T6CI10Bound

/-!
# I10: continuous primitive on the genuine L3 quotient class

The primitive is defined as a continuous map on [0,T] by the
Bochner integral. It depends only on the Lp class, not on
representatives, and is linear.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T6C
open HRS HRS.Whole

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def r26t6c_primitiveFun (T : ℝ) (hT : 0 < T)
    (q : Lp E 3 (volume.restrict (Set.Icc (0 : ℝ) T))) :
    C(Set.Icc (0 : ℝ) T, E) :=
  ⟨fun t => ∫ v in Set.Icc (0 : ℝ) (t : ℝ), (q : ℝ → E) v, by
    have hint : IntegrableOn (q : ℝ → E) (Set.uIcc (0 : ℝ) T) := by
      rw [Set.uIcc_of_le hT.le]
      exact (Lp.memLp q).integrable (by norm_num)
    have hc := intervalIntegral.continuousOn_primitive_interval (a := 0) hint
    rw [Set.uIcc_of_le hT.le] at hc
    have hnew : ContinuousOn
        (fun t : ℝ => ∫ v in Set.Icc (0 : ℝ) t, (q : ℝ → E) v)
        (Set.Icc (0 : ℝ) T) := by
      apply hc.congr
      intro t ht
      change (∫ v in Set.Icc (0 : ℝ) t, (q : ℝ → E) v) =
        ∫ v in (0 : ℝ)..t, (q : ℝ → E) v
      rw [intervalIntegral.integral_of_le ht.1, integral_Icc_eq_integral_Ioc]
    exact continuousOn_iff_continuous_restrict.mp hnew⟩

theorem r26t6c_primitiveFun_add (T : ℝ) (hT : 0 < T)
    (q r : Lp E 3 (volume.restrict (Set.Icc (0 : ℝ) T))) :
    r26t6c_primitiveFun T hT (q + r) =
      r26t6c_primitiveFun T hT q + r26t6c_primitiveFun T hT r := by
  apply ContinuousMap.ext
  intro t
  have hsub : volume.restrict (Set.Icc (0 : ℝ) (t : ℝ)) ≤
      volume.restrict (Set.Icc (0 : ℝ) T) :=
    Measure.restrict_mono (Set.Icc_subset_Icc_right t.2.2) le_rfl
  have hae : (((q + r) : Lp E 3 (volume.restrict (Set.Icc (0 : ℝ) T))) : ℝ → E)
      =ᵐ[volume.restrict (Set.Icc (0 : ℝ) (t : ℝ))]
      (q : ℝ → E) + (r : ℝ → E) :=
    (Lp.coeFn_add q r).filter_mono (Measure.absolutelyContinuous_of_le hsub).ae_le
  have hqfull : IntegrableOn (q : ℝ → E) (Set.Icc (0 : ℝ) T) :=
    (Lp.memLp q).integrable (by norm_num)
  have hrfull : IntegrableOn (r : ℝ → E) (Set.Icc (0 : ℝ) T) :=
    (Lp.memLp r).integrable (by norm_num)
  have hqi : IntegrableOn (q : ℝ → E) (Set.Icc (0 : ℝ) (t : ℝ)) :=
    hqfull.mono_set (Set.Icc_subset_Icc_right t.2.2)
  have hri : IntegrableOn (r : ℝ → E) (Set.Icc (0 : ℝ) (t : ℝ)) :=
    hrfull.mono_set (Set.Icc_subset_Icc_right t.2.2)
  change ∫ v in Set.Icc (0 : ℝ) (t : ℝ), ((q + r : Lp E 3 _) : ℝ → E) v =
    (∫ v in Set.Icc (0 : ℝ) (t : ℝ), (q : ℝ → E) v) +
      ∫ v in Set.Icc (0 : ℝ) (t : ℝ), (r : ℝ → E) v
  rw [integral_congr_ae hae, Pi.add_def, integral_add hqi hri]

theorem r26t6c_primitiveFun_smul (T : ℝ) (hT : 0 < T)
    (c : ℝ) (q : Lp E 3 (volume.restrict (Set.Icc (0 : ℝ) T))) :
    r26t6c_primitiveFun T hT (c • q) =
      c • r26t6c_primitiveFun T hT q := by
  apply ContinuousMap.ext
  intro t
  have hsub : volume.restrict (Set.Icc (0 : ℝ) (t : ℝ)) ≤
      volume.restrict (Set.Icc (0 : ℝ) T) :=
    Measure.restrict_mono (Set.Icc_subset_Icc_right t.2.2) le_rfl
  have hae : (((c • q) : Lp E 3 (volume.restrict (Set.Icc (0 : ℝ) T))) : ℝ → E)
      =ᵐ[volume.restrict (Set.Icc (0 : ℝ) (t : ℝ))]
      c • (q : ℝ → E) :=
    (Lp.coeFn_smul c q).filter_mono (Measure.absolutelyContinuous_of_le hsub).ae_le
  change ∫ v in Set.Icc (0 : ℝ) (t : ℝ), ((c • q : Lp E 3 _) : ℝ → E) v =
    c • ∫ v in Set.Icc (0 : ℝ) (t : ℝ), (q : ℝ → E) v
  rw [integral_congr_ae hae, Pi.smul_def, integral_smul]

def r26t6c_primitiveLin (T : ℝ) (hT : 0 < T) :
    Lp E 3 (volume.restrict (Set.Icc (0 : ℝ) T)) →ₗ[ℝ]
      C(Set.Icc (0 : ℝ) T, E) where
  toFun := r26t6c_primitiveFun T hT
  map_add' := r26t6c_primitiveFun_add T hT
  map_smul' := r26t6c_primitiveFun_smul T hT
end HRS.MS.R26T6C
