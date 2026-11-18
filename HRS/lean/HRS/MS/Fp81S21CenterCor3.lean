import HRS.MS.Fp81S21SmoothSqErr
import HRS.MS.Fp81S21LiftingClean

/-! Conditional physical centering and averaging consequences of the V2
continuous-path to time-L² identity. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HRS.Fp81.S21

local instance fp81s21_centerCor_UH_measSpace (H : ℝ) : MeasurableSpace
    (fp81s21_SmoothUH H) := borel _
local instance fp81s21_centerCor_UH_borelSpace (H : ℝ) : BorelSpace
    (fp81s21_SmoothUH H) := ⟨rfl⟩

/-- The V2 identity identifies the Bochner mean of the time-section class
with the L² section of the Bochner mean continuous path. -/
theorem fp81s21_centerCor_v2_mean_identity
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (H : ℝ) (hH : 0 < H)
    (X : Ω → fp81s21_SmoothCH H)
    (U : Ω → fp81s21_SmoothUH H)
    (hX : MemLp X 2 P) (hU : MemLp U 2 P)
    (hV2 : U =ᵐ[P] fun ω =>
      fp81s21_smoothPathToL2 H hH (X ω)) :
    (∫ ω, U ω ∂P) =
      fp81s21_smoothPathToL2 H hH (∫ ω, X ω ∂P) := by
  have hXint : Integrable X P := hX.integrable one_le_two
  calc
    (∫ ω, U ω ∂P) =
        ∫ ω, fp81s21_smoothPathToL2 H hH (X ω) ∂P :=
      integral_congr_ae hV2
    _ = fp81s21_smoothPathToL2 H hH (∫ ω, X ω ∂P) :=
      (fp81s21_smoothPathToL2 H hH).integral_comp_comm hXint

/-- Under the explicit V2 identity, S2 smoothing remains valid after
centering under the law. The averaging map is
fp81s21_avgOperator H hH k; its error profile is
2 * sqrt D * (H / (k + 2))^(1/8).

The premise hV2 is precisely the physical identity
U =ᵐ[P] fun ω => fp81s21_smoothPathToL2 H hH (X ω). V2-N and V2-G
are not currently available as unconditional physical exports, so this
corollary keeps that missing identity explicit. -/
theorem fp81s21_centerCor_avgOperator_SqErr
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (H D : ℝ) (hH : 0 < H) (hD : 0 ≤ D) (k : ℕ)
    (X : Ω → fp81s21_SmoothCH H)
    (U : Ω → fp81s21_SmoothUH H) (B : Ω → ℝ)
    (hXm : Measurable X) (hX : MemLp X 2 P)
    (hUm : Measurable U) (hU : MemLp U 2 P)
    (hBm : Measurable B) (hB0 : ∀ ω, 0 ≤ B ω)
    (hBint : Integrable (fun ω => B ω ^ 2) P)
    (hBD : (∫ ω, B ω ^ 2 ∂P) ≤ D)
    (hHolder : ∀ᵐ ω ∂P, ∀ s t : Set.Icc (0 : ℝ) H,
      ‖X ω s - X ω t‖ ≤
        B ω * |(s : ℝ) - (t : ℝ)| ^ (1 / 8 : ℝ))
    (hV2 : U =ᵐ[P] fun ω =>
      fp81s21_smoothPathToL2 H hH (X ω)) :
    fp81s21_SqErr P
      (fun ω => X ω - ∫ ω', X ω' ∂P)
      (fun ω => fp81s21_avgOperator H hH k
        (U ω - ∫ ω', U ω' ∂P))
      (2 * Real.sqrt D *
        (H / ((k : ℝ) + 2)) ^ (1 / 8 : ℝ)) := by
  let S : fp81s21_SmoothUH H →L[ℝ] fp81s21_SmoothCH H :=
    fp81s21_avgOperator H hH k
  let V : Ω → fp81s21_SmoothUH H :=
    fun ω => fp81s21_smoothPathToL2 H hH (X ω)
  let Y : Ω → fp81s21_SmoothCH H := fun ω => S (U ω)
  let Y0 : Ω → fp81s21_SmoothCH H := fun ω => S (V ω)
  let ε : ℝ := Real.sqrt D *
    (fp81s21_avgHalfWidth H k) ^ (1 / 8 : ℝ)
  have hhalf : 0 < fp81s21_avgHalfWidth H k := by
    unfold fp81s21_avgHalfWidth
    apply div_pos hH
    exact_mod_cast (show 0 < k + 2 by omega)
  have hYeq : Y0 =ᵐ[P] Y := by
    filter_upwards [hV2] with ω hω
    dsimp [Y0, Y, V]
    rw [hω]
  have hRaw := fp81s21_avgOperator_SqErr P H D hH hD k X B
    hXm hBm hB0 hBint hBD hHolder
  have hRawY0 : fp81s21_SqErr P X Y0 ε := by
    simpa [Y0, V, ε, fp81s21_avgHalfWidth] using hRaw
  have hSqEq :
      (fun ω => ‖X ω - Y0 ω‖ ^ 2) =ᵐ[P]
        (fun ω => ‖X ω - Y ω‖ ^ 2) := by
    filter_upwards [hYeq] with ω hω
    simp [hω]
  have hRawY : fp81s21_SqErr P X Y ε := by
    refine ⟨hRawY0.1.congr hSqEq, ?_⟩
    calc
      (∫ ω, ‖X ω - Y ω‖ ^ 2 ∂P) =
          ∫ ω, ‖X ω - Y0 ω‖ ^ 2 ∂P :=
        integral_congr_ae hSqEq.symm
      _ ≤ ε ^ 2 := hRawY0.2
  have hY : MemLp Y 2 P := by
    exact hU.continuousLinearMap_comp S
  have hDiff : MemLp (fun ω => X ω - Y ω) 2 P :=
    hX.sub hY
  let C : Ω → fp81s21_SmoothCH H := fun ω =>
    (X ω - ∫ ω', X ω' ∂P) - (Y ω - ∫ ω', Y ω' ∂P)
  have hXc : MemLp (fun ω => X ω - ∫ ω', X ω' ∂P) 2 P := by
    exact hX.sub (memLp_const _)
  have hYc : MemLp (fun ω => Y ω - ∫ ω', Y ω' ∂P) 2 P := by
    exact hY.sub (memLp_const _)
  have hC : MemLp C 2 P := by
    exact hXc.sub hYc
  have hCenterBound :
      eLpNorm C 2 P ≤ 2 * eLpNorm (fun ω => X ω - Y ω) 2 P := by
    simpa [C] using
      HRS.Fp81.V01.fp81_s21_center_L2' X Y hX hY
  have hDiffFormula :
      eLpNorm (fun ω => X ω - Y ω) 2 P =
        ENNReal.ofReal (Real.sqrt (∫ ω, ‖X ω - Y ω‖ ^ 2 ∂P)) := by
    rw [hDiff.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    simp [Real.sqrt_eq_rpow]
  have hε0 : 0 ≤ ε := by
    dsimp [ε]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (Real.rpow_nonneg (le_of_lt hhalf) _)
  have hDiffBound :
      eLpNorm (fun ω => X ω - Y ω) 2 P ≤ ENNReal.ofReal ε := by
    rw [hDiffFormula]
    apply ENNReal.ofReal_le_ofReal
    apply Real.sqrt_le_iff.mpr
    exact ⟨hε0, by simpa [ε] using hRawY.2⟩
  have hCBound : eLpNorm C 2 P ≤ ENNReal.ofReal (2 * ε) := by
    calc
      eLpNorm C 2 P ≤ 2 * eLpNorm (fun ω => X ω - Y ω) 2 P :=
        hCenterBound
      _ ≤ 2 * ENNReal.ofReal ε :=
        by gcongr
      _ = ENNReal.ofReal (2 * ε) := by
        calc
          2 * ENNReal.ofReal ε =
              ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal ε := by norm_num
          _ = ENNReal.ofReal (2 * ε) :=
            (ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)).symm
  have hCintegrable : Integrable (fun ω => ‖C ω‖ ^ 2) P :=
    (memLp_two_iff_integrable_sq_norm hC.aestronglyMeasurable).1 hC
  have hCformula :
      eLpNorm C 2 P =
        ENNReal.ofReal (Real.sqrt (∫ ω, ‖C ω‖ ^ 2 ∂P)) := by
    rw [hC.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    simp [Real.sqrt_eq_rpow]
  have hCroot : Real.sqrt (∫ ω, ‖C ω‖ ^ 2 ∂P) ≤ 2 * ε := by
    have hENN : ENNReal.ofReal (Real.sqrt (∫ ω, ‖C ω‖ ^ 2 ∂P)) ≤
        ENNReal.ofReal (2 * ε) := by
      rw [← hCformula]
      exact hCBound
    exact (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (by norm_num) hε0)).mp hENN
  have hCbound : (∫ ω, ‖C ω‖ ^ 2 ∂P) ≤ (2 * ε) ^ 2 := by
    have hI0 : 0 ≤ ∫ ω, ‖C ω‖ ^ 2 ∂P :=
      integral_nonneg fun ω => sq_nonneg _
    rw [← Real.sq_sqrt hI0]
    exact (sq_le_sq₀ (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) hε0)).2 hCroot
  have hUInt : Integrable U P := hU.integrable one_le_two
  have hSmean :
      (∫ ω, Y ω ∂P) = S (∫ ω, U ω ∂P) := by
    exact S.integral_comp_comm hUInt
  have hCenterEq :
      C =ᵐ[P] fun ω =>
        (X ω - ∫ ω', X ω' ∂P) -
          S (U ω - ∫ ω', U ω' ∂P) := by
    filter_upwards with ω
    dsimp [C, Y]
    rw [hSmean]
    simp
  have hCenterSqEq :
      (fun ω => ‖C ω‖ ^ 2) =ᵐ[P]
        (fun ω => ‖(X ω - ∫ ω', X ω' ∂P) -
          S (U ω - ∫ ω', U ω' ∂P)‖ ^ 2) := by
    filter_upwards [hCenterEq] with ω hω
    simp [hω]
  have hTargetIntegrable :
      Integrable (fun ω =>
        ‖(X ω - ∫ ω', X ω' ∂P) -
          S (U ω - ∫ ω', U ω' ∂P)‖ ^ 2) P := by
    exact hCintegrable.congr hCenterSqEq
  refine ⟨hTargetIntegrable, ?_⟩
  calc
    (∫ ω, ‖(X ω - ∫ ω', X ω' ∂P) -
        S (U ω - ∫ ω', U ω' ∂P)‖ ^ 2 ∂P) =
      ∫ ω, ‖C ω‖ ^ 2 ∂P :=
        integral_congr_ae hCenterSqEq.symm
    _ ≤ (2 * ε) ^ 2 := hCbound
    _ = (2 * Real.sqrt D *
        (H / ((k : ℝ) + 2)) ^ (1 / 8 : ℝ)) ^ 2 := by
      simp [ε, fp81s21_avgHalfWidth]
      ring

#print axioms HRS.Fp81.S21.fp81s21_centerCor_v2_mean_identity
#print axioms HRS.Fp81.S21.fp81s21_centerCor_avgOperator_SqErr

end HRS.Fp81.S21
end
