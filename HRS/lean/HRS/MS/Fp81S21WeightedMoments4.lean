import HRS.MS.Fp81S21WeightedMoments3
import HRS.MS.ProClosureS111ChartSections
import HRS.MS.ProClosureS111ChartTrace

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.ProClosureS111 HRS.MS.FixEq

/-- The compact chart encoding is injective because its norm is the
weighted Sobolev norm, whose zero set contains only the zero test. -/
theorem fp81s21_compactFrozenEncode_injective
    {d r : ℕ} {Pw : ℝ}
    (hP : (d : ℝ) < 2 * Pw)
    (E : r26t6_WeightedChart d r Pw) :
    Function.Injective (compactFrozenEncode E hP) := by
  intro f g hfg
  have hsub : compactFrozenEncode E hP (f - g) = 0 := by
    rw [map_sub, hfg, sub_self]
  have hreal : (weightedSobolevE r Pw ((f - g : compactSmoothSubmodule d) : Euc d → ℝ)).toReal = 0 := by
    have hnorm := compactFrozenEncode_norm E hP (f - g)
    rw [hsub] at hnorm
    simpa using hnorm.symm
  have hcompact : IsR2Test ((f - g : compactSmoothSubmodule d) : Euc d → ℝ) :=
    (compactSmoothSubmodule d).sub_mem f.property g.property
  have hwt : IsR2WeightedTest r Pw ((f - g : compactSmoothSubmodule d) : Euc d → ℝ) :=
    (weightedTestSubmodule_iff (d := d)).1
      (weighted_test_of_compact_smooth hP hcompact)
  have hzero : weightedSobolevE r Pw (f - g : Euc d → ℝ) = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff _).1 hreal with hz | hz
    · exact hz
    · exact (hwt.2.ne hz).elim
  have hfun := s57p_E_zero hwt.1 hzero
  apply Subtype.ext
  exact sub_eq_zero.mp hfun

/-- A functional on compact smooth tests that is linear and bounded in the
weighted chart norm extends to the coefficient Hilbert space.  The chart's
dense range and exact norm identity then give its Riesz coefficient vector. -/
theorem fp81s21_chart_riesz_from_tests
    {d r : ℕ} {Pw : ℝ}
    (hP : (d : ℝ) < 2 * Pw)
    (E : r26t6_WeightedChart d r Pw)
    (T : (Euc d → ℝ) → ℝ)
    (hadd : ∀ f g, IsR2Test f → IsR2Test g →
      T (f + g) = T f + T g)
    (hsmul : ∀ c f, IsR2Test f → T (c • f) = c * T f)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ f, IsR2Test f →
      |T f| ≤ C * (weightedSobolevE r Pw f).toReal) :
    ∃ z : r26t6_Coeff,
      (∀ f, IsR2Test f → fp81s21_chartAction E z f = T f) ∧
      dualNormE r Pw T = ENNReal.ofReal ‖z‖ := by
  let S : Submodule ℝ (Euc d → ℝ) := compactSmoothSubmodule d
  let Tlin : S →ₗ[ℝ] ℝ :=
    { toFun := fun f => T f
      map_add' := by
        intro f g
        exact hadd f g f.property g.property
      map_smul' := by
        intro c f
        exact hsmul c f f.property }
  let V : S →ₗ[ℝ] r26t6_Coeff :=
    compactFrozenEncode E hP
  let W : Submodule ℝ r26t6_Coeff := LinearMap.range V
  have hVinj : Function.Injective V :=
    fp81s21_compactFrozenEncode_injective hP E
  let eRange : S ≃ₗ[ℝ] W :=
    { toFun := fun f => ⟨V f, ⟨f, rfl⟩⟩
      invFun := fun x => Classical.choose x.property
      left_inv := by
        intro f
        apply hVinj
        exact Classical.choose_spec (show ∃ g : S, V g = V f from ⟨f, rfl⟩)
      right_inv := by
        intro x
        apply Subtype.ext
        exact Classical.choose_spec x.property
      map_add' := by
        intro f g
        apply Subtype.ext
        exact map_add V f g
      map_smul' := by
        intro c f
        apply Subtype.ext
        exact map_smul V c f }
  let T0 : W →ₗ[ℝ] ℝ := Tlin.comp eRange.symm.toLinearMap
  have hboundChart : ∀ f : S, |T f| ≤ C * ‖E.encode f‖ := by
    intro f
    have hf : IsR2Test (f : Euc d → ℝ) := f.property
    calc
      |T (f : Euc d → ℝ)| ≤
          C * (weightedSobolevE r Pw (f : Euc d → ℝ)).toReal := hbound f hf
      _ = C * ‖E.encode (f : Euc d → ℝ)‖ := by
        rw [E.norm (f : Euc d → ℝ)
          ((weightedTestSubmodule_iff (d := d)).1
            (weighted_test_of_compact_smooth (r := r) hP hf))]
  let Cnn : ℝ≥0 := ⟨C, hC⟩
  have hT0bound : ∀ x : W, ‖T0 x‖ ≤ (Cnn : ℝ) * ‖x‖ := by
    intro x
    let f : S := eRange.symm x
    have hVf : V f = (x : r26t6_Coeff) := by
      exact congrArg Subtype.val (eRange.apply_symm_apply x)
    have hencode : E.encode f = (x : r26t6_Coeff) := by
      exact hVf
    calc
      ‖T0 x‖ = |T f| := by simp [T0, Tlin, f, Real.norm_eq_abs]
      _ ≤ C * ‖E.encode f‖ := hboundChart f
      _ = (Cnn : ℝ) * ‖x‖ := by rw [hencode]; rfl
  let T0c : W →L[ℝ] ℝ := T0.mkContinuous Cnn hT0bound
  let incl : W →L[ℝ] r26t6_Coeff := Submodule.subtypeL W
  have hdense : DenseRange incl := by
    apply Metric.denseRange_iff.2
    intro x eps heps
    obtain ⟨f, hf⟩ := Metric.denseRange_iff.1 E.dense x eps heps
    let f' : S := ⟨f, f.property⟩
    let y : W := ⟨V f', ⟨f', rfl⟩⟩
    refine ⟨y, ?_⟩
    change dist x (E.encode f) < eps
    exact hf
  have hunif : IsUniformInducing incl :=
    (AddMonoidHomClass.isometry_of_norm incl (fun _ => rfl)).isUniformInducing
  let L : r26t6_Coeff →L[ℝ] ℝ := ContinuousLinearMap.extend T0c incl
  have hTagree : ∀ f : S, L (V f) = T f := by
    intro f
    calc
      L (V f) = L (incl (eRange f)) := by rfl
      _ = T0c (eRange f) := by
        rw [ContinuousLinearMap.extend_eq (h_dense := hdense) (h_e := hunif)]
      _ = T f := by simp [T0c, T0, Tlin]
  obtain ⟨z, haction, hdual⟩ := fp81s21_chart_riesz_of_continuous hP E L
  have hTlext : ∀ f, IsR2Test f → T f = L (E.encode f) := by
    intro f hf
    simpa [V, compactFrozenEncode] using (hTagree ⟨f, hf⟩).symm
  have hdualT : dualNormE r Pw T = dualNormE r Pw (fun f => L (E.encode f)) := by
    unfold dualNormE
    apply le_antisymm
    · refine iSup_le fun f => iSup_le fun hf => ?_
      rw [hTlext f ⟨hf.1, hf.2.1⟩]
      exact le_iSup_of_le f (le_iSup_of_le hf le_rfl)
    · refine iSup_le fun f => iSup_le fun hf => ?_
      change ENNReal.ofReal |L (E.encode f)| / weightedSobolevE r Pw f ≤ _
      rw [(hTlext f ⟨hf.1, hf.2.1⟩).symm]
      exact le_iSup_of_le f (le_iSup_of_le hf le_rfl)
  refine ⟨z, ?_, hdualT.trans hdual⟩
  intro f hf
  rw [hTlext f hf]
  exact haction f

#print axioms HRS.Fp81.S21.fp81s21_compactFrozenEncode_injective
#print axioms HRS.Fp81.S21.fp81s21_chart_riesz_from_tests

end HRS.Fp81.S21
