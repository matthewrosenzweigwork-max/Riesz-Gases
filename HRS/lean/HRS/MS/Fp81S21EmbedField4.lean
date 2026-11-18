import HRS.MS.Fp81S21EmbedField3

/-! The bounded primal inclusion on the completed chart coefficient spaces. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.ProClosureS111
  HRS.MS.FixEq

/-- The common compact-test image in the strong chart. -/
def fp81s21_embedField_strongRange
    {d q : ℕ} {Pw : ℝ}
    (hP : (d : ℝ) < 2 * Pw)
    (E : r26t6_WeightedChart d (q + 2) Pw) :
    Submodule ℝ r26t6_Coeff :=
  (fp81s21_embedField_strongTestEncode hP E).range

/-- Recover a compact test from its strong chart coordinate. -/
def fp81s21_embedField_strongRangeEquiv
    {d q : ℕ} {Pw : ℝ}
    (hP : (d : ℝ) < 2 * Pw)
    (E : r26t6_WeightedChart d (q + 2) Pw) :
    compactSmoothSubmodule d ≃ₗ[ℝ]
      fp81s21_embedField_strongRange hP E :=
  LinearEquiv.ofInjective (fp81s21_embedField_strongTestEncode hP E)
    (fp81s21_embedField_strongTestEncode_injective hP E)

/-- The bounded identity map on the common compact-test image. -/
def fp81s21_embedField_primalTestMap
    {d q : ℕ} {Pw : ℝ}
    (hP : (d : ℝ) < 2 * Pw)
    (hPs : (d : ℝ) < 2 * (Pw + 2))
    (E : r26t6_WeightedChart d (q + 2) Pw)
    (Es : r26t6_WeightedChart d q (Pw + 2)) :
    fp81s21_embedField_strongRange hP E →ₗ[ℝ] r26t6_Coeff :=
  (fp81s21_embedField_weakTestEncode hPs Es).comp
    (fp81s21_embedField_strongRangeEquiv hP E).symm.toLinearMap

/-- On the compact-test image, the primal identity is contractive by weight
monotonicity and the exact chart norm formulas. -/
theorem fp81s21_embedField_primalTestMap_norm_le
    {d q : ℕ} {Pw : ℝ}
    (hP : (d : ℝ) < 2 * Pw)
    (hPs : (d : ℝ) < 2 * (Pw + 2))
    (E : r26t6_WeightedChart d (q + 2) Pw)
    (Es : r26t6_WeightedChart d q (Pw + 2))
    (x : fp81s21_embedField_strongRange hP E) :
    ‖fp81s21_embedField_primalTestMap hP hPs E Es x‖ ≤ ‖x‖ := by
  let f : compactSmoothSubmodule d :=
    (fp81s21_embedField_strongRangeEquiv hP E).symm x
  have hstrong : fp81s21_embedField_strongTestEncode hP E f = x.1 :=
    congrArg Subtype.val
      ((fp81s21_embedField_strongRangeEquiv hP E).apply_symm_apply x)
  have hwtS : IsR2WeightedTest (q + 2) Pw (f : Euc d → ℝ) :=
    weightedTestSubmodule_iff.1
      (weighted_test_of_compact_smooth (r := q + 2) (Pw := Pw) hP f.property)
  have hwtW : IsR2WeightedTest q (Pw + 2) (f : Euc d → ℝ) :=
    weightedTestSubmodule_iff.1
      (weighted_test_of_compact_smooth (r := q) (Pw := Pw + 2) hPs f.property)
  have hnormS := E.norm (f : Euc d → ℝ) hwtS
  have hnormW := Es.norm (f : Euc d → ℝ) hwtW
  have henergy := fp81s21_embedField_weightedTestNorm_le
    (d := d) (q := q) (Pw := Pw) (f := (f : Euc d → ℝ))
  change ‖Es.encode (f : Euc d → ℝ)‖ ≤ ‖x.1‖
  calc
    ‖Es.encode (f : Euc d → ℝ)‖ =
        (weightedSobolevE q (Pw + 2) (f : Euc d → ℝ)).toReal := hnormW
    _ ≤ (weightedSobolevE (q + 2) Pw (f : Euc d → ℝ)).toReal :=
      ENNReal.toReal_mono hwtS.2.ne henergy
    _ = ‖fp81s21_embedField_strongTestEncode hP E f‖ := hnormS.symm
    _ = ‖x.1‖ := by rw [hstrong]

/-- The common compact-test image is dense in the strong coefficient space. -/
theorem fp81s21_embedField_strongRange_dense
    {d q : ℕ} {Pw : ℝ}
    (hP : (d : ℝ) < 2 * Pw)
    (E : r26t6_WeightedChart d (q + 2) Pw) :
    DenseRange (fp81s21_embedField_strongRange hP E).subtypeL := by
  let strong := fp81s21_embedField_strongTestEncode hP E
  let S := fp81s21_embedField_strongRange hP E
  let e : S →L[ℝ] r26t6_Coeff := S.subtypeL
  have hrange : Set.range (fun x : S => e x) =
      Set.range (fun f : {f : Euc d → ℝ // IsR2Test f} => E.encode f) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨f, hf⟩ := x.property
      refine ⟨⟨(f : Euc d → ℝ), f.property⟩, ?_⟩
      simpa [e, strong, fp81s21_embedField_strongTestEncode] using hf
    · rintro ⟨f, rfl⟩
      let f' : compactSmoothSubmodule d := ⟨f.1, f.2⟩
      refine ⟨⟨strong f', ⟨f', rfl⟩⟩, ?_⟩
      rfl
  change Dense (Set.range fun x : S => e x)
  rw [hrange]
  exact E.dense

/-- Extend the identity on compact tests to the strong chart completion. -/
def fp81s21_embedField_primal
    {d q : ℕ} {Pw : ℝ}
    (hP : (d : ℝ) < 2 * Pw)
    (hPs : (d : ℝ) < 2 * (Pw + 2))
    (E : r26t6_WeightedChart d (q + 2) Pw)
    (Es : r26t6_WeightedChart d q (Pw + 2)) :
    r26t6_Coeff →L[ℝ] r26t6_Coeff := by
  let S := fp81s21_embedField_strongRange hP E
  let e : S →L[ℝ] r26t6_Coeff := S.subtypeL
  let J : S →L[ℝ] r26t6_Coeff :=
    LinearMap.mkContinuous (fp81s21_embedField_primalTestMap hP hPs E Es) 1
      (fun x => by
        have hx := fp81s21_embedField_primalTestMap_norm_le hP hPs E Es x
        simpa using hx)
  exact ContinuousLinearMap.extend J e

/-- The extended primal inclusion is a contraction. -/
theorem fp81s21_embedField_primal_norm_le
    {d q : ℕ} {Pw : ℝ}
    (hP : (d : ℝ) < 2 * Pw)
    (hPs : (d : ℝ) < 2 * (Pw + 2))
    (E : r26t6_WeightedChart d (q + 2) Pw)
    (Es : r26t6_WeightedChart d q (Pw + 2)) :
    ‖fp81s21_embedField_primal hP hPs E Es‖ ≤ 1 := by
  let S := fp81s21_embedField_strongRange hP E
  let e : S →L[ℝ] r26t6_Coeff := S.subtypeL
  let J : S →L[ℝ] r26t6_Coeff :=
    LinearMap.mkContinuous (fp81s21_embedField_primalTestMap hP hPs E Es) 1
      (fun x => by
        have hx := fp81s21_embedField_primalTestMap_norm_le hP hPs E Es x
        simpa using hx)
  have hdense := fp81s21_embedField_strongRange_dense hP E
  have heNorm : ∀ x : S, ‖e x‖ = ‖(x : r26t6_Coeff)‖ := fun _ => rfl
  have heUniform : IsUniformInducing e :=
    (AddMonoidHomClass.isometry_of_norm e heNorm).isUniformInducing
  have hJnorm : ‖J‖ ≤ 1 :=
    LinearMap.mkContinuous_norm_le (fp81s21_embedField_primalTestMap hP hPs E Es)
      (by norm_num : (0 : ℝ) ≤ 1) (fun x => by
        have hx := fp81s21_embedField_primalTestMap_norm_le hP hPs E Es x
        simpa using hx)
  have hExt : ‖ContinuousLinearMap.extend J e‖ ≤ (1 : ℝ) * ‖J‖ :=
    ContinuousLinearMap.opNorm_extend_le J hdense (N := 1)
      (fun x => by rw [heNorm]; simpa using
        (fp81s21_embedField_primalTestMap_norm_le hP hPs E Es x))
  change ‖ContinuousLinearMap.extend J e‖ ≤ 1
  exact le_trans hExt (by simpa using hJnorm)

/-- The extended primal map agrees with the chart identity on tests. -/
theorem fp81s21_embedField_primal_apply_test
    {d q : ℕ} {Pw : ℝ}
    (hP : (d : ℝ) < 2 * Pw)
    (hPs : (d : ℝ) < 2 * (Pw + 2))
    (E : r26t6_WeightedChart d (q + 2) Pw)
    (Es : r26t6_WeightedChart d q (Pw + 2))
    (f : Euc d → ℝ) (hf : IsR2Test f) :
    fp81s21_embedField_primal hP hPs E Es (E.encode f) = Es.encode f := by
  let S := fp81s21_embedField_strongRange hP E
  let e : S →L[ℝ] r26t6_Coeff := S.subtypeL
  let J : S →L[ℝ] r26t6_Coeff :=
    LinearMap.mkContinuous (fp81s21_embedField_primalTestMap hP hPs E Es) 1
      (fun x => by
        have hx := fp81s21_embedField_primalTestMap_norm_le hP hPs E Es x
        simpa using hx)
  have hdense := fp81s21_embedField_strongRange_dense hP E
  have heNorm : ∀ x : S, ‖e x‖ = ‖(x : r26t6_Coeff)‖ := fun _ => rfl
  have heUniform : IsUniformInducing e :=
    (AddMonoidHomClass.isometry_of_norm e heNorm).isUniformInducing
  let x : S := ⟨E.encode f,
    ⟨⟨f, hf⟩, by simp [fp81s21_embedField_strongTestEncode]⟩⟩
  have hx : e x = E.encode f := rfl
  change ContinuousLinearMap.extend J e (E.encode f) = Es.encode f
  rw [← hx, ContinuousLinearMap.extend_eq (h_dense := hdense) (h_e := heUniform)]
  change fp81s21_embedField_primalTestMap hP hPs E Es x = Es.encode f
  have hI : (fp81s21_embedField_strongRangeEquiv hP E).symm x = ⟨f, hf⟩ := by
    apply (fp81s21_embedField_strongRangeEquiv hP E).injective
    calc
      _ = x := (fp81s21_embedField_strongRangeEquiv hP E).apply_symm_apply x
      _ = _ := by apply Subtype.ext; rfl
  simp [fp81s21_embedField_primalTestMap, hI,
    fp81s21_embedField_weakTestEncode]

#print axioms HRS.Fp81.S21.fp81s21_embedField_primalTestMap_norm_le
#print axioms HRS.Fp81.S21.fp81s21_embedField_strongRange_dense
#print axioms HRS.Fp81.S21.fp81s21_embedField_primal_norm_le
#print axioms HRS.Fp81.S21.fp81s21_embedField_primal_apply_test

end HRS.Fp81.S21
