import HRS.MS.Fp81S21WeightedGenAdj
import HRS.MS.Fp81S21EmbedField4

/-! Extension of the bounded weighted generator from compact tests. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open scoped RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

abbrev fp81s21_Output (p : Parameters) (f : Euc p.d → ℝ) : Prop :=
  IsR2WeightedTest (fp81s21_q p) (fp81s21_P p + 2) f

abbrev fp81s21_Ein (p : Parameters) (f : Euc p.d → ℝ) : ENNReal :=
  weightedSobolevE (fp81s21_q p + 2) (fp81s21_P p) f

abbrev fp81s21_Eout (p : Parameters) (f : Euc p.d → ℝ) : ENNReal :=
  weightedSobolevE (fp81s21_q p) (fp81s21_P p + 2) f

def fp81s21_bound {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    (A : ℝ) : Prop :=
  ∀ u, 0 ≤ u → ∀ f, fp81s21_Input p f →
    fp81s21_Output p (generatorW (r26t3_coeff R) u f) ∧
    fp81s21_Eout p (generatorW (r26t3_coeff R) u f) ≤
      ENNReal.ofReal A * fp81s21_Ein p f

def fp81s21_linear {p : Parameters} {δ : ℝ} (R : Trajectory p δ) : Prop :=
  ∀ u, 0 ≤ u → ∀ f g, fp81s21_Input p f → fp81s21_Input p g → ∀ a : ℝ,
    generatorW (r26t3_coeff R) u (f + a • g) =
      generatorW (r26t3_coeff R) u f + a • generatorW (r26t3_coeff R) u g

private theorem fp81s21_weightedGen_compactInput
    {p : Parameters} (hP : (p.d : ℝ) < 2 * fp81s21_P p)
    (f : compactSmoothSubmodule p.d) : fp81s21_Input p f := by
  change IsR2WeightedTest (fp81s21_q p + 2) (fp81s21_P p) (f : Euc p.d → ℝ)
  exact weightedTestSubmodule_iff.1
    (weighted_test_of_compact_smooth (r := fp81s21_q p + 2)
      (Pw := fp81s21_P p) hP f.property)

/-- The encoded generator on the compact smooth test core is linear at each
nonnegative time, using the supplied full-test linearity hypothesis. -/
def fp81s21_weightedGen_compactMap
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (fp81s21_q p) (fp81s21_P p + 2))
    (E : r26t6_WeightedChart p.d (fp81s21_q p + 2) (fp81s21_P p))
    (hP : (p.d : ℝ) < 2 * fp81s21_P p)
    (A : ℝ) (hb : fp81s21_bound R A) (hl : fp81s21_linear R)
    (u : ℝ) (hu : 0 ≤ u) :
    compactSmoothSubmodule p.d →ₗ[ℝ] fp81s21_F where
  toFun f := Es.encode (generatorW (r26t3_coeff R) u f)
  map_add' := by
    intro f g
    have hf := fp81s21_weightedGen_compactInput hP f
    have hg := fp81s21_weightedGen_compactInput hP g
    have houtf := (hb u hu f hf).1
    have houtg := (hb u hu g hg).1
    have hgen := hl u hu f g hf hg (1 : ℝ)
    change Es.encode (generatorW (r26t3_coeff R) u ((f : Euc p.d → ℝ) + g)) = _
    rw [show (f : Euc p.d → ℝ) + (g : Euc p.d → ℝ) =
      (f : Euc p.d → ℝ) + (1 : ℝ) • (g : Euc p.d → ℝ) by simp]
    calc
      Es.encode (generatorW (r26t3_coeff R) u
          ((f : Euc p.d → ℝ) + (1 : ℝ) • (g : Euc p.d → ℝ))) =
          Es.encode (generatorW (r26t3_coeff R) u (f : Euc p.d → ℝ) +
            1 • generatorW (r26t3_coeff R) u (g : Euc p.d → ℝ)) :=
        congrArg Es.encode hgen
      _ = Es.encode (generatorW (r26t3_coeff R) u (f : Euc p.d → ℝ) +
            generatorW (r26t3_coeff R) u (g : Euc p.d → ℝ)) := by rw [one_smul]
      _ = Es.encode (generatorW (r26t3_coeff R) u (f : Euc p.d → ℝ)) +
            Es.encode (generatorW (r26t3_coeff R) u (g : Euc p.d → ℝ)) :=
        Es.add _ _ houtf houtg
  map_smul' := by
    intro a f
    have hf := fp81s21_weightedGen_compactInput hP f
    have hzero : fp81s21_Input p (0 : Euc p.d → ℝ) := by
      change IsR2WeightedTest (fp81s21_q p + 2) (fp81s21_P p) 0
      exact weightedTestSubmodule_iff.1
        (weightedTestSubmodule p.d (fp81s21_q p + 2) (fp81s21_P p)).zero_mem
    have hGzero := hl u hu (0 : Euc p.d → ℝ) 0 hzero hzero (1 : ℝ)
    have hGzero' : generatorW (r26t3_coeff R) u 0 = 0 := by
      have h' : 0 + generatorW (r26t3_coeff R) u 0 =
          generatorW (r26t3_coeff R) u 0 + generatorW (r26t3_coeff R) u 0 := by
        simpa using hGzero
      exact (add_right_cancel h').symm
    have hgen := hl u hu (0 : Euc p.d → ℝ) f hzero hf a
    have hscaled : generatorW (r26t3_coeff R) u (a • (f : Euc p.d → ℝ)) =
        a • generatorW (r26t3_coeff R) u f := by
      simpa [hGzero'] using hgen
    have houtf := (hb u hu f hf).1
    change Es.encode (generatorW (r26t3_coeff R) u (a • (f : Euc p.d → ℝ))) = _
    rw [hscaled]
    exact Es.smul a _ houtf

private theorem fp81s21_weightedGen_compactMap_norm_le
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (fp81s21_q p) (fp81s21_P p + 2))
    (E : r26t6_WeightedChart p.d (fp81s21_q p + 2) (fp81s21_P p))
    (hP : (p.d : ℝ) < 2 * fp81s21_P p)
    (A : ℝ) (hA : 0 ≤ A) (hb : fp81s21_bound R A)
    (u : ℝ) (hu : 0 ≤ u) (f : compactSmoothSubmodule p.d) :
    ‖Es.encode (generatorW (r26t3_coeff R) u f)‖ ≤
      A * ‖E.encode f‖ := by
  have hf := fp81s21_weightedGen_compactInput hP f
  have hres := hb u hu f hf
  have hnormIn := E.norm f hf
  have hnormOut := Es.norm (generatorW (r26t3_coeff R) u f) hres.1
  have hprod : ENNReal.ofReal A * fp81s21_Ein p f ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.2.ne
  have hreal := ENNReal.toReal_mono hprod hres.2
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA] at hreal
  change ‖Es.encode (generatorW (r26t3_coeff R) u f)‖ ≤
    A * ‖E.encode f‖
  rw [hnormOut, hnormIn]
  exact hreal

/-- Extend the compact-test generator continuously to the coefficient space.
The result has the exact supplied operator norm bound and agrees with the
encoded generator on every compact smooth test. -/
def fp81s21_weightedGen_extension
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (fp81s21_q p) (fp81s21_P p + 2))
    (E : r26t6_WeightedChart p.d (fp81s21_q p + 2) (fp81s21_P p))
    (hP : (p.d : ℝ) < 2 * fp81s21_P p)
    (A : ℝ) (hA : 0 ≤ A) (hb : fp81s21_bound R A)
    (hl : fp81s21_linear R) (u : ℝ) (hu : 0 ≤ u) :
    fp81s21_F →L[ℝ] fp81s21_F := by
  let S := fp81s21_embedField_strongRange hP E
  let e : S →L[ℝ] fp81s21_F := S.subtypeL
  let J0 : S →ₗ[ℝ] fp81s21_F :=
    (fp81s21_weightedGen_compactMap R Es E hP A hb hl u hu).comp
      (fp81s21_embedField_strongRangeEquiv hP E).symm.toLinearMap
  have hJbound : ∀ x : S, ‖J0 x‖ ≤ A * ‖(x : fp81s21_F)‖ := by
    intro x
    let f : compactSmoothSubmodule p.d :=
      (fp81s21_embedField_strongRangeEquiv hP E).symm x
    have hstrong : fp81s21_embedField_strongTestEncode hP E f = x.1 :=
      congrArg Subtype.val
        ((fp81s21_embedField_strongRangeEquiv hP E).apply_symm_apply x)
    have hstrong' : E.encode (f : Euc p.d → ℝ) = (x : fp81s21_F) := by
      simpa [fp81s21_embedField_strongTestEncode] using hstrong
    change ‖fp81s21_weightedGen_compactMap R Es E hP A hb hl u hu f‖ ≤
      A * ‖(x : fp81s21_F)‖
    change ‖Es.encode (generatorW (r26t3_coeff R) u f)‖ ≤
      A * ‖(x : fp81s21_F)‖
    calc
      ‖Es.encode (generatorW (r26t3_coeff R) u f)‖ ≤ A * ‖E.encode f‖ :=
        fp81s21_weightedGen_compactMap_norm_le
          R Es E hP A hA hb u hu f
      _ = A * ‖(x : fp81s21_F)‖ := by rw [hstrong']
  let J : S →L[ℝ] fp81s21_F := LinearMap.mkContinuous J0 A hJbound
  let L : fp81s21_F →L[ℝ] fp81s21_F := ContinuousLinearMap.extend J e
  exact L

theorem fp81s21_weightedGen_extension_norm_le
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (fp81s21_q p) (fp81s21_P p + 2))
    (E : r26t6_WeightedChart p.d (fp81s21_q p + 2) (fp81s21_P p))
    (hP : (p.d : ℝ) < 2 * fp81s21_P p)
    (A : ℝ) (hA : 0 ≤ A) (hb : fp81s21_bound R A)
    (hl : fp81s21_linear R) (u : ℝ) (hu : 0 ≤ u) :
    ‖fp81s21_weightedGen_extension R Es E hP A hA hb hl u hu‖ ≤ A := by
  let S := fp81s21_embedField_strongRange hP E
  let e : S →L[ℝ] fp81s21_F := S.subtypeL
  let J0 : S →ₗ[ℝ] fp81s21_F :=
    (fp81s21_weightedGen_compactMap R Es E hP A hb hl u hu).comp
      (fp81s21_embedField_strongRangeEquiv hP E).symm.toLinearMap
  have hJbound : ∀ x : S, ‖J0 x‖ ≤ A * ‖(x : fp81s21_F)‖ := by
    intro x
    let f : compactSmoothSubmodule p.d :=
      (fp81s21_embedField_strongRangeEquiv hP E).symm x
    have hstrong : fp81s21_embedField_strongTestEncode hP E f = x.1 :=
      congrArg Subtype.val
        ((fp81s21_embedField_strongRangeEquiv hP E).apply_symm_apply x)
    have hstrong' : E.encode (f : Euc p.d → ℝ) = (x : fp81s21_F) := by
      simpa [fp81s21_embedField_strongTestEncode] using hstrong
    change ‖fp81s21_weightedGen_compactMap R Es E hP A hb hl u hu f‖ ≤
      A * ‖(x : fp81s21_F)‖
    change ‖Es.encode (generatorW (r26t3_coeff R) u f)‖ ≤
      A * ‖(x : fp81s21_F)‖
    calc
      ‖Es.encode (generatorW (r26t3_coeff R) u f)‖ ≤ A * ‖E.encode f‖ :=
        fp81s21_weightedGen_compactMap_norm_le
          R Es E hP A hA hb u hu f
      _ = A * ‖(x : fp81s21_F)‖ := by rw [hstrong']
  let J : S →L[ℝ] fp81s21_F := LinearMap.mkContinuous J0 A hJbound
  have hJnorm : ‖J‖ ≤ A :=
    LinearMap.mkContinuous_norm_le J0 hA hJbound
  have hdense := fp81s21_embedField_strongRange_dense hP E
  have heNorm : ∀ x : S, ‖e x‖ = ‖(x : fp81s21_F)‖ := fun _ => rfl
  have hExt : ‖ContinuousLinearMap.extend J e‖ ≤
      (1 : ℝ) * ‖J‖ :=
    ContinuousLinearMap.opNorm_extend_le J hdense (N := 1) fun x => by
      calc
        ‖x‖ = ‖e x‖ := by rw [heNorm]; rfl
        _ ≤ (1 : ℝ) * ‖e x‖ := by simp
  change ‖ContinuousLinearMap.extend J e‖ ≤ A
  calc
    ‖ContinuousLinearMap.extend J e‖ ≤ (1 : ℝ) * ‖J‖ := hExt
    _ ≤ A := by simpa using hJnorm

#print axioms HRS.Fp81.S21.fp81s21_weightedGen_extension_norm_le

end HRS.Fp81.S21
