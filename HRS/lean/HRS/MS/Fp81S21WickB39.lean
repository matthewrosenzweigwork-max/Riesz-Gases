import HRS.MS.Fp81S21WickB38

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory
open HRS (Euc)
open HRS.Whole

namespace HRS.Fp81.S21

variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P) (Kstar : ℝ)
    (hL : ‖L‖ ≤ Kstar)
    (hJoint : ∀ r (v : Fin r → Lp ℝ 2 μ),
      HRS.IsCenteredGaussian (P.map fun ω => fun i => (L (v i)) ω))

theorem fp81s21_wickB39_operator_sub
    (x y : fp81s21_wickB32_finiteRankSubmodule μ) :
    fp81s21_wickB38_operator L Kstar hL hJoint (x - y) =
      fp81s21_wickB38_operator L Kstar hL hJoint x -
      fp81s21_wickB38_operator L Kstar hL hJoint y := by
  let r := fp81s21_wickB38_choose μ x
  let s := fp81s21_wickB38_choose μ y
  let w := fp81s21_wickB22_concatFunction r.u s.u
  let a := fp81s21_wickB22_concatCoeff r.c s.c
  let hw := fp81s21_wickB36_concat_memLp r.u r.hu s.u s.hu
  have hkern : fp81s21_wickG_finite_rank_kernel w a =
      fp81s21_wickG_finite_rank_kernel r.u r.c - fp81s21_wickG_finite_rank_kernel s.u s.c :=
    fp81s21_wickB35_kernel_concat r.u s.u r.c s.c
  have hk : MemLp (fp81s21_wickG_finite_rank_kernel w a) 2 (μ.prod μ) := by
    rw [hkern]; exact r.hk.sub s.hk
  have heq : ((x - y : fp81s21_wickB32_finiteRankSubmodule μ) : Lp ℝ 2 (μ.prod μ)) =
      hk.toLp (fp81s21_wickG_finite_rank_kernel w a) := by
    change (x : Lp ℝ 2 (μ.prod μ)) - y = _
    calc
      _ = r.hk.toLp _ - s.hk.toLp _ := congrArg₂ (fun u v : Lp ℝ 2 (μ.prod μ) => u - v) r.eq_class s.eq_class
      _ = (r.hk.sub s.hk).toLp _ := (MemLp.toLp_sub r.hk s.hk).symm
      _ = hk.toLp _ := MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun z => (congrFun hkern z).symm)
  rw [fp81s21_wickB38_operator_eq L Kstar hL hJoint (x-y) w hw a hk heq]
  exact fp81s21_wickB36_polynomialLp_concat L Kstar hL hJoint r.u r.hu s.u s.hu r.c s.c

theorem fp81s21_wickB39_operator_smul
    (a : ℝ) (x : fp81s21_wickB32_finiteRankSubmodule μ) :
    fp81s21_wickB38_operator L Kstar hL hJoint (a • x) =
      a • fp81s21_wickB38_operator L Kstar hL hJoint x := by
  let r := fp81s21_wickB38_choose μ x
  have hkern : fp81s21_wickG_finite_rank_kernel r.u (fun i j => a * r.c i j) =
      a • fp81s21_wickG_finite_rank_kernel r.u r.c :=
    fp81s21_wickB35_kernel_smul r.u r.c a
  have hk : MemLp (fp81s21_wickG_finite_rank_kernel r.u (fun i j => a * r.c i j))
      2 (μ.prod μ) := by rw [hkern]; exact r.hk.const_smul a
  have heq : ((a • x : fp81s21_wickB32_finiteRankSubmodule μ) : Lp ℝ 2 (μ.prod μ)) =
      hk.toLp (fp81s21_wickG_finite_rank_kernel r.u (fun i j => a * r.c i j)) := by
    change a • (x : Lp ℝ 2 (μ.prod μ)) = _
    calc
      _ = a • r.hk.toLp _ := congrArg (fun z : Lp ℝ 2 (μ.prod μ) => a • z) r.eq_class
      _ = (r.hk.const_smul a).toLp _ := (MemLp.toLp_const_smul a r.hk).symm
      _ = hk.toLp _ := MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun z => (congrFun hkern z).symm)
  rw [fp81s21_wickB38_operator_eq L Kstar hL hJoint (a • x) r.u r.hu _ hk heq]
  exact fp81s21_wickB36_polynomialLp_smul L Kstar hL hJoint r.u r.hu r.c a

/-- The half-Wick polynomial assignment as a linear map on the finite-rank span. -/
def fp81s21_wickB39_linear : fp81s21_wickB32_finiteRankSubmodule μ →ₗ[ℝ] Lp ℝ 2 P where
  toFun := fp81s21_wickB38_operator L Kstar hL hJoint
  map_add' x y := by
    have h := fp81s21_wickB39_operator_sub L Kstar hL hJoint x (-y)
    have hy : (-1 : ℝ) • y = -y := by
      ext
      simp
    have hn : fp81s21_wickB38_operator L Kstar hL hJoint (-y) =
        -fp81s21_wickB38_operator L Kstar hL hJoint y := by
      simpa only [hy, neg_one_smul] using fp81s21_wickB39_operator_smul L Kstar hL hJoint (-1) y
    rw [hn] at h
    simpa using h
  map_smul' a x := fp81s21_wickB39_operator_smul L Kstar hL hJoint a x

theorem fp81s21_wickB39_linear_bound (x : fp81s21_wickB32_finiteRankSubmodule μ) :
    ‖fp81s21_wickB39_linear L Kstar hL hJoint x‖ ≤
      Kstar ^ 2 / Real.sqrt 2 * ‖(x : Lp ℝ 2 (μ.prod μ))‖ := by
  let r := fp81s21_wickB38_choose μ x
  change ‖fp81s21_wickB22_polynomialLp L Kstar hL hJoint r.u r.hu r.c‖ ≤ _
  calc
    _ ≤ Kstar ^ 2 / Real.sqrt 2 * ‖r.hk.toLp (fp81s21_wickG_finite_rank_kernel r.u r.c)‖ :=
      fp81s21_wickB34_polynomialLp_bound L Kstar hL hJoint r.u r.hu r.c r.hk
    _ = _ := congrArg (fun z : Lp ℝ 2 (μ.prod μ) => Kstar ^ 2 / Real.sqrt 2 * ‖z‖) r.eq_class.symm

#print axioms fp81s21_wickB39_operator_sub
#print axioms fp81s21_wickB39_operator_smul
#print axioms fp81s21_wickB39_linear
#print axioms fp81s21_wickB39_linear_bound

end HRS.Fp81.S21
end
