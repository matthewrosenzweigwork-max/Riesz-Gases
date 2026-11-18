import HRS.MS.SA16RHeat13
import HRS.MS.SA16SNl1

/-!
# S.A.16 (SA16Y5) Gd1: the second derivatives of the heat kernel in `L^1` (K1, Gaussian part)

`sa16y5_ddg d a i j = ∂_i ∂_j g_a = (-δ_ij/(2a) + z_i z_j/(4a²)) g_a` (`sa16y5_dg_fderiv`), `|ddg| ≤ (1/(2a)) g_a + (4/3)(4/3)^d a^{-1} g_{16a/9}`
(Gaussian domination as for `sa16r_dg_pointwise`), hence `∫ |ddg| ≤ (1/2 + (4/3)(4/3)^d) a^{-1}` (`sa16y5_ddg_L1`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA

section Gd1
variable {d : ℕ}

def sa16y5_ddg (d : ℕ) (a : ℝ) (i j : Fin d) (z : Euc d) : ℝ :=
  (-(if i = j then (1 : ℝ) else 0) / (2 * a) + z i * z j / (4 * a ^ 2)) * sa16r_g d a z

lemma sa16y5_dg_fderiv {a : ℝ} (ha : 0 < a) (i j : Fin d) (z : Euc d) :
    fderiv ℝ (sa16r_dg d a j) z (EuclideanSpace.single i 1) = sa16y5_ddg d a i j z := by
  have h1 : HasFDerivAt (fun z : Euc d => -(z j) / (2 * a))
      ((-1 / (2 * a)) • (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ)) z := by
    have := ((EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).hasFDerivAt (x := z)).const_smul (-1 / (2 * a))
    refine this.congr_fderiv rfl |>.congr_of_eventuallyEq ?_
    exact Eventually.of_forall fun y => by simp [smul_eq_mul]; ring
  have hg : DifferentiableAt ℝ (sa16r_g d a) z := (sa16r_g_contDiff (a := a)).differentiable (by simp) z
  have hf : DifferentiableAt ℝ (fun z : Euc d => -(z j) / (2 * a)) z := h1.differentiableAt
  have hdg : sa16r_dg d a j = fun z => (-(z j) / (2 * a)) * sa16r_g d a z := rfl
  rw [hdg, fderiv_fun_mul hf hg, h1.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [sa16r_g_fderiv ha z i]
  have e1 : (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ) (EuclideanSpace.single i 1) = if i = j then 1 else 0 := by
    simp [EuclideanSpace.proj, PiLp.single_apply, eq_comm]
  rw [e1]
  simp only [sa16r_dg, sa16y5_ddg]
  by_cases h : i = j
  · subst h; simp; field_simp; ring
  · simp [h]; field_simp; ring

lemma sa16y5_ddg_cont (a : ℝ) (i j : Fin d) : Continuous (sa16y5_ddg d a i j) := by
  unfold sa16y5_ddg
  have h1 : Continuous (fun z : Euc d => z i) := (continuous_apply i).comp (PiLp.continuous_ofLp 2 (fun _ : Fin d => ℝ))
  have h2 : Continuous (fun z : Euc d => z j) := (continuous_apply j).comp (PiLp.continuous_ofLp 2 (fun _ : Fin d => ℝ))
  exact ((continuous_const.add ((h1.mul h2).div_const _))).mul (sa16r_g_contDiff (a := a)).continuous

lemma sa16y5_zg_le {a : ℝ} (ha : 0 < a) (i : Fin d) (z : Euc d) :
    |z i| * sa16r_g d a z ≤ 2 * a * (a ^ (-(1 / 2 : ℝ)) * (4 / 3 : ℝ) ^ ((d : ℝ) / 2) * sa16r_g d (4 * a / 3) z) := by
  have h := sa16r_dg_pointwise ha i z
  have hg := sa16r_g_pos ha z
  have e : |sa16r_dg d a i z| = |z i| / (2 * a) * sa16r_g d a z := by
    rw [sa16r_dg, abs_mul, abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * a), abs_of_pos hg]
  rw [e] at h
  have : |z i| * sa16r_g d a z = 2 * a * (|z i| / (2 * a) * sa16r_g d a z) := by field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left h (by positivity)

lemma sa16y5_ddg_pointwise {a : ℝ} (ha : 0 < a) (i j : Fin d) (z : Euc d) :
    |sa16y5_ddg d a i j z| ≤ (1 / (2 * a)) * sa16r_g d a z +
      (4 / 3 : ℝ) * ((4 / 3 : ℝ) ^ d) * a⁻¹ * sa16r_g d (16 * a / 9) z := by
  set c : ℝ := (4 / 3 : ℝ) ^ ((d : ℝ) / 2) with hc
  have hc0 : 0 < c := by positivity
  have hcc : c * c = (4 / 3 : ℝ) ^ d := by
    rw [hc, ← Real.rpow_add (by norm_num), ← two_mul]
    have : 2 * ((d : ℝ) / 2) = (d : ℝ) := by ring
    rw [this, Real.rpow_natCast]
  set u : ℝ := a ^ (-(1 / 2 : ℝ)) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos ha _
  have huu : u * u * a = 1 := by
    rw [hu, ← Real.rpow_add ha]
    have : -(1 / 2 : ℝ) + -(1 / 2) = -1 := by ring
    rw [this, Real.rpow_neg_one]
    field_simp
  have h43 : 0 < 4 * a / 3 := by positivity
  have hu' : (4 * a / 3) ^ (-(1 / 2 : ℝ)) ≤ u := by
    rw [hu]
    exact Real.rpow_le_rpow_of_nonpos ha (by linarith) (by norm_num)
  have hg := sa16r_g_pos ha z
  have hg1 := sa16r_g_pos h43 z
  -- |z_i z_j| g_a ≤ ...
  have h1 := sa16y5_zg_le ha j z
  have h2 := sa16y5_zg_le h43 i z
  have e16 : 4 * (4 * a / 3) / 3 = 16 * a / 9 := by ring
  rw [e16] at h2
  have hzz : |z i| * |z j| * sa16r_g d a z ≤ 2 * a * (u * c) * (2 * (4 * a / 3) * (u * c * sa16r_g d (16 * a / 9) z)) := by
    calc |z i| * |z j| * sa16r_g d a z = |z i| * (|z j| * sa16r_g d a z) := by ring
      _ ≤ |z i| * (2 * a * (u * c * sa16r_g d (4 * a / 3) z)) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = 2 * a * (u * c) * (|z i| * sa16r_g d (4 * a / 3) z) := by ring
      _ ≤ 2 * a * (u * c) * (2 * (4 * a / 3) * ((4 * a / 3) ^ (-(1 / 2 : ℝ)) * c * sa16r_g d (16 * a / 9) z)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ 2 * a * (u * c) * (2 * (4 * a / 3) * (u * c * sa16r_g d (16 * a / 9) z)) := by
          have hg2 := sa16r_g_pos (by positivity : (0 : ℝ) < 16 * a / 9) z
          gcongr
  unfold sa16y5_ddg
  have habs : |(-(if i = j then (1 : ℝ) else 0) / (2 * a) + z i * z j / (4 * a ^ 2)) * sa16r_g d a z| ≤
      (1 / (2 * a)) * sa16r_g d a z + |z i| * |z j| * sa16r_g d a z / (4 * a ^ 2) := by
    rw [abs_mul, abs_of_pos hg]
    have h3 : |(-(if i = j then (1 : ℝ) else 0) / (2 * a) + z i * z j / (4 * a ^ 2))| ≤
        1 / (2 * a) + |z i| * |z j| / (4 * a ^ 2) := by
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * a)]
        split_ifs <;> simp
        positivity
      · rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * a ^ 2)]
    calc |(-(if i = j then (1 : ℝ) else 0) / (2 * a) + z i * z j / (4 * a ^ 2))| * sa16r_g d a z
        ≤ (1 / (2 * a) + |z i| * |z j| / (4 * a ^ 2)) * sa16r_g d a z := mul_le_mul_of_nonneg_right h3 hg.le
      _ = _ := by ring
  refine habs.trans ?_
  refine add_le_add le_rfl ?_
  have h4 : |z i| * |z j| * sa16r_g d a z / (4 * a ^ 2) ≤
      (2 * a * (u * c) * (2 * (4 * a / 3) * (u * c * sa16r_g d (16 * a / 9) z))) / (4 * a ^ 2) := by
    gcongr
  refine h4.trans (le_of_eq ?_)
  have : 2 * a * (u * c) * (2 * (4 * a / 3) * (u * c * sa16r_g d (16 * a / 9) z)) =
      (16 / 3) * a ^ 2 * (u * u) * (c * c) * sa16r_g d (16 * a / 9) z := by ring
  rw [this, hcc]
  have hua : u * u = a⁻¹ := by
    have := huu
    field_simp at this ⊢
    nlinarith
  rw [hua]
  field_simp
  ring

theorem sa16y5_ddg_L1 {a : ℝ} (ha : 0 < a) (i j : Fin d) :
    Integrable (sa16y5_ddg d a i j) ∧
      ∫ z, |sa16y5_ddg d a i j z| ≤ (1 / 2 + (4 / 3 : ℝ) * ((4 / 3 : ℝ) ^ d)) * a⁻¹ := by
  have h169 : 0 < 16 * a / 9 := by positivity
  have hint : Integrable (fun z : Euc d => (1 / (2 * a)) * sa16r_g d a z +
      (4 / 3 : ℝ) * ((4 / 3 : ℝ) ^ d) * a⁻¹ * sa16r_g d (16 * a / 9) z) :=
    ((sa16r_g_int ha).const_mul _).add ((sa16r_g_int h169).const_mul _)
  have hI : Integrable (sa16y5_ddg d a i j) :=
    hint.mono' (sa16y5_ddg_cont a i j).aestronglyMeasurable
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact sa16y5_ddg_pointwise ha i j z)
  refine ⟨hI, ?_⟩
  calc ∫ z, |sa16y5_ddg d a i j z| ≤ ∫ z : Euc d, ((1 / (2 * a)) * sa16r_g d a z +
        (4 / 3 : ℝ) * ((4 / 3 : ℝ) ^ d) * a⁻¹ * sa16r_g d (16 * a / 9) z) :=
        integral_mono hI.abs hint (fun z => sa16y5_ddg_pointwise ha i j z)
    _ = _ := by
        rw [integral_add ((sa16r_g_int ha).const_mul _) ((sa16r_g_int h169).const_mul _),
          integral_const_mul, integral_const_mul, sa16r_g_mass ha, sa16r_g_mass h169]
        field_simp

end Gd1

end HRS.Whole.AppendixA.Phase2SA16R
