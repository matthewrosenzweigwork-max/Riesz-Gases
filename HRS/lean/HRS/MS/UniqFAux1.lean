import HRS.MS.UniqQAux9
import HRS.MS.OrbFeatTie

/-!
# UNIQ-F (uniqueness of classical adjoint solutions for `fixedEqCoeff`), part 1: SCOPE and the nonlocal term for general slices

**Target** (`UniqFTie`): for the frozen S5.7 coefficient `fixedEqCoeff b.s b.M b.Q ν c ρ` (drift `-Qx + c_t(x)`, matrix `M`, viscosity
`ν ∈ [0, ν*]`, time-dependent probability densities `ρ_t` with weighted bounds, `FixedEqFcauHyp`), two `IsClassicalAdjointW` solutions
with the same terminal datum agree on `[0,t]`; hence `propagatorW (fixedEqCoeff ..) r t φ` is the classical solution.

**Scope (what each engine covers).**

1. *`ν > 0`, ANY matrix `M`, ANY regime/force data, time-dependent bounded `c_t`, time-dependent `ρ_t`* (`uniqf_unique_pos`, UniqFAux2-3, `uniqf_unique_of_pos` UniqFAux4):
   the maximum-principle route of `UNIQQ` (`HRS/MS/UniqQAux1..9`) is abstract in the source
   `S = ⟨c_r, ∇u⟩ - N_r(∇u)` (`UqSol`, `uniqq_step`, `uniqq_window`, `uniqq_propagate` do not mention `c`, `ρ`).  Only three things
   used the data: (a) the bound `|N(∇u)| ≤ K (‖∇u‖_∞ + [∇u]_β)`, which needs `ρ` only through `sup|ρ|`, `sup|∇ρ|`, `‖ρ‖_{L¹}`
   (`uniqf_nl_bound`; `K` is uniform over `r` when these three numbers are, which the weighted density bounds give); (b) linearity of
   `ulNL` on `C_b²` (`uniqf_nl_sub`; needs `ρ ∈ C¹ ∩ L¹`); (c) the window length, which depends on `sup_r |c_r|` and on `K` only.
   The regime of `FixedEqFcauHyp` is NOT used (the Gaussian smoothing of `νΔ` absorbs the nonlocal term of order `s + 2 - d < 2`).
2. *`ν = 0` with the tie `c_t = M ∇g*ρ_t - c₀`* (`uniqf_unique_tie`, UniqFAux5; the bridge from the slice hypotheses of `fixed_equation` is UniqFAux4): then `-Qx + c_t = M∇g*ρ_t - ∇V`, `V = ½xᵀQx + c₀·x`,
   and `fixedEqCoeff = D.coeff ρ` for `D = ⟨s, M, V, ν⟩ : WholeDyn d`, so `Fcau.propagatorW_unique_star` (every regime of
   `FixedEqFcauHyp.regime`: R1, R2a, R2c, R3, `LpCase` at `p = 2` through `lpcase_two_cover`) applies.
3. *`ν = 0` with a FREE bounded `c_t`*: NOT covered.  Maximum principle: no smoothing.  F-CAU engine (`uloc_uniqueness_core_star`, about
   160 files `UniqC*, UniqE*, UniqN*, UniqG2*, UniqM*, UniqT*, Flow*, Bilip*, Star*`, about 20k lines, `WholeDyn`-parametrised with ~700
   occurrences of `D`/`meanFieldDriftW`): generalising it from `WholeDyn` to an advecting drift is mathematically unchanged but mechanical
   (estimated 8-10k lines of new files), beyond the packet.  For `s ≤ d - 2` a weighted `L²` energy argument would work (not done);
   for `s > d - 2` (R2a/R2c/R3-at-zero/`UlocStarRegime`) dissipation of the nonlocal term is needed (`SymNonpos M`), i.e. the engine.

**Proposed minimal statement change for `fixed_equation`** (not applied here): add to `FixedEqFcauHyp` the field
`uniq_data : 0 < ν ∨ ∃ c₀ : Euc d, ∀ t ∈ Set.Icc 0 b.T, ∀ x, c t x = Torus.matVec b.M (convGradConvW (rieszKernelGrad d b.s) (ρ t) x) - c₀`
(true for the mean-field coefficients of `WholeSetup`, where `c_N^t = M∇g*ρ_N^t - c₀`; the weaker alternative `0 < ν` alone excludes the
zero-viscosity limit equation).

**Final assembly**: `UniqFTie` (`uniqf_unique`, `uniqf_propagatorW_eq`, `uniqf_unique_fe`, `uniqf_propagatorW_eq_fe`; `UqfCase b ν c ρ := 0 < ν ∨ UqfTie b c ρ`).

**This file**: the nonlocal term `ulNL s M ψ` for a slice `ψ` that is only `C¹ ∩ L¹` with three numerical bounds (`UqfGood`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff RealInnerProductSpace Matrix MatrixOrder

namespace HRS.MS.UniqF

open HRS HRS.Whole HRS.MS.Ul HRS.MS.Lc HRS.MS.UniqN2a HRS.MS.UniqQ

variable {d : ℕ}

/-- a slice `ψ` of class `C¹`, integrable, `|ψ| ≤ B`, `‖∇ψ‖ ≤ L`, `∫|ψ| ≤ I` -/
structure UqfGood (ψ : Euc d → ℝ) (B L I : ℝ) : Prop where
  c1 : ContDiff ℝ 1 ψ
  int : Integrable ψ
  bB : ∀ y, |ψ y| ≤ B
  bL : ∀ y, ‖fderiv ℝ ψ y‖ ≤ L
  bI : ∫ y, |ψ y| ≤ I

theorem UqfGood.B_nonneg {ψ : Euc d → ℝ} {B L I : ℝ} (h : UqfGood ψ B L I) : 0 ≤ B :=
  (abs_nonneg _).trans (h.bB 0)

theorem UqfGood.L_nonneg {ψ : Euc d → ℝ} {B L I : ℝ} (h : UqfGood ψ B L I) : 0 ≤ L :=
  (norm_nonneg _).trans (h.bL 0)

theorem UqfGood.I_nonneg {ψ : Euc d → ℝ} {B L I : ℝ} (h : UqfGood ψ B L I) : 0 ≤ I :=
  (integral_nonneg fun _ => abs_nonneg _).trans h.bI

theorem uniqf_F_contDiff {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 1 ψ) (M : Matrix (Fin d) (Fin d) ℝ) {u : Euc d → ℝ}
    (hu : ContDiff ℝ 2 u) (j : Fin d) :
    ContDiff ℝ 1 (fun y => ψ y * fderiv ℝ u y (ul1w M j)) := by
  have hd : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  exact hψ.mul (hd.clm_apply contDiff_const)

theorem uniqf_F_int {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψi : Integrable ψ) (M : Matrix (Fin d) (Fin d) ℝ)
    {u : Euc d → ℝ} (hu : ContDiff ℝ 2 u) {G : ℝ} (hG : ∀ y, ‖gradient u y‖ ≤ G) (j : Fin d) :
    Integrable (fun y => ψ y * fderiv ℝ u y (ul1w M j)) := by
  refine (hψi.abs.mul_const (G * ‖ul1w M j‖)).mono'
    (uniqf_F_contDiff hψ M hu j).continuous.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have hA : |fderiv ℝ u y (ul1w M j)| ≤ G * ‖ul1w M j‖ := by
    rw [← uniqq_grad_inner]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hG y) (norm_nonneg _))
  exact mul_le_mul_of_nonneg_left hA (abs_nonneg _)

/-- **the nonlocal term for a general good slice is controlled by `∇u` in `C^β`** (port of `uniqq_nl_bound`) -/
theorem uniqf_nl_bound {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hβs : s + 1 - d < β) (M : Matrix (Fin d) (Fin d) ℝ) (Bψ Lψ Iψ : ℝ) :
    ∃ KN : ℝ, 0 ≤ KN ∧ ∀ {ψ : Euc d → ℝ}, UqfGood ψ Bψ Lψ Iψ →
      ∀ {u : Euc d → ℝ}, ContDiff ℝ 2 u → ∀ {G H : ℝ}, 0 ≤ G → 0 ≤ H →
      (∀ y, ‖gradient u y‖ ≤ G) → (∀ x a, ‖gradient u (x + a) - gradient u x‖ ≤ H * ‖a‖ ^ β) →
      ∀ x, |ulNL s M ψ u x| ≤ KN * (G + H) := by
  set Ib : ℝ := ∫ z, ballF (d := d) (s + 1 - β) z with hIb
  have hIb0 : 0 ≤ Ib := integral_nonneg fun z => ballF_nonneg _ _
  have hm1 : (0 : ℝ) ≤ max 1 s := le_trans zero_le_one (le_max_left _ _)
  set KN : ℝ := ∑ j : Fin d, (max 1 s * (|Bψ| + |Lψ|) * ‖ul1w M j‖ * Ib +
    max 1 s * 8 ^ (s + 1) * |Iψ| * ‖ul1w M j‖) with hKN
  have hKN0 : 0 ≤ KN := Finset.sum_nonneg fun j _ => by positivity
  refine ⟨KN, hKN0, fun {ψ} hψ {u} hu {G H} hG hH hGb hHb x => ?_⟩
  have hBψ0 := hψ.B_nonneg
  have hLψ0 := hψ.L_nonneg
  have hIψ0 := hψ.I_nonneg
  have hψd := hψ.c1
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  set F : Fin d → Euc d → ℝ := fun j y => ψ y * fderiv ℝ u y (ul1w M j) with hF
  have hFc : ∀ j, ContDiff ℝ 1 (F j) := fun j => uniqf_F_contDiff hψd M hu j
  have hA : ∀ j y, |fderiv ℝ u y (ul1w M j)| ≤ G * ‖ul1w M j‖ := by
    intro j y
    rw [← uniqq_grad_inner]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hGb y) (norm_nonneg _))
  have hFb : ∀ j y, |F j y| ≤ |ψ y| * (G * ‖ul1w M j‖) := fun j y => by
    simp only [hF]; rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hA j y) (abs_nonneg _)
  have hFi : ∀ j, Integrable (F j) := fun j => uniqf_F_int hψd hψ.int M hu hGb j
  have hFL1 : ∀ j, ∫ y, |F j y| ≤ Iψ * (G * ‖ul1w M j‖) := fun j => by
    calc ∫ y, |F j y| ≤ ∫ y, |ψ y| * (G * ‖ul1w M j‖) :=
          integral_mono (hFi j).abs (hψ.int.abs.mul_const _) (hFb j)
      _ = (∫ y, |ψ y|) * (G * ‖ul1w M j‖) := integral_mul_const _ _
      _ ≤ Iψ * (G * ‖ul1w M j‖) :=
          mul_le_mul_of_nonneg_right hψ.bI (by positivity)
  have hHol : ∀ j y, ‖x - y‖ ≤ 1 / 4 →
      |F j y - F j x| ≤ ((Bψ * H + Lψ * G) * ‖ul1w M j‖) * ‖x - y‖ ^ β := by
    intro j y hxy
    have hr1 : ‖x - y‖ ≤ 1 := by linarith
    have hself := uniqq_self_le_rpow (norm_nonneg (x - y)) hr1 hβ1.le
    have h1 : |fderiv ℝ u y (ul1w M j) - fderiv ℝ u x (ul1w M j)| ≤ H * ‖x - y‖ ^ β * ‖ul1w M j‖ := by
      have := hHb x (y - x)
      rw [add_sub_cancel, norm_sub_rev y x] at this
      rw [← uniqq_grad_inner, ← uniqq_grad_inner, ← inner_sub_left]
      exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right this (norm_nonneg _))
    have h2 : |ψ y - ψ x| ≤ Lψ * ‖x - y‖ := by
      have := ul4_lip_of_cb hψd hψ.bL y x
      rwa [norm_sub_rev y x] at this
    have e : F j y - F j x = ψ y * (fderiv ℝ u y (ul1w M j) - fderiv ℝ u x (ul1w M j)) +
        (ψ y - ψ x) * fderiv ℝ u x (ul1w M j) := by simp only [hF]; ring
    rw [e]
    calc _ ≤ |ψ y * (fderiv ℝ u y (ul1w M j) - fderiv ℝ u x (ul1w M j))| +
          |(ψ y - ψ x) * fderiv ℝ u x (ul1w M j)| := abs_add_le _ _
      _ = |ψ y| * |fderiv ℝ u y (ul1w M j) - fderiv ℝ u x (ul1w M j)| +
          |ψ y - ψ x| * |fderiv ℝ u x (ul1w M j)| := by rw [abs_mul, abs_mul]
      _ ≤ Bψ * (H * ‖x - y‖ ^ β * ‖ul1w M j‖) + (Lψ * ‖x - y‖) * (G * ‖ul1w M j‖) := by
          gcongr
          · exact hψ.bB y
          · exact hA j x
      _ ≤ Bψ * (H * ‖x - y‖ ^ β * ‖ul1w M j‖) + (Lψ * ‖x - y‖ ^ β) * (G * ‖ul1w M j‖) := by
          gcongr
      _ = _ := by ring
  have hcomp : ∀ j, (convGradConvW (rieszKernelGrad d s) (F j) x) j =
      ∫ y, (if ‖x - y‖ ≤ 1 / 4 then (F j y - F j x) * kap d s j (x - y)
        else F j y * kap d s j (x - y)) := fun j => ul1_conv_comp hs0 hsd j (hFc j) (hFi j) x
  have hrepr : ulNL s M ψ u x = ∑ j, (convGradConvW (rieszKernelGrad d s) (F j) x) j := by
    unfold ulNL
    simp only [ul1_matVec]
    rfl
  rw [hrepr]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ j ∈ Finset.univ, |(convGradConvW (rieszKernelGrad d s) (F j) x) j| ≤
      (max 1 s * (|Bψ| + |Lψ|) * ‖ul1w M j‖ * Ib + max 1 s * 8 ^ (s + 1) * |Iψ| * ‖ul1w M j‖) * (G + H) := by
    intro j _
    rw [hcomp j]
    have hHF : 0 ≤ (Bψ * H + Lψ * G) * ‖ul1w M j‖ := by positivity
    have h1 := uniqq_cc_bound hs0 hsd hβ0 hβ1 hβs j (hFc j) (hFi j) hHF x (hHol j)
    refine h1.trans ?_
    have hBa : Bψ = |Bψ| := (abs_of_nonneg hBψ0).symm
    have hLa : Lψ = |Lψ| := (abs_of_nonneg hLψ0).symm
    have hIa : Iψ = |Iψ| := (abs_of_nonneg hIψ0).symm
    have h2 : max 1 s * 8 ^ (s + 1) * ∫ y, |F j y| ≤ max 1 s * 8 ^ (s + 1) * (Iψ * (G * ‖ul1w M j‖)) :=
      mul_le_mul_of_nonneg_left (hFL1 j) (by positivity)
    have h3 : max 1 s * ((Bψ * H + Lψ * G) * ‖ul1w M j‖) * Ib ≤
        max 1 s * (|Bψ| + |Lψ|) * ‖ul1w M j‖ * Ib * (G + H) := by
      have : (Bψ * H + Lψ * G) ≤ (|Bψ| + |Lψ|) * (G + H) := by
        rw [← hBa, ← hLa]
        nlinarith [mul_nonneg hBψ0 hG, mul_nonneg hLψ0 hH]
      have hw := norm_nonneg (ul1w M j)
      calc max 1 s * ((Bψ * H + Lψ * G) * ‖ul1w M j‖) * Ib
          = max 1 s * ‖ul1w M j‖ * Ib * (Bψ * H + Lψ * G) := by ring
        _ ≤ max 1 s * ‖ul1w M j‖ * Ib * ((|Bψ| + |Lψ|) * (G + H)) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
    have h4 : max 1 s * 8 ^ (s + 1) * (Iψ * (G * ‖ul1w M j‖)) ≤
        max 1 s * 8 ^ (s + 1) * |Iψ| * ‖ul1w M j‖ * (G + H) := by
      have hw := norm_nonneg (ul1w M j)
      rw [← hIa]
      calc max 1 s * 8 ^ (s + 1) * (Iψ * (G * ‖ul1w M j‖))
          = max 1 s * 8 ^ (s + 1) * Iψ * ‖ul1w M j‖ * G := by ring
        _ ≤ max 1 s * 8 ^ (s + 1) * Iψ * ‖ul1w M j‖ * (G + H) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    calc _ ≤ max 1 s * ((Bψ * H + Lψ * G) * ‖ul1w M j‖) * Ib +
          max 1 s * 8 ^ (s + 1) * (Iψ * (G * ‖ul1w M j‖)) := by
          have : max 1 s * ((Bψ * H + Lψ * G) * ‖ul1w M j‖) * Ib =
              max 1 s * (Bψ * H + Lψ * G) * ‖ul1w M j‖ * Ib := by ring
          nlinarith [h2]
      _ ≤ _ := by nlinarith [h3, h4]
  calc _ ≤ ∑ j : Fin d, (max 1 s * (|Bψ| + |Lψ|) * ‖ul1w M j‖ * Ib +
        max 1 s * 8 ^ (s + 1) * |Iψ| * ‖ul1w M j‖) * (G + H) := Finset.sum_le_sum hterm
    _ = KN * (G + H) := by rw [hKN, Finset.sum_mul]

/-- linearity of the nonlocal term on `C²` functions with bounded gradient, for a good slice -/
theorem uniqf_nl_sub {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M : Matrix (Fin d) (Fin d) ℝ)
    {ψ : Euc d → ℝ} {B L I : ℝ} (hψ : UqfGood ψ B L I)
    {u v : Euc d → ℝ} (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) {G : ℝ}
    (hGu : ∀ y, ‖gradient u y‖ ≤ G) (hGv : ∀ y, ‖gradient v y‖ ≤ G) (x : Euc d) :
    ulNL s M ψ (fun y => u y - v y) x = ulNL s M ψ u x - ulNL s M ψ v x := by
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by norm_num)
  set Fu : Fin d → Euc d → ℝ := fun j y => ψ y * fderiv ℝ u y (ul1w M j) with hFu
  set Fv : Fin d → Euc d → ℝ := fun j y => ψ y * fderiv ℝ v y (ul1w M j) with hFv
  have hFuc : ∀ j, ContDiff ℝ 1 (Fu j) := fun j => uniqf_F_contDiff hψ.c1 M hu j
  have hFvc : ∀ j, ContDiff ℝ 1 (Fv j) := fun j => uniqf_F_contDiff hψ.c1 M hv j
  have hFui : ∀ j, Integrable (Fu j) := fun j => uniqf_F_int hψ.c1 hψ.int M hu hGu j
  have hFvi : ∀ j, Integrable (Fv j) := fun j => uniqf_F_int hψ.c1 hψ.int M hv hGv j
  have hFw : ∀ j, (fun y => ψ y * fderiv ℝ (fun y => u y - v y) y (ul1w M j)) = fun y => Fu j y - Fv j y := by
    intro j; funext y
    rw [fderiv_fun_sub (hu1.differentiable one_ne_zero y) (hv1.differentiable one_ne_zero y)]
    simp only [hFu, hFv, ContinuousLinearMap.sub_apply]; ring
  have key : ∀ j, (convGradConvW (rieszKernelGrad d s) (fun y => Fu j y - Fv j y) x) j =
      (convGradConvW (rieszKernelGrad d s) (Fu j) x) j - (convGradConvW (rieszKernelGrad d s) (Fv j) x) j := by
    intro j
    rw [ul1_conv_comp hs0 hsd j ((hFuc j).sub (hFvc j)) ((hFui j).sub (hFvi j)) x,
      ul1_conv_comp hs0 hsd j (hFuc j) (hFui j) x, ul1_conv_comp hs0 hsd j (hFvc j) (hFvi j) x,
      ← integral_sub (ul1_comp_integrable hs0 hsd j (hFuc j) (hFui j) x)
        (ul1_comp_integrable hs0 hsd j (hFvc j) (hFvi j) x)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    by_cases h : ‖x - y‖ ≤ 1 / 4 <;> simp only [h, ↓reduceIte] <;> ring
  unfold ulNL
  simp only [ul1_matVec]
  simp_rw [hFw]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => key j

end HRS.MS.UniqF
