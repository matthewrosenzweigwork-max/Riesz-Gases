import HRS.MS.WrRefMargAux3
import HRS.MS.WrMargBAux2
import HRS.MS.WrTr
import HRS.MS.WrFld
import HRS.Equilibrium.QuadraticVariance

/-!
# HRS.MS.WrQuadAux1 -- centered quadratic functional: resampling, rows, retained repulsion (WR-14a, part 1)

Packet WR-14a of `docs/WR_B_PLAN.md` (T12; TeX `euc-D-diagonal`, `euc-row-variance`, `euc-reference-quadratic`),
namespace `HRS.MS.Wr`, helper prefix `wr14a_`.  Euclidean port of `HRS/Equilibrium/QuadraticVariance.lean`
(`QuadWeak` and `QuadRow` parts) with `quadStat h ν X` replaced by `HRS.Whole.centeredPairFunctional h X ν`, the
torus envelope `singEnvelope` replaced by `1 + rieszWeight s` (`|h(x,y)| ≤ B (1 + W_s(x-y))` off the diagonal)
and the torus radial integrals replaced by the whole-space `wr13c_radial_J` / `wr3_row_bounds_real`
(row mass `wr3_lintegral_W_row`).  The generic (any measurable space `E`) lemmas `HRS.Quad.lintegral_pinned_succ`,
`HRS.Quad.second_moment_pinned`, `HRS.Quad.pinned_marginal_le_density` are reused, not re-proved.

Contents:
* `wr14a_D_eq_row_add_rest` (`D_N = (2/N²) row_i + rest_i`), `wr14a_evariance_quad_le` (Wu: `Var D_N ≤ (8/N⁴) ∑ E|row_i|²`);
* `wr14a_row_lintegral_le`, `wr14a_pair_lintegral_le`, `wr14a_quad_reference_le` (row second moments under the
  pinned weak ensemble, disintegration);
* `wr14a_tv_pin_le` (total-variation pin comparison);
* the envelope integrals of whole space: `wr14a_Hc_bound`, `wr14a_variance_integral_le` (retained repulsion),
  `wr14a_mean_one_le` (row mean: near part by bounded densities, far part by total variation).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MS.Wr

open HRS.External

variable {d : ℕ}

/-! ### The centered kernel and the row -/

/-- `H(x) = ∫ h(x,y) dπ(y)`. -/
def wr14a_Hc (h : Euc d → Euc d → ℝ) (π : Measure (Euc d)) (x : Euc d) : ℝ := ∫ y, h x y ∂π

/-- `h₀ = ∬ h dπ dπ`. -/
def wr14a_h0 (h : Euc d → Euc d → ℝ) (π : Measure (Euc d)) : ℝ := ∫ x, ∫ y, h x y ∂π ∂π

/-- The doubly centered kernel `h_c(x,y) = h(x,y) - H(x) - H(y) + h₀`. -/
def wr14a_cK (h : Euc d → Euc d → ℝ) (π : Measure (Euc d)) (x y : Euc d) : ℝ :=
  h x y - wr14a_Hc h π x - wr14a_Hc h π y + wr14a_h0 h π

/-- The row `∑_{j≠i} h_c(x_i,x_j) - H(x_i)` (TeX `euc-row-variance`). -/
def wr14a_row (h : Euc d → Euc d → ℝ) (π : Measure (Euc d)) {N : ℕ} (i : Fin N) (Y : Fin N → Euc d) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, wr14a_cK h π (Y i) (Y j) - wr14a_Hc h π (Y i)

/-- The part of `D_N` that does not depend on `x_i`. -/
def wr14a_rest (h : Euc d → Euc d → ℝ) (π : Measure (Euc d)) {N : ℕ} (i : Fin N) (Y : Fin N → Euc d) : ℝ :=
  (1 / (N : ℝ) ^ 2) * ∑ a ∈ Finset.univ.erase i, ∑ b ∈ (Finset.univ.erase i).erase a, h (Y a) (Y b)
    - 2 * ((N : ℝ) - 1) / (N : ℝ) ^ 2 * ∑ a ∈ Finset.univ.erase i, wr14a_Hc h π (Y a)
    + (1 - 2 * ((N : ℝ) - 1) / (N : ℝ) ^ 2) * wr14a_h0 h π

theorem wr14a_measurable_h_pair {h : Euc d → Euc d → ℝ} (hm : Measurable (Function.uncurry h)) {N : ℕ}
    (i j : Fin N) : Measurable fun X : Fin N → Euc d => h (X i) (X j) :=
  Measurable.comp (g := Function.uncurry h) hm (f := fun X : Fin N → Euc d => (X i, X j))
    ((measurable_pi_apply (X := fun _ : Fin N => Euc d) i).prodMk
      (measurable_pi_apply (X := fun _ : Fin N => Euc d) j))

theorem wr14a_measurable_h_x {h : Euc d → Euc d → ℝ} (hm : Measurable (Function.uncurry h)) (x : Euc d) :
    Measurable (h x) :=
  Measurable.comp (g := Function.uncurry h) hm (f := fun y : Euc d => (x, y))
    (measurable_const.prodMk measurable_id)

theorem wr14a_measurable_Hc {h : Euc d → Euc d → ℝ} (hm : Measurable (Function.uncurry h))
    (π : Measure (Euc d)) [SFinite π] : Measurable (wr14a_Hc h π) := by
  unfold wr14a_Hc
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := π)).measurable

theorem wr14a_measurable_D {h : Euc d → Euc d → ℝ} (hm : Measurable (Function.uncurry h))
    (π : Measure (Euc d)) [SFinite π] {N : ℕ} :
    Measurable (fun X : Fin N → Euc d => HRS.Whole.centeredPairFunctional h X π) := by
  unfold HRS.Whole.centeredPairFunctional
  have hH := wr14a_measurable_Hc hm π
  refine Measurable.add (Measurable.sub ?_ ?_) measurable_const
  · refine Measurable.const_mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_) _
    exact wr14a_measurable_h_pair hm i j
  · refine Measurable.const_mul (Measurable.const_mul (Finset.measurable_sum _ fun i _ => ?_) _) _
    exact hH.comp (measurable_pi_apply i)

theorem wr14a_measurable_row {h : Euc d → Euc d → ℝ} (hm : Measurable (Function.uncurry h))
    (π : Measure (Euc d)) [SFinite π] {N : ℕ} (i : Fin N) : Measurable (wr14a_row h π i) := by
  unfold wr14a_row wr14a_cK
  have hH := wr14a_measurable_Hc hm π
  refine Measurable.sub (Finset.measurable_sum _ fun j _ => ?_) (hH.comp (measurable_pi_apply i))
  refine Measurable.add (Measurable.sub (Measurable.sub ?_ (hH.comp (measurable_pi_apply i)))
    (hH.comp (measurable_pi_apply j))) measurable_const
  exact wr14a_measurable_h_pair hm i j

/-- Splitting the double sum over ordered pairs `a ≠ b` at the index `i`. -/
theorem wr14a_sum_sum_erase_split {N : ℕ} (i : Fin N) (f : Fin N → Fin N → ℝ) :
    ∑ a, ∑ b ∈ Finset.univ.erase a, f a b
      = ∑ b ∈ Finset.univ.erase i, f i b + ∑ a ∈ Finset.univ.erase i, f a i
        + ∑ a ∈ Finset.univ.erase i, ∑ b ∈ (Finset.univ.erase i).erase a, f a b :=
  HRS.Quad.sum_sum_erase_split i f

/-- **Omitted-diagonal identity** (TeX `euc-D-diagonal`), single-site form: for a symmetric kernel,
`D_N(h;π)(Y) = (2/N²) row_i(Y) + rest_i(Y)`. -/
theorem wr14a_D_eq_row_add_rest {h : Euc d → Euc d → ℝ} (hsym : ∀ x y, h x y = h y x)
    (π : Measure (Euc d)) {N : ℕ} (hN : 0 < N) (i : Fin N) (Y : Fin N → Euc d) :
    HRS.Whole.centeredPairFunctional h Y π = (2 / (N : ℝ) ^ 2) * wr14a_row h π i Y + wr14a_rest h π i Y := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold HRS.Whole.centeredPairFunctional wr14a_row wr14a_rest wr14a_cK wr14a_Hc wr14a_h0
  rw [wr14a_sum_sum_erase_split i (fun a b => h (Y a) (Y b))]
  have e1 : ∑ a ∈ Finset.univ.erase i, h (Y a) (Y i) = ∑ b ∈ Finset.univ.erase i, h (Y i) (Y b) :=
    Finset.sum_congr rfl fun a _ => hsym _ _
  rw [e1]
  have hcard : ((Finset.univ.erase i).card : ℝ) = (N : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp [Nat.cast_sub hN]
  have e2 : ∑ j ∈ Finset.univ.erase i, (h (Y i) (Y j) - ∫ y, h (Y i) y ∂π - ∫ y, h (Y j) y ∂π
      + ∫ x, ∫ y, h x y ∂π ∂π)
      = ∑ j ∈ Finset.univ.erase i, h (Y i) (Y j) - ((N : ℝ) - 1) * ∫ y, h (Y i) y ∂π
        - ∑ j ∈ Finset.univ.erase i, ∫ y, h (Y j) y ∂π + ((N : ℝ) - 1) * ∫ x, ∫ y, h x y ∂π ∂π := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul, hcard]
  rw [e2]
  have e3 : ∑ a, ∫ y, h (Y a) y ∂π = ∫ y, h (Y i) y ∂π + ∑ a ∈ Finset.univ.erase i, ∫ y, h (Y a) y ∂π :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  rw [e3]
  field_simp
  ring

theorem wr14a_rest_update {h : Euc d → Euc d → ℝ} (π : Measure (Euc d)) {N : ℕ} (i : Fin N)
    (Y : Fin N → Euc d) (z : Euc d) : wr14a_rest h π i (Function.update Y i z) = wr14a_rest h π i Y := by
  unfold wr14a_rest
  have h1 : ∀ a ∈ Finset.univ.erase i, Function.update Y i z a = Y a := fun a ha =>
    Function.update_of_ne (Finset.ne_of_mem_erase ha) _ _
  have h2 : ∑ a ∈ Finset.univ.erase i, ∑ b ∈ (Finset.univ.erase i).erase a,
        h (Function.update Y i z a) (Function.update Y i z b)
      = ∑ a ∈ Finset.univ.erase i, ∑ b ∈ (Finset.univ.erase i).erase a, h (Y a) (Y b) := by
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
    rw [h1 a ha, h1 b (Finset.mem_of_mem_erase hb)]
  have h3 : ∑ a ∈ Finset.univ.erase i, wr14a_Hc h π (Function.update Y i z a)
      = ∑ a ∈ Finset.univ.erase i, wr14a_Hc h π (Y a) :=
    Finset.sum_congr rfl fun a ha => by rw [h1 a ha]
  rw [h2, h3]

/-! ### Wu's inequality for the quadratic statistic -/

section Resample

variable {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

/-- **TeX `euc-row-variance`**: single-site resampling reduces the variance of `D_N(h;π)` under the weak
ensemble `R` to the second moments of the rows, `Var_R D_N ≤ (8/N⁴) ∑_i E_R |row_i|²`. -/
theorem wr14a_evariance_quad_le (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {N : ℕ} (hN0 : 0 < N)
    (hκ : weakKappa V β ≤ 1 / 2) {h : Euc d → Euc d → ℝ} (hm : Measurable (Function.uncurry h))
    (hsym : ∀ x y, h x y = h y x) (π : Measure (Euc d)) [IsProbabilityMeasure π] :
    evariance (fun X : Fin N → Euc d => HRS.Whole.centeredPairFunctional h X π)
        (pinnedLaw V (β / N) N (fun e : Empty => e.elim)) ≤
      ENNReal.ofReal (8 / (N : ℝ) ^ 4) * ∑ i, ∫⁻ Y, ‖wr14a_row h π i Y‖ₑ ^ 2
        ∂(pinnedLaw V (β / N) N (fun e : Empty => e.elim)) := by
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg N)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN0
  have hψ := isField_pinField V hlam (fun e : Empty => e.elim)
  set S := fieldSpec (V := V) hψ hlam N with hS
  have hSP : S.P = pinnedLaw V (β / N) N (fun e : Empty => e.elim) := rfl
  have hF : Measurable (fun X : Fin N → Euc d => HRS.Whole.centeredPairFunctional h X π) :=
    wr14a_measurable_D hm π
  have h1 := weak_resampling (B := Empty) V hβ hN0 (by simp) (fun e : Empty => e.elim) hκ _ hF
  refine h1.trans ?_
  have hper : ∀ i : Fin N, ∫⁻ x, evariance (fun z => HRS.Whole.centeredPairFunctional h (Function.update x i z) π)
      (siteKernel μ (pinnedDensity V (β / N) N (fun e : Empty => e.elim)) i x)
        ∂(pinnedLaw V (β / N) N (fun e : Empty => e.elim))
      ≤ ENNReal.ofReal (4 / (N : ℝ) ^ 4) * ∫⁻ Y, ‖wr14a_row h π i Y‖ₑ ^ 2
        ∂(pinnedLaw V (β / N) N (fun e : Empty => e.elim)) := by
    intro i
    have hG : ∀ x, siteKernel μ (pinnedDensity V (β / N) N (fun e : Empty => e.elim)) i x = S.G i x :=
      fun x => rfl
    have hrow := wr14a_measurable_row hm π (N := N) i
    have hpt : ∀ x, evariance (fun z => HRS.Whole.centeredPairFunctional h (Function.update x i z) π)
        (siteKernel μ (pinnedDensity V (β / N) N (fun e : Empty => e.elim)) i x)
        ≤ ∫⁻ z, ENNReal.ofReal (4 / (N : ℝ) ^ 4) * ‖wr14a_row h π i (Function.update x i z)‖ₑ ^ 2 ∂(S.G i x) := by
      intro x
      rw [hG]
      refine (evariance_le_lintegral_sub (S.G i x) (hF.comp (measurable_update x)).aestronglyMeasurable
        (wr14a_rest h π i x)).trans (le_of_eq ?_)
      refine lintegral_congr fun z => ?_
      have e1 := wr14a_D_eq_row_add_rest hsym π hN0 i (Function.update x i z)
      rw [wr14a_rest_update] at e1
      simp only [Function.comp]
      rw [e1, add_sub_cancel_right, HRS.Quad.enorm_sq_const_mul _ _ (by positivity)]
      congr 2
      field_simp
      norm_num
    calc _ ≤ ∫⁻ x, ∫⁻ z, ENNReal.ofReal (4 / (N : ℝ) ^ 4) * ‖wr14a_row h π i (Function.update x i z)‖ₑ ^ 2 ∂(S.G i x)
          ∂(pinnedLaw V (β / N) N (fun e : Empty => e.elim)) := lintegral_mono hpt
      _ = ∫⁻ Y, ENNReal.ofReal (4 / (N : ℝ) ^ 4) * ‖wr14a_row h π i Y‖ₑ ^ 2
          ∂(pinnedLaw V (β / N) N (fun e : Empty => e.elim)) := by
        rw [← hSP]
        exact S.invariant i (fun Y => ENNReal.ofReal (4 / (N : ℝ) ^ 4) * ‖wr14a_row h π i Y‖ₑ ^ 2)
          (measurable_const.mul (hrow.enorm.pow_const 2))
      _ = _ := by
        rw [lintegral_const_mul _ (hrow.enorm.pow_const 2)]
  calc 2 * ∑ i, ∫⁻ x, evariance (fun z => HRS.Whole.centeredPairFunctional h (Function.update x i z) π)
        (siteKernel μ (pinnedDensity V (β / N) N (fun e : Empty => e.elim)) i x)
          ∂(pinnedLaw V (β / N) N (fun e : Empty => e.elim))
      ≤ 2 * ∑ i : Fin N, (ENNReal.ofReal (4 / (N : ℝ) ^ 4) * ∫⁻ Y, ‖wr14a_row h π i Y‖ₑ ^ 2
          ∂(pinnedLaw V (β / N) N (fun e : Empty => e.elim))) := by
        gcongr with i _
        exact hper i
    _ = _ := by
        rw [← Finset.mul_sum, ← mul_assoc]
        congr 1
        rw [show (8 : ℝ) / (N : ℝ) ^ 4 = 2 * (4 / (N : ℝ) ^ 4) by ring,
          ENNReal.ofReal_mul (by norm_num)]
        simp

end Resample

/-! ### Disintegration: row and pair second moments under the pinned weak ensemble -/

section Row

variable {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

/-- **Row second moment** (pinned): if for every pin value `x` the variance integral
`∫ |h_c(x,y)|² e^{M'+βγ+ψ_x(y)} dμ(y) ≤ 𝒱` (with the retained pin factor inside `ψ_x`) and the mean
`|∑_k ∫ h_c(x,·) dπ^x_k - H(x)| ≤ 𝓜`, then `E_R |row_i|² ≤ 2n 𝒱 + 𝓜²`. -/
theorem wr14a_row_lintegral_le (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} [NeZero n]
    (hκ : weakKappa V β ≤ 1 / 2) {h : Euc d → Euc d → ℝ} (hm : Measurable (Function.uncurry h))
    (π : Measure (Euc d)) [IsProbabilityMeasure π] (i : Fin (n + 1)) {𝒱 : ℝ≥0∞} {𝓜 : ℝ}
    (hV : ∀ x, ∫⁻ y, ‖wr14a_cK h π x y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
        pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) y)) ∂μ ≤ 𝒱)
    (hM : ∀ x, |∑ k : Fin n, ∫ y, wr14a_cK h π x y ∂((pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) n
        (pinsWith (fun e : Empty => e.elim) x)).map (fun Y => Y k)) - wr14a_Hc h π x| ≤ 𝓜) :
    ∫⁻ Y, ‖wr14a_row h π i Y‖ₑ ^ 2 ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim))
      ≤ ENNReal.ofReal (2 * n) * 𝒱 + ENNReal.ofReal (𝓜 ^ 2) := by
  have hN0 : 0 < n + 1 := Nat.succ_pos n
  have hlam : 0 ≤ β / ((n + 1 : ℕ) : ℝ) := div_nonneg hβ (Nat.cast_nonneg _)
  have hΦ : Measurable fun Y : Fin (n + 1) → Euc d => ‖wr14a_row h π i Y‖ₑ ^ 2 :=
    (wr14a_measurable_row hm π i).enorm.pow_const 2
  rw [HRS.Quad.lintegral_pinned_succ V hlam (fun e : Empty => e.elim) i hΦ]
  have hx : ∀ x : Euc d, ∫⁻ y, ‖wr14a_row h π i (insertAt i x y)‖ₑ ^ 2
      ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) n (pinsWith (fun e : Empty => e.elim) x))
      ≤ ENNReal.ofReal (2 * n) * 𝒱 + ENNReal.ofReal (𝓜 ^ 2) := by
    intro x
    have hrow : ∀ y : Fin n → Euc d,
        wr14a_row h π i (insertAt i x y) = ∑ k, wr14a_cK h π x (y k) - wr14a_Hc h π x := by
      intro y
      unfold wr14a_row
      rw [insertAt_same, HRS.Quad.sum_erase_insertAt i x y (fun z => wr14a_cK h π x z)]
    simp_rw [hrow]
    have hcm : Measurable (wr14a_cK h π x) := by
      unfold wr14a_cK
      have hH := wr14a_measurable_Hc hm π
      exact ((wr14a_measurable_h_x hm x).sub measurable_const |>.sub hH).add measurable_const
    have hcard : n + Fintype.card (Option Empty) ≤ n + 1 := by simp
    refine (HRS.Quad.second_moment_pinned (B := Option Empty) V hβ (N := n + 1) hN0 hcard
      (pinsWith (fun e : Empty => e.elim) x) hκ hcm (wr14a_Hc h π x)).trans ?_
    refine add_le_add (mul_le_mul' le_rfl (hV x)) (ENNReal.ofReal_le_ofReal ?_)
    have := abs_le.1 (hM x)
    exact sq_le_sq' this.1 this.2
  calc ∫⁻ x, pinWeight V (β / ((n + 1 : ℕ) : ℝ)) (fun e : Empty => e.elim) n x *
        ∫⁻ y, ‖wr14a_row h π i (insertAt i x y)‖ₑ ^ 2
          ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) n (pinsWith (fun e : Empty => e.elim) x)) ∂μ
      ≤ ∫⁻ x, pinWeight V (β / ((n + 1 : ℕ) : ℝ)) (fun e : Empty => e.elim) n x *
        (ENNReal.ofReal (2 * n) * 𝒱 + ENNReal.ofReal (𝓜 ^ 2)) ∂μ :=
        lintegral_mono fun x => mul_le_mul' le_rfl (hx x)
    _ ≤ ENNReal.ofReal (2 * n) * 𝒱 + ENNReal.ofReal (𝓜 ^ 2) := by
        by_cases hC : ENNReal.ofReal (2 * n) * 𝒱 + ENNReal.ofReal (𝓜 ^ 2) = ⊤
        · rw [hC]; exact le_top
        · rw [lintegral_mul_const' _ _ hC, lintegral_pinWeight V hlam (fun e : Empty => e.elim) i (0 : Fin n),
            one_mul]

/-- `N Var_R[D_N(h;π)] ≤ (8/N²)(2n 𝒱 + 𝓜²)` from the row bounds. -/
theorem wr14a_quad_reference_le (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} [NeZero n]
    (hκ : weakKappa V β ≤ 1 / 2) {h : Euc d → Euc d → ℝ} (hm : Measurable (Function.uncurry h))
    (hsym : ∀ x y, h x y = h y x) (π : Measure (Euc d)) [IsProbabilityMeasure π] {𝒱 : ℝ≥0∞} {𝓜 : ℝ}
    (hV : ∀ x, ∫⁻ y, ‖wr14a_cK h π x y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
        pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) y)) ∂μ ≤ 𝒱)
    (hM : ∀ x, |∑ k : Fin n, ∫ y, wr14a_cK h π x y ∂((pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) n
        (pinsWith (fun e : Empty => e.elim) x)).map (fun Y => Y k)) - wr14a_Hc h π x| ≤ 𝓜) :
    ((n + 1 : ℕ) : ℝ≥0∞) * evariance (fun X : Fin (n + 1) → Euc d => HRS.Whole.centeredPairFunctional h X π)
        (pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim))
      ≤ ENNReal.ofReal (8 / ((n + 1 : ℕ) : ℝ) ^ 2) * (ENNReal.ofReal (2 * n) * 𝒱 + ENNReal.ofReal (𝓜 ^ 2)) := by
  have hN0 : 0 < n + 1 := Nat.succ_pos n
  have hN' : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hN0
  have h1 := wr14a_evariance_quad_le V hβ hN0 hκ hm hsym π
  have h2 : ∀ i : Fin (n + 1), ∫⁻ Y, ‖wr14a_row h π i Y‖ₑ ^ 2
      ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim))
      ≤ ENNReal.ofReal (2 * n) * 𝒱 + ENNReal.ofReal (𝓜 ^ 2) :=
    fun i => wr14a_row_lintegral_le V hβ hκ hm π i hV hM
  set Ω := ENNReal.ofReal (2 * n) * 𝒱 + ENNReal.ofReal (𝓜 ^ 2) with hΩ
  calc ((n + 1 : ℕ) : ℝ≥0∞) * evariance (fun X : Fin (n + 1) → Euc d => HRS.Whole.centeredPairFunctional h X π)
        (pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim))
      ≤ ((n + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (8 / ((n + 1 : ℕ) : ℝ) ^ 4) *
          ∑ i : Fin (n + 1), Ω) := by
        gcongr
        refine h1.trans ?_
        gcongr with i _
        exact h2 i
    _ = ENNReal.ofReal (8 / ((n + 1 : ℕ) : ℝ) ^ 2) * Ω := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have e : ((n + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((n + 1 : ℕ) : ℝ) := (ENNReal.ofReal_natCast _).symm
        rw [e, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hN'.le, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        field_simp

/-- **Pair second moment** under the weak ensemble (no smallness needed): by disintegration at
coordinate `a`, the pair `(y_a, y_b)` has second moment of `h` bounded by the per-pin integral. -/
theorem wr14a_pair_lintegral_le (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (a b : Fin (n + 1))
    (hab : a ≠ b) {h : Euc d → Euc d → ℝ} (hm : Measurable (Function.uncurry h)) {𝒲 : ℝ≥0∞}
    (hW : ∀ x, ∫⁻ z, ‖h x z‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
        pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) z)) ∂μ ≤ 𝒲) :
    ∫⁻ Y, ‖h (Y a) (Y b)‖ₑ ^ 2
      ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) ≤ 𝒲 := by
  have hN0 : 0 < n + 1 := Nat.succ_pos n
  have hlam : 0 ≤ β / ((n + 1 : ℕ) : ℝ) := div_nonneg hβ (Nat.cast_nonneg _)
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hab.symm
  have hΦ : Measurable fun Y : Fin (n + 1) → Euc d => ‖h (Y a) (Y b)‖ₑ ^ 2 :=
    ((wr14a_measurable_h_pair hm a b).enorm).pow_const 2
  rw [HRS.Quad.lintegral_pinned_succ V hlam (fun e : Empty => e.elim) a hΦ]
  have hx : ∀ x : Euc d, ∫⁻ y, ‖h (insertAt a x y a) (insertAt a x y b)‖ₑ ^ 2
      ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) n (pinsWith (fun e : Empty => e.elim) x)) ≤ 𝒲 := by
    intro x
    have e : ∀ y : Fin n → Euc d, ‖h (insertAt a x y a) (insertAt a x y b)‖ₑ ^ 2 = ‖h x (y k)‖ₑ ^ 2 := by
      intro y
      rw [insertAt_same, ← hk, insertAt_succAbove]
    simp_rw [e]
    have hcard : n + Fintype.card (Option Empty) ≤ n + 1 := by simp
    have hmeas : Measurable fun z => ‖h x z‖ₑ ^ 2 := ((wr14a_measurable_h_x hm x).enorm).pow_const 2
    have hdom := HRS.Quad.pinned_marginal_le_density (B := Option Empty) V hβ hN0 (n := n) hcard
      (pinsWith (fun e : Empty => e.elim) x) k
    calc ∫⁻ y, ‖h x (y k)‖ₑ ^ 2 ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) n (pinsWith (fun e : Empty => e.elim) x))
        = ∫⁻ z, ‖h x z‖ₑ ^ 2 ∂((pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) n
            (pinsWith (fun e : Empty => e.elim) x)).map (fun Y => Y k)) := by
          rw [lintegral_map hmeas (measurable_pi_apply k)]
      _ ≤ ∫⁻ z, ‖h x z‖ₑ ^ 2 ∂(μ.withDensity fun z => ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
            pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) z))) :=
          lintegral_mono' hdom le_rfl
      _ = ∫⁻ z, ‖h x z‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
            pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) z)) ∂μ := by
          rw [lintegral_withDensity_eq_lintegral_mul₀]
          · simp only [Pi.mul_apply]
            exact lintegral_congr fun z => mul_comm _ _
          · exact (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
              (measurable_const.add (isField_pinField V hlam _).measurable))).aemeasurable
          · exact hmeas.aemeasurable
      _ ≤ 𝒲 := hW x
  calc ∫⁻ x, pinWeight V (β / ((n + 1 : ℕ) : ℝ)) (fun e : Empty => e.elim) n x *
        ∫⁻ y, ‖h (insertAt a x y a) (insertAt a x y b)‖ₑ ^ 2
          ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) n (pinsWith (fun e : Empty => e.elim) x)) ∂μ
      ≤ ∫⁻ x, pinWeight V (β / ((n + 1 : ℕ) : ℝ)) (fun e : Empty => e.elim) n x * 𝒲 ∂μ :=
        lintegral_mono fun x => mul_le_mul' le_rfl (hx x)
    _ ≤ 𝒲 := by
        by_cases hC : 𝒲 = ⊤
        · rw [hC]; exact le_top
        · rw [lintegral_mul_const' _ _ hC,
            lintegral_pinWeight V hlam (fun e : Empty => e.elim) a (k : Fin n), one_mul]

/-! ### Exchangeability and the total-variation comparison -/

/-- All one-coordinate marginals of the weak ensemble with no pins coincide. -/
theorem wr14a_pinned_marginal_eq (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (n : ℕ) (i j : Fin n) :
    (pinnedLaw V lam n (fun e : Empty => e.elim)).map (fun Y => Y i)
      = (pinnedLaw V lam n (fun e : Empty => e.elim)).map (fun Y => Y j) := by
  have hψ := isField_pinField V hlam (fun e : Empty => e.elim)
  exact map_eval_eq_of_symm μ (pinnedDensity V lam n (fun e : Empty => e.elim))
    (measurable_fieldDensity hψ.measurable V _ n) (fun σ y => fieldDensity_comp_perm V _ _ σ y) i j

/-- **Total-variation comparison** (TeX `euc-pin-TV`): the conditional law of `y_k` given `y_0 = x` is within
`2κ/N` of the one-point marginal `π`. -/
theorem wr14a_tv_pin_le (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hκ : weakKappa V β ≤ 1 / 2)
    (x : Euc d) (k : Fin n) {A : Set (Euc d)} (hA : MeasurableSet A) :
    |((pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) n (pinsWith (fun e : Empty => e.elim) x)).map (fun Y => Y k)).real A
        - ((pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)).map
            (fun Y => Y 0)).real A| ≤ 2 * weakKappa V β / ((n + 1 : ℕ) : ℝ) := by
  have hlam : 0 ≤ β / ((n + 1 : ℕ) : ℝ) := div_nonneg hβ (Nat.cast_nonneg _)
  have h := rvh_pin_comparison (B := Empty) V hβ (N := n + 1) (n := n) (Nat.succ_pos n) (by simp)
    (fun e : Empty => e.elim) hκ (0 : Fin (n + 1)) k x hA
  rw [wr14a_pinned_marginal_eq V hlam (n + 1) ((0 : Fin (n + 1)).succAbove k) 0] at h
  exact h

end Row

/-! ### Whole-space envelope integrals -/

section Env

variable {s : ℝ}

theorem wr14a_measurable_g (hs0 : 0 < s) : Measurable (fun z : Euc d => HRS.Whole.rieszKernel d s z) := by
  have : (fun z : Euc d => HRS.Whole.rieszKernel d s z) = fun z => ‖z‖ ^ (-s) := by
    funext z; unfold HRS.Whole.rieszKernel; rw [if_neg hs0.ne']
  rw [this]
  exact measurable_norm.pow_const _

theorem wr14a_g_nonneg (hs0 : 0 < s) (z : Euc d) : 0 ≤ HRS.Whole.rieszKernel d s z := by
  rw [wr13e_g_eq_weight hs0]
  exact wr3_rieszWeight_nonneg s z

/-- `ν ≤ Cp μ` for an atomless `μ = ρ dx` does not charge a point. -/
theorem wr14a_ae_ne_of_le {ρ : Euc d → ℝ} (hd : 1 ≤ d) {ν : Measure (Euc d)} {Cp : ℝ}
    (hν : ν ≤ ENNReal.ofReal Cp • HRS.Whole.withDensityReal ρ) (x : Euc d) : ∀ᵐ y ∂ν, y ≠ x :=
  (Measure.absolutelyContinuous_of_le_smul hν).ae_le (wr3_ae_ne hd ρ x)

/-- Row mass of the envelope `1 + W_s(x - ·)` against a measure dominated by `Cp · ρ dx`. -/
theorem wr14a_lintegral_env_le (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (M : ℝ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ {ρ : Euc d → ℝ}, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ {ν : Measure (Euc d)} {Cp : ℝ}, ν ≤ ENNReal.ofReal Cp • HRS.Whole.withDensityReal ρ → 0 ≤ Cp →
      ∀ x : Euc d, ∫⁻ y, ENNReal.ofReal (1 + HRS.Whole.rieszWeight s (x - y)) ∂ν ≤ ENNReal.ofReal (c * Cp) := by
  have hσ0 := HRS.WeakRef.sigmaOf_pos hd hs0
  have hσd := HRS.WeakRef.sigmaOf_lt hd hsd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hsA := HRS.Whole.Q34.sphereArea_nonneg hd
  have hdσ : 0 < (d : ℝ) - HRS.WeakRef.sigmaOf d s := by linarith
  set c : ℝ := 1 + (1 + 4 / (d : ℝ)) * (|M| * sphereArea d / ((d : ℝ) - HRS.WeakRef.sigmaOf d s) + 1) with hc
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  refine ⟨c, hc0, fun {ρ} hρ hM {ν Cp} hν hCp x => ?_⟩
  have hrow := wr3_lintegral_W_row hd hs0 hsd hρ hM x
  have hle : (1 + (1 + 4 / (d : ℝ)) * (M * sphereArea d / ((d : ℝ) - HRS.WeakRef.sigmaOf d s) + 1)) ≤ c := by
    rw [hc]
    have h1 : M * sphereArea d / ((d : ℝ) - HRS.WeakRef.sigmaOf d s) ≤
        |M| * sphereArea d / ((d : ℝ) - HRS.WeakRef.sigmaOf d s) := by
      gcongr
      exact le_abs_self M
    have h2 : 0 ≤ 1 + 4 / (d : ℝ) := by positivity
    nlinarith
  calc ∫⁻ y, ENNReal.ofReal (1 + HRS.Whole.rieszWeight s (x - y)) ∂ν
      ≤ ∫⁻ y, ENNReal.ofReal (1 + HRS.Whole.rieszWeight s (x - y))
          ∂(ENNReal.ofReal Cp • HRS.Whole.withDensityReal ρ) := lintegral_mono' hν le_rfl
    _ = ENNReal.ofReal Cp * ∫⁻ y, ENNReal.ofReal (1 + HRS.Whole.rieszWeight s (x - y))
          ∂(HRS.Whole.withDensityReal ρ) := by rw [lintegral_smul_measure, smul_eq_mul]
    _ ≤ ENNReal.ofReal Cp * ENNReal.ofReal c := by
        gcongr
        exact hrow.trans (ENNReal.ofReal_le_ofReal hle)
    _ = ENNReal.ofReal (c * Cp) := by rw [← ENNReal.ofReal_mul hCp, mul_comm]

/-- `|H(x)| ≤ c Cp B` for `|h| ≤ B (1 + W_s)` and `π ≤ Cp μ`. -/
theorem wr14a_Hc_bound (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (M : ℝ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ {ρ : Euc d → ℝ}, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ {π : Measure (Euc d)} {Cp : ℝ}, π ≤ ENNReal.ofReal Cp • HRS.Whole.withDensityReal ρ → 0 ≤ Cp →
      ∀ {B : ℝ}, 0 ≤ B → ∀ {h : Euc d → Euc d → ℝ},
      (∀ x y, x ≠ y → |h x y| ≤ B * (1 + HRS.Whole.rieszWeight s (x - y))) →
      ∀ x : Euc d, |wr14a_Hc h π x| ≤ c * Cp * B := by
  obtain ⟨c, hc0, hcb⟩ := wr14a_lintegral_env_le hd hs0 hsd M
  refine ⟨c, hc0, fun {ρ} hρ hM {π Cp} hπ hCp {B} hB {h} hh x => ?_⟩
  have hae := wr14a_ae_ne_of_le hd hπ x
  unfold wr14a_Hc
  have h1 := norm_integral_le_lintegral_norm (μ := π) (fun y => h x y)
  have h2 : ∫⁻ y, ENNReal.ofReal ‖h x y‖ ∂π ≤ ENNReal.ofReal B * ENNReal.ofReal (c * Cp) := by
    calc ∫⁻ y, ENNReal.ofReal ‖h x y‖ ∂π
        ≤ ∫⁻ y, ENNReal.ofReal B * ENNReal.ofReal (1 + HRS.Whole.rieszWeight s (x - y)) ∂π := by
          refine lintegral_mono_ae ?_
          filter_upwards [hae] with y hy
          rw [← ENNReal.ofReal_mul hB, Real.norm_eq_abs]
          exact ENNReal.ofReal_le_ofReal (hh x y (Ne.symm hy))
      _ = ENNReal.ofReal B * ∫⁻ y, ENNReal.ofReal (1 + HRS.Whole.rieszWeight s (x - y)) ∂π := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ _ := by gcongr; exact hcb hρ hM hπ hCp x
  have h3 : (∫⁻ y, ENNReal.ofReal ‖h x y‖ ∂π).toReal ≤ c * Cp * B := by
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) (h2.trans ?_)
    rw [← ENNReal.ofReal_mul hB]
    refine le_of_eq ?_
    congr 1; ring
  rw [← Real.norm_eq_abs]
  exact h1.trans h3

/-- Integrability of a function with the envelope bound against a dominated measure. -/
theorem wr14a_integrable_of_env_bound (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (M : ℝ) :
    ∀ {ρ : Euc d → ℝ}, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ {ν : Measure (Euc d)} {Cp : ℝ}, ν ≤ ENNReal.ofReal Cp • HRS.Whole.withDensityReal ρ → 0 ≤ Cp →
      ∀ {b : ℝ}, 0 ≤ b → ∀ {x : Euc d} {f : Euc d → ℝ}, Measurable f →
      (∀ y, y ≠ x → |f y| ≤ b * (1 + HRS.Whole.rieszWeight s (x - y))) → Integrable f ν := by
  obtain ⟨c, hc0, hcb⟩ := wr14a_lintegral_env_le hd hs0 hsd M
  intro ρ hρ hM ν Cp hν hCp b hb x f hfm hf
  refine ⟨hfm.aestronglyMeasurable, ?_⟩
  have hae := wr14a_ae_ne_of_le hd hν x
  have : ∫⁻ y, ‖f y‖ₑ ∂ν ≤ ENNReal.ofReal b * ENNReal.ofReal (c * Cp) := by
    calc ∫⁻ y, ‖f y‖ₑ ∂ν
        ≤ ∫⁻ y, ENNReal.ofReal b * ENNReal.ofReal (1 + HRS.Whole.rieszWeight s (x - y)) ∂ν := by
          refine lintegral_mono_ae ?_
          filter_upwards [hae] with y hy
          rw [← ENNReal.ofReal_mul hb, Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal (hf y hy)
      _ = ENNReal.ofReal b * ∫⁻ y, ENNReal.ofReal (1 + HRS.Whole.rieszWeight s (x - y)) ∂ν := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ _ := by gcongr; exact hcb hρ hM hν hCp x
  exact lt_of_le_of_lt this (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)

end Env

/-! ### Centered kernel: zero mean and envelope -/

section Centered

variable {s : ℝ}

theorem wr14a_integral_cK_eq_zero {h : Euc d → Euc d → ℝ} (π : Measure (Euc d)) [IsProbabilityMeasure π]
    (x : Euc d) (hh : Integrable (h x) π) (hHi : Integrable (wr14a_Hc h π) π) :
    ∫ y, wr14a_cK h π x y ∂π = 0 := by
  unfold wr14a_cK
  have e1 : ∫ y, (h x y - wr14a_Hc h π x - wr14a_Hc h π y + wr14a_h0 h π) ∂π
      = (∫ y, h x y ∂π) - wr14a_Hc h π x - ∫ y, wr14a_Hc h π y ∂π + wr14a_h0 h π := by
    have i1 : Integrable (fun y => h x y - wr14a_Hc h π x) π := hh.sub (integrable_const _)
    have i2 : Integrable (fun y => h x y - wr14a_Hc h π x - wr14a_Hc h π y) π := i1.sub hHi
    rw [integral_add i2 (integrable_const _), integral_sub i1 hHi, integral_sub hh (integrable_const _)]
    simp
  rw [e1]
  unfold wr14a_h0 wr14a_Hc
  ring

theorem wr14a_abs_h0_le {h : Euc d → Euc d → ℝ} (π : Measure (Euc d)) [IsProbabilityMeasure π] {HB : ℝ}
    (hHB : ∀ x, |wr14a_Hc h π x| ≤ HB) : |wr14a_h0 h π| ≤ HB := by
  have : wr14a_h0 h π = ∫ x, wr14a_Hc h π x ∂π := rfl
  rw [this, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := HB) (Filter.Eventually.of_forall fun x => ?_)).trans (by simp)
  rw [Real.norm_eq_abs]; exact hHB x

theorem wr14a_abs_cK_le {h : Euc d → Euc d → ℝ} (π : Measure (Euc d)) [IsProbabilityMeasure π] {B HB : ℝ}
    (hB : 0 ≤ B) (hHB : ∀ x, |wr14a_Hc h π x| ≤ HB)
    (hh : ∀ x y, x ≠ y → |h x y| ≤ B * (1 + HRS.Whole.rieszWeight s (x - y))) (x y : Euc d) (hxy : y ≠ x) :
    |wr14a_cK h π x y| ≤ (B + 3 * HB) * (1 + HRS.Whole.rieszWeight s (x - y)) := by
  unfold wr14a_cK
  have h1 := hh x y (Ne.symm hxy)
  have h2 := hHB x
  have h3 := hHB y
  have h4 := wr14a_abs_h0_le π hHB
  have he : 1 ≤ 1 + HRS.Whole.rieszWeight s (x - y) := by
    linarith [wr3_rieszWeight_nonneg (d := d) s (x - y)]
  have hHB0 : 0 ≤ HB := (abs_nonneg _).trans h2
  have : |h x y - wr14a_Hc h π x - wr14a_Hc h π y + wr14a_h0 h π|
      ≤ |h x y| + |wr14a_Hc h π x| + |wr14a_Hc h π y| + |wr14a_h0 h π| := by
    calc _ ≤ |h x y - wr14a_Hc h π x - wr14a_Hc h π y| + |wr14a_h0 h π| := abs_add_le _ _
      _ ≤ |h x y - wr14a_Hc h π x| + |wr14a_Hc h π y| + |wr14a_h0 h π| := by gcongr; exact abs_sub _ _
      _ ≤ |h x y| + |wr14a_Hc h π x| + |wr14a_Hc h π y| + |wr14a_h0 h π| := by gcongr; exact abs_sub _ _
  nlinarith

end Centered

/-! ### Retained repulsion, row tails, row mean -/

section Repulsion

variable {s : ℝ}

/-- **Retained repulsion** (TeX `euc-radial`): if `|f(y)| ≤ b (1 + W(x-y))` and the weight satisfies
`ψ(y) ≤ M₀ - λ W(x-y)` (`y ≠ x`), then `∫ |f|² e^{ψ} dμ ≤ c b² e^{M₀} J_s(λ)` (`J_s = wr13c_J`). -/
theorem wr14a_variance_integral_le (hd : 1 ≤ d) (hs0 : 0 < s) (hsd : s < d) (M : ℝ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ {ρ : Euc d → ℝ}, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ {b : ℝ}, 0 ≤ b → ∀ {x : Euc d} {lam M0 : ℝ}, 0 < lam →
      ∀ {f ψ : Euc d → ℝ}, (∀ y, y ≠ x → |f y| ≤ b * (1 + HRS.Whole.rieszWeight s (x - y))) →
        (∀ y, y ≠ x → ψ y ≤ M0 - lam * HRS.Whole.rieszWeight s (x - y)) →
      ∫⁻ y, ‖f y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (ψ y)) ∂(HRS.Whole.withDensityReal ρ)
        ≤ ENNReal.ofReal (c * b ^ 2 * Real.exp M0 * wr13c_J d s lam) := by
  obtain ⟨C, hC0, hrad⟩ := wr13c_radial_J hd hs0 hsd M
  refine ⟨2 * (1 + C), by positivity, fun {ρ} hρ hM {b} hb {x lam M0} hlam {f ψ} hf hψ => ?_⟩
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  have hae : ∀ᵐ y ∂μ, y ≠ x := wr3_ae_ne hd ρ x
  have hgm : Measurable (fun y : Euc d => HRS.Whole.rieszKernel d s (x - y)) :=
    (wr14a_measurable_g hs0).comp (measurable_const.sub measurable_id)
  have hJ1 := wr13c_one_le_J (d := d) (s := s) lam hlam
  set Aexp : Euc d → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp (-(lam * HRS.Whole.rieszKernel d s (x - y)))) with hA
  set Bsq : Euc d → ℝ≥0∞ := fun y => ENNReal.ofReal (HRS.Whole.rieszKernel d s (x - y) ^ 2 *
    Real.exp (-(lam * HRS.Whole.rieszKernel d s (x - y)))) with hBsq
  have hAm : Measurable Aexp :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hgm.const_mul lam).neg)
  have hpt : ∀ᵐ y ∂μ, ‖f y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (ψ y)) ≤
      ENNReal.ofReal (2 * b ^ 2 * Real.exp M0) * (Aexp y + Bsq y) := by
    filter_upwards [hae] with y hy
    have h1 := hf y hy
    have h2 := hψ y hy
    have hg := wr13e_g_eq_weight (d := d) hs0 (x - y)
    have hg0 := wr14a_g_nonneg (d := d) hs0 (x - y)
    have e : ‖f y‖ₑ ^ 2 = ENNReal.ofReal (f y ^ 2) := by
      rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
    rw [e, ← ENNReal.ofReal_mul (sq_nonneg _), hA, hBsq]
    simp only
    rw [← ENNReal.ofReal_add (Real.exp_pos _).le (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← hg] at h1 h2
    set g := HRS.Whole.rieszKernel d s (x - y) with hgdef
    have h3 : f y ^ 2 ≤ b ^ 2 * (1 + g) ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg _) h1 2
      rwa [mul_pow, sq_abs] at this
    have h4 : Real.exp (ψ y) ≤ Real.exp M0 * Real.exp (-(lam * g)) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
    have h5 : (1 + g) ^ 2 ≤ 2 * (1 + g ^ 2) := by nlinarith [sq_nonneg (1 - g)]
    calc f y ^ 2 * Real.exp (ψ y) ≤ (b ^ 2 * (1 + g) ^ 2) * (Real.exp M0 * Real.exp (-(lam * g))) :=
          mul_le_mul h3 h4 (Real.exp_pos _).le (by positivity)
      _ ≤ (b ^ 2 * (2 * (1 + g ^ 2))) * (Real.exp M0 * Real.exp (-(lam * g))) := by
          gcongr
      _ = 2 * b ^ 2 * Real.exp M0 * (Real.exp (-(lam * g)) + g ^ 2 * Real.exp (-(lam * g))) := by ring
  have hAint : ∫⁻ y, Aexp y ∂μ ≤ 1 := by
    calc ∫⁻ y, Aexp y ∂μ ≤ ∫⁻ _y, 1 ∂μ := by
          refine lintegral_mono fun y => ?_
          rw [hA]; simp only
          rw [← ENNReal.ofReal_one]
          refine ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.2 ?_)
          have := mul_nonneg hlam.le (wr14a_g_nonneg (d := d) hs0 (x - y))
          linarith
      _ = 1 := by simp
  have hBint : ∫⁻ y, Bsq y ∂μ ≤ ENNReal.ofReal (C * wr13c_J d s lam) := hrad ρ hρ hM lam hlam x
  calc ∫⁻ y, ‖f y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (ψ y)) ∂μ
      ≤ ∫⁻ y, ENNReal.ofReal (2 * b ^ 2 * Real.exp M0) * (Aexp y + Bsq y) ∂μ := lintegral_mono_ae hpt
    _ = ENNReal.ofReal (2 * b ^ 2 * Real.exp M0) * (∫⁻ y, Aexp y ∂μ + ∫⁻ y, Bsq y ∂μ) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left hAm]
    _ ≤ ENNReal.ofReal (2 * b ^ 2 * Real.exp M0) * (ENNReal.ofReal 1 + ENNReal.ofReal (C * wr13c_J d s lam)) := by
        gcongr
        · simpa using hAint
    _ = ENNReal.ofReal (2 * b ^ 2 * Real.exp M0 * (1 + C * wr13c_J d s lam)) := by
        rw [← ENNReal.ofReal_add zero_le_one (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h0 : 0 ≤ 2 * b ^ 2 * Real.exp M0 := by positivity
        have : 1 + C * wr13c_J d s lam ≤ (1 + C) * wr13c_J d s lam := by nlinarith
        calc 2 * b ^ 2 * Real.exp M0 * (1 + C * wr13c_J d s lam)
            ≤ 2 * b ^ 2 * Real.exp M0 * ((1 + C) * wr13c_J d s lam) := mul_le_mul_of_nonneg_left this h0
          _ = _ := by ring

/-- **Tail of the envelope**: `∫_{W(x-y) > K} (1 + W(x-y)) dμ(y) ≤ c K^{1-d/s}` for `K ≥ 1`. -/
theorem wr14a_env_tail_lintegral (hd : 1 ≤ d) (hs0 : 0 < s) (hsd : s < d) (M : ℝ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ {ρ : Euc d → ℝ}, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ {K : ℝ}, 1 ≤ K → ∀ x : Euc d,
      ∫⁻ y, {z : Euc d | K < HRS.Whole.rieszWeight s z}.indicator
          (fun z => ENNReal.ofReal (1 + HRS.Whole.rieszWeight s z)) (x - y) ∂(HRS.Whole.withDensityReal ρ)
        ≤ ENNReal.ofReal (c * K ^ (1 - (d : ℝ) / s)) := by
  obtain ⟨Ca, Cb, hCa, hCb, hrow⟩ := wr3_row_bounds_real hd hs0.le hsd 1 M
  have hσ : HRS.WeakRef.sigmaOf d s = s := by simp [HRS.WeakRef.sigmaOf, hs0.ne']
  set e : ℝ := 1 - (d : ℝ) / s with he
  refine ⟨4 * Ca / (2 : ℝ) ^ e, by positivity, fun {ρ} hρ hM {K} hK x => ?_⟩
  have hK0 : 0 < K := by linarith
  have hq0 : ∀ x y : Euc d, 0 ≤ HRS.Whole.rieszWeight s (x - y) := fun x y => wr3_rieszWeight_nonneg s _
  have hqb : ∀ x y : Euc d, x ≠ y →
      HRS.Whole.rieszWeight s (x - y) ≤ 1 * (1 + HRS.Whole.rieszWeight s (x - y)) := fun x y _ => by
    linarith
  have h1 := (hrow ρ hρ hM (fun x y => HRS.Whole.rieszWeight s (x - y)) hq0 hqb x).1 (K / 2) (by positivity)
  rw [hσ] at h1
  have hpt : ∀ y : Euc d, {z : Euc d | K < HRS.Whole.rieszWeight s z}.indicator
      (fun z => ENNReal.ofReal (1 + HRS.Whole.rieszWeight s z)) (x - y) ≤
      ENNReal.ofReal 4 * ENNReal.ofReal (max (HRS.Whole.rieszWeight s (x - y) - K / 2) 0) := by
    intro y
    by_cases hz : K < HRS.Whole.rieszWeight s (x - y)
    · rw [Set.indicator_of_mem (show x - y ∈ {z : Euc d | K < HRS.Whole.rieszWeight s z} from hz)]
      rw [← ENNReal.ofReal_mul (by norm_num)]
      refine ENNReal.ofReal_le_ofReal ?_
      have : K / 2 ≤ HRS.Whole.rieszWeight s (x - y) := by linarith
      rw [max_eq_left (by linarith)]
      linarith
    · rw [Set.indicator_of_notMem (show x - y ∉ {z : Euc d | K < HRS.Whole.rieszWeight s z} from hz)]
      exact bot_le
  calc ∫⁻ y, {z : Euc d | K < HRS.Whole.rieszWeight s z}.indicator
          (fun z => ENNReal.ofReal (1 + HRS.Whole.rieszWeight s z)) (x - y) ∂(HRS.Whole.withDensityReal ρ)
      ≤ ∫⁻ y, ENNReal.ofReal 4 * ENNReal.ofReal (max (HRS.Whole.rieszWeight s (x - y) - K / 2) 0)
          ∂(HRS.Whole.withDensityReal ρ) := lintegral_mono hpt
    _ = ENNReal.ofReal 4 * ∫⁻ y, ENNReal.ofReal (max (HRS.Whole.rieszWeight s (x - y) - K / 2) 0)
          ∂(HRS.Whole.withDensityReal ρ) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal 4 * ENNReal.ofReal (Ca * (K / 2) ^ e) := by gcongr
    _ = ENNReal.ofReal (4 * Ca / (2 : ℝ) ^ e * K ^ e) := by
        rw [← ENNReal.ofReal_mul (by norm_num), Real.div_rpow hK0.le (by norm_num)]
        congr 1; ring

/-- **Mean of the row, one coordinate**: near part by the bounded densities, far part by the
total-variation closeness `ε` of `ν` to `π`. -/
theorem wr14a_mean_one_le (hd : 1 ≤ d) (hs0 : 0 < s) (hsd : s < d) (M : ℝ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ {ρ : Euc d → ℝ}, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ {Cp : ℝ}, 0 ≤ Cp → ∀ {b : ℝ}, 0 ≤ b → ∀ {x : Euc d} {ε K : ℝ}, 0 ≤ ε → 1 ≤ K →
      ∀ {π ν : Measure (Euc d)} [IsProbabilityMeasure π] [IsProbabilityMeasure ν],
      π ≤ ENNReal.ofReal Cp • HRS.Whole.withDensityReal ρ →
      ν ≤ ENNReal.ofReal Cp • HRS.Whole.withDensityReal ρ →
      (∀ A : Set (Euc d), MeasurableSet A → |ν.real A - π.real A| ≤ ε) →
      ∀ {f : Euc d → ℝ}, Measurable f →
      (∀ y, y ≠ x → |f y| ≤ b * (1 + HRS.Whole.rieszWeight s (x - y))) →
      |∫ y, f y ∂ν - ∫ y, f y ∂π| ≤ 4 * b * K * ε + 2 * (c * Cp * b * K ^ (1 - (d : ℝ) / s)) := by
  obtain ⟨c, hc0, hct⟩ := wr14a_env_tail_lintegral hd hs0 hsd M
  refine ⟨c, hc0, fun {ρ} hρ hM {Cp} hCp {b} hb {x ε K} hε hK {π ν} _ _ hπ hν hTV {f} hfm hf => ?_⟩
  set W : Euc d → ℝ := HRS.Whole.rieszWeight s with hW
  set T : Set (Euc d) := {y : Euc d | y ≠ x ∧ W (x - y) ≤ K} with hT
  have hWm : Measurable W := wr3_measurable_rieszWeight s
  have hTm : MeasurableSet T :=
    (measurableSet_singleton x).compl.inter
      (measurableSet_le (hWm.comp (measurable_const.sub measurable_id)) measurable_const)
  set f1 : Euc d → ℝ := T.indicator f with hf1
  set f2 : Euc d → ℝ := Tᶜ.indicator f with hf2
  have hsplit : ∀ y, f y = f1 y + f2 y := fun y => by
    have := congrFun (Set.indicator_self_add_compl T f) y
    exact this.symm
  have hf1m : Measurable f1 := hfm.indicator hTm
  have hf2m : Measurable f2 := hfm.indicator hTm.compl
  have hf1b : ∀ y, |f1 y| ≤ 2 * b * K := by
    intro y
    by_cases hy : y ∈ T
    · rw [hf1, Set.indicator_of_mem hy]
      have h1 := hf y hy.1
      have h2 : 1 + W (x - y) ≤ 2 * K := by linarith [hy.2]
      calc |f y| ≤ b * (1 + W (x - y)) := h1
        _ ≤ b * (2 * K) := mul_le_mul_of_nonneg_left h2 hb
        _ = 2 * b * K := by ring
    · rw [hf1, Set.indicator_of_notMem hy]; simp; positivity
  have hfi : ∀ (κ : Measure (Euc d)), κ ≤ ENNReal.ofReal Cp • HRS.Whole.withDensityReal ρ → Integrable f κ :=
    fun κ hκ => wr14a_integrable_of_env_bound hd hs0.le hsd M hρ hM hκ hCp hb hfm hf
  have hf1i : ∀ (κ : Measure (Euc d)) [IsProbabilityMeasure κ], Integrable f1 κ := fun κ _ =>
    Integrable.of_bound hf1m.aestronglyMeasurable (2 * b * K) (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hf1b y)
  have hf2i : ∀ (κ : Measure (Euc d)), κ ≤ ENNReal.ofReal Cp • HRS.Whole.withDensityReal ρ → Integrable f2 κ :=
    fun κ hκ => (hfi κ hκ).indicator hTm.compl
  have hint : ∀ (κ : Measure (Euc d)) [IsProbabilityMeasure κ],
      κ ≤ ENNReal.ofReal Cp • HRS.Whole.withDensityReal ρ → ∫ y, f y ∂κ = ∫ y, f1 y ∂κ + ∫ y, f2 y ∂κ := by
    intro κ _ hκ
    rw [← integral_add (hf1i κ) (hf2i κ hκ)]
    exact integral_congr_ae (Filter.Eventually.of_forall hsplit)
  have htail : ∀ (κ : Measure (Euc d)), κ ≤ ENNReal.ofReal Cp • HRS.Whole.withDensityReal ρ →
      |∫ y, f2 y ∂κ| ≤ c * Cp * b * K ^ (1 - (d : ℝ) / s) := by
    intro κ hκ
    have hae := wr14a_ae_ne_of_le hd hκ x
    set F : Euc d → ℝ≥0∞ := {z : Euc d | K < W z}.indicator (fun z => ENNReal.ofReal (1 + W z)) with hF
    have hpt : ∀ᵐ y ∂κ, ENNReal.ofReal ‖f2 y‖ ≤ ENNReal.ofReal b * F (x - y) := by
      filter_upwards [hae] with y hy
      by_cases hyT : y ∈ T
      · rw [hf2, Set.indicator_of_notMem (by simpa using hyT)]
        simp
      · have hK' : K < W (x - y) := by
          by_contra hcon
          exact hyT ⟨hy, not_lt.1 hcon⟩
        rw [hf2, Set.indicator_of_mem (show y ∈ Tᶜ from hyT)]
        rw [hF, Set.indicator_of_mem (show x - y ∈ {z : Euc d | K < W z} from hK'), ← ENNReal.ofReal_mul hb]
        exact ENNReal.ofReal_le_ofReal (by rw [Real.norm_eq_abs]; exact hf y hy)
    have h1 := norm_integral_le_lintegral_norm (μ := κ) f2
    have h2 : ∫⁻ y, ENNReal.ofReal ‖f2 y‖ ∂κ ≤ ENNReal.ofReal (c * Cp * b * K ^ (1 - (d : ℝ) / s)) := by
      calc ∫⁻ y, ENNReal.ofReal ‖f2 y‖ ∂κ ≤ ∫⁻ y, ENNReal.ofReal b * F (x - y) ∂κ := lintegral_mono_ae hpt
        _ = ENNReal.ofReal b * ∫⁻ y, F (x - y) ∂κ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal b * (ENNReal.ofReal Cp * ∫⁻ y, F (x - y) ∂(HRS.Whole.withDensityReal ρ)) := by
            gcongr
            calc ∫⁻ y, F (x - y) ∂κ
                ≤ ∫⁻ y, F (x - y) ∂(ENNReal.ofReal Cp • HRS.Whole.withDensityReal ρ) := lintegral_mono' hκ le_rfl
              _ = _ := by rw [lintegral_smul_measure, smul_eq_mul]
        _ ≤ ENNReal.ofReal b * (ENNReal.ofReal Cp * ENNReal.ofReal (c * K ^ (1 - (d : ℝ) / s))) := by
            gcongr
            exact hct hρ hM hK x
        _ = _ := by
            rw [← ENNReal.ofReal_mul hCp, ← ENNReal.ofReal_mul hb]
            congr 1; ring
    rw [← Real.norm_eq_abs]
    refine h1.trans (ENNReal.toReal_le_of_le_ofReal (by positivity) h2)
  have hD : 0 ≤ 4 * b * K := by positivity
  have h1 := abs_integral_sub_le_of_tv ν π (c := ε) (D := 4 * b * K) hD hTV hf1m (h := f1) (fun z z' => by
    have h1 := abs_le.1 (hf1b z)
    have h2 := abs_le.1 (hf1b z')
    rw [abs_le]; constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2])
  rw [hint ν hν, hint π hπ]
  have e : ∫ y, f1 y ∂ν + ∫ y, f2 y ∂ν - (∫ y, f1 y ∂π + ∫ y, f2 y ∂π)
      = (∫ y, f1 y ∂ν - ∫ y, f1 y ∂π) + ∫ y, f2 y ∂ν - ∫ y, f2 y ∂π := by ring
  rw [e]
  have h3 := htail ν hν
  have h4 := htail π hπ
  have h5 := abs_le.1 h1
  have h6 := abs_le.1 h3
  have h7 := abs_le.1 h4
  rw [abs_le]
  constructor <;> nlinarith [h5.1, h5.2, h6.1, h6.2, h7.1, h7.2, mul_comm ε (4 * b * K)]

end Repulsion

end HRS.MS.Wr
