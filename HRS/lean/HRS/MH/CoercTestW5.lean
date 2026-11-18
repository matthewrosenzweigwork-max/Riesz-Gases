import Mathlib
import HRS.Whole.AppendixALemmas
import HRS.MH.CoercLowerDefs
import HRS.MH.CoercLowerFinal
import HRS.MH.CoercTestSpecDefs

/-!
# W5: mollification (proofs of `uMol_eq_gaussU`, `mollify_error` of `HRS/MH/CoercTestSpec.lean`)
-/

noncomputable section

open MeasureTheory
open scoped BigOperators FourierTransform

namespace HRS.MH.CoercTest

open HRS.MH.CoercLower

variable {d N : ℕ}

/-- [W5a] `u_{2t} = (2t/π)^{d/2} gaussU t` (pure algebra: `gaussK` is even; `integral_const_mul`). -/
theorem uMol_eq_gaussU {t : ℝ} (ht : 0 < t) (X : HRS.Whole.EucConfig d N) (ρ : Euc d → ℝ) :
    uMol (2 * t) X ρ = fun z => (2 * t / Real.pi) ^ ((d : ℝ) / 2) * gaussU t X ρ z := by
  funext z
  simp only [uMol, gaussU, molK, mul_assoc]
  rw [integral_const_mul, ← Finset.mul_sum]
  ring

/-- Integrability of `x ↦ exp(-t‖x‖²)` on `Euc d` for `t > 0`. -/
theorem p_wt5_gaussK_integrable {t : ℝ} (ht : 0 < t) : Integrable (gaussK t : Euc d → ℝ) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := Euc d) (b := (t : ℂ))
    (by simpa using ht) 0 0
  refine h.re.congr (Filter.Eventually.of_forall fun v => ?_)
  simp [gaussK, Complex.exp_re, ← Complex.ofReal_pow]

/-- `∫ exp(-s‖x‖²) dx = (π/s)^{d/2}` on `Euc d` for `s > 0`. -/
theorem p_wt5_gaussK_integral {s : ℝ} (hs : 0 < s) :
    ∫ x : Euc d, gaussK s x = (Real.pi / s) ^ ((d : ℝ) / 2) := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := Euc d) hs
  rw [finrank_euclideanSpace_fin] at h
  simpa [gaussK] using h

theorem p_wt5_continuous_gaussK (t : ℝ) : Continuous (gaussK t : Euc d → ℝ) := by
  unfold gaussK
  fun_prop

theorem p_wt5_continuous_molK (b : ℝ) : Continuous (molK b : Euc d → ℝ) := by
  unfold molK
  exact continuous_const.mul (p_wt5_continuous_gaussK b)

theorem p_wt5_molK_nonneg {b : ℝ} (hb : 0 < b) (x : Euc d) : 0 ≤ molK b x := by
  unfold molK gaussK
  have : 0 ≤ b / Real.pi := by positivity
  positivity

theorem p_wt5_molK_integrable {b : ℝ} (hb : 0 < b) : Integrable (molK b : Euc d → ℝ) :=
  (p_wt5_gaussK_integrable hb).const_mul _

theorem p_wt5_molK_integral {b : ℝ} (hb : 0 < b) : ∫ x : Euc d, molK b x = 1 := by
  unfold molK
  rw [integral_const_mul, p_wt5_gaussK_integral hb, ← Real.mul_rpow (by positivity) (by positivity)]
  rw [show b / Real.pi * (Real.pi / b) = 1 by field_simp]
  simp

/-- pointwise: `‖w‖ e^{-b‖w‖²} ≤ b^{-1/2} e^{-(b/2)‖w‖²}`. -/
theorem p_wt5_pointwise {b : ℝ} (hb : 0 < b) (w : Euc d) :
    ‖w‖ * gaussK b w ≤ b ^ (-(1 / 2 : ℝ)) * gaussK (b / 2) w := by
  have hsq : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb.le
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  set s := Real.sqrt b * ‖w‖ with hs
  have h1 : s ≤ Real.exp (s ^ 2 / 2) := by
    have := Real.add_one_le_exp (s ^ 2 / 2)
    nlinarith [sq_nonneg (s - 1)]
  have h2 : s ^ 2 = b * ‖w‖ ^ 2 := by rw [hs, mul_pow, hsq]
  have h3 : b ^ (-(1 / 2 : ℝ)) = (Real.sqrt b)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hb.le]
  unfold gaussK
  rw [h3]
  have h4 : Real.exp (-b * ‖w‖ ^ 2) = Real.exp (-(b / 2) * ‖w‖ ^ 2) * Real.exp (-(b / 2) * ‖w‖ ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h4]
  have h5 : Real.exp (s ^ 2 / 2) = Real.exp ((b / 2) * ‖w‖ ^ 2) := by rw [h2]; congr 1; ring
  have h6 : Real.exp (-(b / 2) * ‖w‖ ^ 2) * Real.exp ((b / 2) * ‖w‖ ^ 2) = 1 := by
    rw [← Real.exp_add]; simp
  set E := Real.exp (-(b / 2) * ‖w‖ ^ 2) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have h7 : s * E ≤ 1 := by
    calc s * E ≤ Real.exp (s ^ 2 / 2) * E := mul_le_mul_of_nonneg_right h1 hE0
      _ = 1 := by rw [h5, mul_comm, h6]
  have h8 : ‖w‖ = (Real.sqrt b)⁻¹ * s := by
    rw [hs]; field_simp
  rw [h8]
  have hinv : 0 ≤ (Real.sqrt b)⁻¹ := by positivity
  calc (Real.sqrt b)⁻¹ * s * (E * E) = (Real.sqrt b)⁻¹ * (s * E) * E := by ring
    _ ≤ (Real.sqrt b)⁻¹ * 1 * E := by gcongr
    _ = (Real.sqrt b)⁻¹ * E := by ring

/-- The first moment of the mollifier: integrable, with `∫ ‖w‖ G_b(w) ≤ 2^{d/2} b^{-1/2}`. -/
theorem p_wt5_moment {b : ℝ} (hb : 0 < b) :
    Integrable (fun w : Euc d => ‖w‖ * molK b w) ∧
      ∫ w : Euc d, ‖w‖ * molK b w ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * b ^ (-(1 / 2 : ℝ)) := by
  have hint : Integrable (fun w : Euc d => (b / Real.pi) ^ ((d : ℝ) / 2) * (b ^ (-(1 / 2 : ℝ)) *
      gaussK (b / 2) w)) := ((p_wt5_gaussK_integrable (by positivity : 0 < b / 2)).const_mul _).const_mul _
  have hle : ∀ w : Euc d, ‖w‖ * molK b w ≤
      (b / Real.pi) ^ ((d : ℝ) / 2) * (b ^ (-(1 / 2 : ℝ)) * gaussK (b / 2) w) := by
    intro w
    have h0 : 0 ≤ (b / Real.pi) ^ ((d : ℝ) / 2) := by positivity
    calc ‖w‖ * molK b w = (b / Real.pi) ^ ((d : ℝ) / 2) * (‖w‖ * gaussK b w) := by
          unfold molK; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (p_wt5_pointwise hb w) h0
  have hmeas : AEStronglyMeasurable (fun w : Euc d => ‖w‖ * molK b w) volume :=
    (continuous_norm.mul (p_wt5_continuous_molK b)).aestronglyMeasurable
  have hint' : Integrable (fun w : Euc d => ‖w‖ * molK b w) :=
    hint.mono' hmeas (Filter.Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (p_wt5_molK_nonneg hb w))]
      exact hle w)
  refine ⟨hint', ?_⟩
  calc ∫ w : Euc d, ‖w‖ * molK b w ≤ ∫ w : Euc d, (b / Real.pi) ^ ((d : ℝ) / 2) *
        (b ^ (-(1 / 2 : ℝ)) * gaussK (b / 2) w) := integral_mono hint' hint hle
    _ = (b / Real.pi) ^ ((d : ℝ) / 2) * (b ^ (-(1 / 2 : ℝ)) * (Real.pi / (b / 2)) ^ ((d : ℝ) / 2)) := by
        rw [integral_const_mul, integral_const_mul, p_wt5_gaussK_integral (by positivity : 0 < b / 2)]
    _ = (2 : ℝ) ^ ((d : ℝ) / 2) * b ^ (-(1 / 2 : ℝ)) := by
        have : (b / Real.pi) ^ ((d : ℝ) / 2) * (Real.pi / (b / 2)) ^ ((d : ℝ) / 2) =
            (2 : ℝ) ^ ((d : ℝ) / 2) := by
          rw [← Real.mul_rpow (by positivity) (by positivity)]
          congr 1
          field_simp
        calc _ = ((b / Real.pi) ^ ((d : ℝ) / 2) * (Real.pi / (b / 2)) ^ ((d : ℝ) / 2)) *
              b ^ (-(1 / 2 : ℝ)) := by ring
          _ = _ := by rw [this]

/-- A Lipschitz compactly supported function is continuous, bounded and integrable. -/
theorem p_wt5_psi_facts {ψ : Euc d → ℝ} {L : ℝ} (hL : 0 ≤ L) (hψ : HRS.PDE.ToolboxRd.IsLipschitz L ψ)
    (hc : HasCompactSupport ψ) :
    Continuous ψ ∧ (∃ B : ℝ, ∀ x, ‖ψ x‖ ≤ B) ∧ Integrable ψ := by
  have hlip : LipschitzWith L.toNNReal ψ := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hL]
    exact hψ x y
  have hcont : Continuous ψ := hlip.continuous
  exact ⟨hcont, hcont.bounded_above_of_compact_support hc, hcont.integrable_of_hasCompactSupport hc⟩

/-- `Φ(y) = ∫ ψ(z) G_b(y - z) dz`. -/
def p_wt5_Phi (b : ℝ) (ψ : Euc d → ℝ) (y : Euc d) : ℝ := ∫ z, ψ z * molK b (y - z)

theorem p_wt5_integrable_conv {b : ℝ} (hb : 0 < b) {ψ : Euc d → ℝ} (hψc : Continuous ψ) {B : ℝ}
    (hB : ∀ x, ‖ψ x‖ ≤ B) (y : Euc d) : Integrable (fun z => ψ z * molK b (y - z)) :=
  ((p_wt5_molK_integrable hb).comp_sub_left y).bdd_mul hψc.aestronglyMeasurable
    (Filter.Eventually.of_forall hB)

theorem p_wt5_Phi_bound {b : ℝ} (hb : 0 < b) {ψ : Euc d → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hψ : HRS.PDE.ToolboxRd.IsLipschitz L ψ) (hψc : Continuous ψ) {B : ℝ} (hB : ∀ x, ‖ψ x‖ ≤ B)
    (y : Euc d) : |ψ y - p_wt5_Phi b ψ y| ≤ L * ∫ w : Euc d, ‖w‖ * molK b w := by
  have hint : Integrable (fun w : Euc d => ψ (y - w) * molK b w) :=
    (p_wt5_molK_integrable hb).bdd_mul (hψc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun w => hB _)
  have hΦ : p_wt5_Phi b ψ y = ∫ w : Euc d, ψ (y - w) * molK b w := by
    unfold p_wt5_Phi
    rw [← integral_sub_left_eq_self (fun z => ψ z * molK b (y - z)) volume y]
    simp [sub_sub_cancel]
  have hψy : ψ y = ∫ w : Euc d, ψ y * molK b w := by
    rw [integral_const_mul, p_wt5_molK_integral hb, mul_one]
  have hmom := (p_wt5_moment (d := d) hb).1
  have hsub : ψ y - p_wt5_Phi b ψ y = ∫ w : Euc d, (ψ y * molK b w - ψ (y - w) * molK b w) := by
    rw [integral_sub ((p_wt5_molK_integrable hb).const_mul _) hint, ← hψy, ← hΦ]
  rw [hsub, ← Real.norm_eq_abs, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hmom.const_mul L) (Filter.Eventually.of_forall fun w => ?_)
  rw [← sub_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (p_wt5_molK_nonneg hb w)]
  have := hψ y (y - w)
  rw [show y - (y - w) = w by abel] at this
  calc |ψ y - ψ (y - w)| * molK b w ≤ (L * ‖w‖) * molK b w :=
        mul_le_mul_of_nonneg_right this (p_wt5_molK_nonneg hb w)
    _ = L * (‖w‖ * molK b w) := by ring

/-- Joint integrability for Fubini (first variable `z` carries `ψ`, second `y` carries `ρ`). -/
theorem p_wt5_fubini_integrable {b : ℝ} (hb : 0 < b) {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ)
    {ψ : Euc d → ℝ} (hψc : Continuous ψ) {B : ℝ} (hB : ∀ x, ‖ψ x‖ ≤ B) :
    Integrable (fun p : Euc d × Euc d => ρ p.2 * (ψ p.1 * molK b (p.2 - p.1)))
      (volume.prod volume) := by
  have hρi : Integrable ρ := Integrable.of_integral_ne_zero (by rw [hρ.integral_one]; exact one_ne_zero)
  have hmeas : AEStronglyMeasurable (fun p : Euc d × Euc d => ρ p.2 * (ψ p.1 * molK b (p.2 - p.1)))
      (volume.prod volume) := by
    refine Measurable.aestronglyMeasurable ?_
    exact (hρ.measurable.comp measurable_snd).mul ((hψc.measurable.comp measurable_fst).mul
      ((p_wt5_continuous_molK b).measurable.comp (measurable_snd.sub measurable_fst)))
  rw [integrable_prod_iff' hmeas]
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  refine ⟨Filter.Eventually.of_forall fun y => ?_, ?_⟩
  · have h1 : Integrable (fun z => ψ z * molK b (y - z)) := p_wt5_integrable_conv hb hψc hB y
    exact h1.const_mul (ρ y)
  · refine Integrable.mono' (hρi.const_mul B) ?_ (Filter.Eventually.of_forall fun y => ?_)
    · exact hmeas.norm.prod_swap.integral_prod_right'
    · have h1 : Integrable (fun z => ψ z * molK b (y - z)) := p_wt5_integrable_conv hb hψc hB y
      have hnn : 0 ≤ ∫ z, ‖ρ y * (ψ z * molK b (y - z))‖ := integral_nonneg fun _ => norm_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      have hρy := hρ.nonneg y
      calc ∫ z, ‖ρ y * (ψ z * molK b (y - z))‖ ≤ ∫ z, ρ y * (B * molK b (y - z)) := by
            refine integral_mono (h1.const_mul (ρ y)).norm
              ((((p_wt5_molK_integrable hb).comp_sub_left y).const_mul B).const_mul (ρ y)) fun z => ?_
            have hG := p_wt5_molK_nonneg hb (y - z)
            rw [norm_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg hρy, Real.norm_eq_abs (molK b (y - z)),
              abs_of_nonneg hG]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hB z) hG) hρy
        _ = B * ρ y := by
            rw [integral_const_mul, integral_const_mul,
              integral_sub_left_eq_self (molK b) volume y, p_wt5_molK_integral hb]
            ring

theorem p_wt5_pair_empirical {ψ : Euc d → ℝ} (hψc : Continuous ψ) (X : HRS.Whole.EucConfig d N) :
    HRS.Whole.pair (HRS.Whole.empirical X) ψ = (1 / (N : ℝ)) * ∑ i, ψ (X i) := by
  unfold HRS.Whole.pair HRS.Whole.empirical
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp [integral_dirac, ENNReal.toReal_inv]
  · intro i _
    exact integrable_dirac' hψc.stronglyMeasurable (by simp)

theorem p_wt5_pair_density {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) (ψ : Euc d → ℝ) :
    HRS.Whole.pair (HRS.Whole.withDensityReal ρ) ψ = ∫ y, ρ y * ψ y := by
  unfold HRS.Whole.pair HRS.Whole.withDensityReal
  rw [integral_withDensity_eq_integral_toReal_smul hρ.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun y => ENNReal.ofReal_lt_top)]
  congr 1
  funext y
  rw [ENNReal.toReal_ofReal (hρ.nonneg y), smul_eq_mul]

theorem p_wt5_rhoPhi_integrable {b : ℝ} (hb : 0 < b) {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ)
    {ψ : Euc d → ℝ} (hψc : Continuous ψ) {B : ℝ} (hB : ∀ x, ‖ψ x‖ ≤ B) :
    Integrable (fun y => ρ y * p_wt5_Phi b ψ y) := by
  have h := (p_wt5_fubini_integrable hb hρ hψc hB).integral_prod_right
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [p_wt5_Phi]
  rw [integral_const_mul]

theorem p_wt5_main_identity {b : ℝ} (hb : 0 < b) {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ)
    {ψ : Euc d → ℝ} (hψc : Continuous ψ) {B : ℝ} (hB : ∀ x, ‖ψ x‖ ≤ B)
    (X : HRS.Whole.EucConfig d N) :
    ∫ z, ψ z * uMol b X ρ z =
      (1 / (N : ℝ)) * ∑ i, p_wt5_Phi b ψ (X i) - ∫ y, ρ y * p_wt5_Phi b ψ y := by
  have hF := p_wt5_fubini_integrable hb hρ hψc hB
  have h1 : Integrable (fun z => (1 / (N : ℝ)) * ∑ i, ψ z * molK b (X i - z)) :=
    (integrable_finsetSum _ fun i _ => p_wt5_integrable_conv hb hψc hB (X i)).const_mul _
  have h2 : Integrable (fun z => ψ z * ∫ y, molK b (y - z) * ρ y) := by
    refine hF.integral_prod_left.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  have hsplit : ∀ z, ψ z * uMol b X ρ z =
      (1 / (N : ℝ)) * ∑ i, ψ z * molK b (X i - z) - ψ z * ∫ y, molK b (y - z) * ρ y := by
    intro z
    simp only [uMol]
    rw [mul_sub]
    congr 1
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [hsplit]
  rw [integral_sub h1 h2, integral_const_mul, integral_finsetSum _
    (fun i _ => p_wt5_integrable_conv hb hψc hB (X i))]
  congr 1
  have hswap := integral_integral_swap (μ := (volume : Measure (Euc d))) (ν := (volume : Measure (Euc d)))
    (f := fun z y => ρ y * (ψ z * molK b (y - z))) hF
  calc ∫ z, ψ z * ∫ y, molK b (y - z) * ρ y
      = ∫ z, ∫ y, ρ y * (ψ z * molK b (y - z)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only
        rw [← integral_const_mul]
        congr 1
        funext y
        ring
    _ = ∫ y, ∫ z, ρ y * (ψ z * molK b (y - z)) := hswap
    _ = ∫ y, ρ y * p_wt5_Phi b ψ y := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [p_wt5_Phi]
        rw [integral_const_mul]

/-- [W5b] Mollification error: for compactly supported `L`-Lipschitz `ψ`,
`|(μ_N - ρ)(ψ) - ∫ ψ u_b| ≤ C L b^{-1/2}` with `C = C(d)`.  Route: `pair (empirical X) ψ = N⁻¹ ∑ ψ(x_i)`,
`pair (withDensityReal ρ) ψ = ∫ ψρ`, Fubini (`ψ` bounded with compact support), `|ψ - G_b * ψ| ≤ L ∫‖y‖ G_b`
and the Gaussian first moment `∫ ‖y‖ G_b = C_d b^{-1/2}`. -/
theorem mollify_error (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ b : ℝ, 0 < b → ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ →
      ∀ N : ℕ, ∀ X : HRS.Whole.EucConfig d N, 1 ≤ N →
      ∀ (ψ : Euc d → ℝ) (L : ℝ), 0 ≤ L → HRS.PDE.ToolboxRd.IsLipschitz L ψ → HasCompactSupport ψ →
        |(HRS.Whole.pair (HRS.Whole.empirical X) ψ - HRS.Whole.pair (HRS.Whole.withDensityReal ρ) ψ) -
            ∫ z, ψ z * uMol b X ρ z| ≤ C * L * b ^ (-(1 / 2 : ℝ)) := by
  refine ⟨2 * (2 : ℝ) ^ ((d : ℝ) / 2), by positivity, ?_⟩
  intro b hb ρ hρ N X hN ψ L hL hψ hc
  obtain ⟨hψc, ⟨B, hB⟩, hψi⟩ := p_wt5_psi_facts hL hψ hc
  set K := ∫ w : Euc d, ‖w‖ * molK b w with hK
  have hK0 : 0 ≤ K := integral_nonneg fun w => mul_nonneg (norm_nonneg _) (p_wt5_molK_nonneg hb w)
  have hKle : K ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * b ^ (-(1 / 2 : ℝ)) := (p_wt5_moment (d := d) hb).2
  have hρi : Integrable ρ := Integrable.of_integral_ne_zero (by rw [hρ.integral_one]; exact one_ne_zero)
  have hbd := fun y => p_wt5_Phi_bound hb hL hψ hψc hB y
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [p_wt5_pair_empirical hψc, p_wt5_pair_density hρ, p_wt5_main_identity hb hρ hψc hB]
  have hρψ : Integrable (fun y => ρ y * ψ y) := hρi.mul_bdd hψc.aestronglyMeasurable
    (Filter.Eventually.of_forall hB)
  have hρΦ := p_wt5_rhoPhi_integrable hb hρ hψc hB
  have e1 : (1 / (N : ℝ)) * ∑ i, ψ (X i) - (1 / (N : ℝ)) * ∑ i, p_wt5_Phi b ψ (X i) =
      (1 / (N : ℝ)) * ∑ i, (ψ (X i) - p_wt5_Phi b ψ (X i)) := by
    rw [Finset.sum_sub_distrib]; ring
  have e2 : (∫ y, ρ y * ψ y) - (∫ y, ρ y * p_wt5_Phi b ψ y) = ∫ y, ρ y * (ψ y - p_wt5_Phi b ψ y) := by
    rw [← integral_sub hρψ hρΦ]
    congr 1; funext y; ring
  have b1 : |(1 / (N : ℝ)) * ∑ i, (ψ (X i) - p_wt5_Phi b ψ (X i))| ≤ L * K := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / (N : ℝ))]
    have : |∑ i, (ψ (X i) - p_wt5_Phi b ψ (X i))| ≤ N * (L * K) := by
      calc _ ≤ ∑ i, |ψ (X i) - p_wt5_Phi b ψ (X i)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin N, (L * K) := Finset.sum_le_sum fun i _ => hbd (X i)
        _ = N * (L * K) := by simp
    calc 1 / (N : ℝ) * |∑ i, (ψ (X i) - p_wt5_Phi b ψ (X i))| ≤ 1 / (N : ℝ) * (N * (L * K)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = L * K := by field_simp
  have b2 : |∫ y, ρ y * (ψ y - p_wt5_Phi b ψ y)| ≤ L * K := by
    rw [← Real.norm_eq_abs]
    have hg : Integrable (fun y => (L * K) * ρ y) := hρi.const_mul _
    calc ‖∫ y, ρ y * (ψ y - p_wt5_Phi b ψ y)‖ ≤ ∫ y, (L * K) * ρ y := by
          refine norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall fun y => ?_)
          rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hρ.nonneg y), Real.norm_eq_abs, mul_comm]
          exact mul_le_mul_of_nonneg_right (hbd y) (hρ.nonneg y)
      _ = L * K := by rw [integral_const_mul, hρ.integral_one, mul_one]
  have key : (1 / (N : ℝ) * ∑ i, ψ (X i) - ∫ y, ρ y * ψ y) -
      (1 / (N : ℝ) * ∑ i, p_wt5_Phi b ψ (X i) - ∫ y, ρ y * p_wt5_Phi b ψ y) =
      (1 / (N : ℝ)) * ∑ i, (ψ (X i) - p_wt5_Phi b ψ (X i)) -
        ∫ y, ρ y * (ψ y - p_wt5_Phi b ψ y) := by
    linarith [e1, e2]
  rw [key]
  calc _ ≤ |(1 / (N : ℝ)) * ∑ i, (ψ (X i) - p_wt5_Phi b ψ (X i))| +
        |∫ y, ρ y * (ψ y - p_wt5_Phi b ψ y)| := abs_sub _ _
    _ ≤ L * K + L * K := add_le_add b1 b2
    _ ≤ 2 * (2 : ℝ) ^ ((d : ℝ) / 2) * L * b ^ (-(1 / 2 : ℝ)) := by
        have := mul_le_mul_of_nonneg_left hKle hL
        nlinarith

end HRS.MH.CoercTest
