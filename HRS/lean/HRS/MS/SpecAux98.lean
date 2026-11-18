import HRS.MS.SpecAux97

/-!
# S8M: the uniform `L⁴(μ)` bound for `∇U` (S8.7, R4)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_X_L4`: there is `A ≥ 0`, depending only on `d, s, ρ, β`, such that for every
Schwartz `φ` with `W₂ = ∫ ρ (φ/√ρ)² ≤ β` and `∫ ‖∇e‖² dμ = ω` (`e = s8p_E φ`), `∫ ‖∇U‖⁴ dμ ≤ A (1 + ω)²`.
Proof: `‖∇U‖ ≤ g * ‖∇h‖` (`s8p_DU_norm_le`), `‖∇h‖ ≤ ρ ‖∇w‖ + |w| ‖∇ρ‖`, `∇w = β(∇e - ∇U)`, the `L²` bound
`s8p_DU_L2` and the master estimate `s8p_master`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace ContDiff

namespace HRS.MS.Spec

open HRS HRS.Whole HRS.MS.MovDec

variable {d : ℕ} {s : ℝ} {ρ : Euc d → ℝ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

/-- Cauchy-Schwarz for the probability density `ρ`. -/
theorem s8p_cs_rho {M : ℝ} (hM : S8pRho d s ρ M) {f : Euc d → ℝ}
    (h1 : Integrable (fun x => ρ x * f x)) (h2 : Integrable (fun x => ρ x * f x ^ 2)) :
    (∫ x, ρ x * f x) ^ 2 ≤ ∫ x, ρ x * f x ^ 2 := by
  set m := ∫ x, ρ x * f x with hm
  have hint : Integrable (fun x => ρ x * f x ^ 2 - 2 * m * (ρ x * f x) + m ^ 2 * ρ x) :=
    (h2.sub (h1.const_mul (2 * m))).add (hM.int.const_mul (m ^ 2))
  have h0 : 0 ≤ ∫ x, (ρ x * f x ^ 2 - 2 * m * (ρ x * f x) + m ^ 2 * ρ x) := by
    refine integral_nonneg fun x => ?_
    have : ρ x * f x ^ 2 - 2 * m * (ρ x * f x) + m ^ 2 * ρ x = ρ x * (f x - m) ^ 2 := by ring
    rw [this]
    exact mul_nonneg (hM.nonneg x) (sq_nonneg _)
  have hA : Integrable (fun x => ρ x * f x ^ 2 - 2 * m * (ρ x * f x)) := h2.sub (h1.const_mul (2 * m))
  have hB : Integrable (fun x => m ^ 2 * ρ x) := hM.int.const_mul _
  rw [integral_add hA hB, integral_sub h2 (h1.const_mul (2 * m)), integral_const_mul, integral_const_mul,
    hM.one, ← hm] at h0
  nlinarith

theorem s8p_L4_alg {A0 M B0 β c3 κ om n m1 I1 I2 : ℝ} (hA0 : 0 ≤ A0) (hM0 : 0 ≤ M) (hB0 : 0 ≤ B0)
    (hβ : 0 ≤ β) (hc3 : 0 ≤ c3) (hκ : 0 ≤ κ) (hom : 0 ≤ om) (hn0 : 0 ≤ n) (hm10 : 0 ≤ m1)
    (hm1n : m1 ^ 2 ≤ n) (hnle : n ≤ κ * (1 + om)) (hI20 : 0 ≤ I2) (hI10 : 0 ≤ I1)
    (hI2 : I2 ≤ 2 * M * n + 2 * (B0 * β)) (hI1 : I1 ≤ m1 + c3) :
    A0 * (I2 ^ 2 + I1 ^ 4) ≤ 8 * A0 * ((M ^ 2 + 1) * κ ^ 2 + B0 ^ 2 * β ^ 2 + c3 ^ 4) * (1 + om) ^ 2 := by
  have e1 : I2 ^ 2 ≤ 8 * M ^ 2 * n ^ 2 + 8 * B0 ^ 2 * β ^ 2 := by
    have := pow_le_pow_left₀ hI20 hI2 2
    nlinarith [sq_nonneg (2 * M * n - 2 * (B0 * β))]
  have e2 : I1 ^ 4 ≤ 8 * n ^ 2 + 8 * c3 ^ 4 := by
    have h1 := pow_le_pow_left₀ hI10 hI1 4
    have h2 : (m1 + c3) ^ 4 ≤ 8 * (m1 ^ 4 + c3 ^ 4) := by
      nlinarith [sq_nonneg (m1 ^ 2 - c3 ^ 2), sq_nonneg (m1 - c3), sq_nonneg (m1 + c3),
        mul_nonneg hm10 hc3, sq_nonneg (m1 * c3), mul_nonneg (mul_nonneg hm10 hc3) (sq_nonneg (m1 - c3))]
    have h3 : m1 ^ 4 ≤ n ^ 2 := by
      have := pow_le_pow_left₀ (sq_nonneg m1) hm1n 2
      nlinarith
    nlinarith
  have hn2 : n ^ 2 ≤ κ ^ 2 * (1 + om) ^ 2 := by
    have := pow_le_pow_left₀ hn0 hnle 2
    nlinarith
  have hom1 : 1 ≤ (1 + om) ^ 2 := by nlinarith
  have h2 : 8 * M ^ 2 * n ^ 2 + 8 * B0 ^ 2 * β ^ 2 + (8 * n ^ 2 + 8 * c3 ^ 4) ≤
      8 * ((M ^ 2 + 1) * κ ^ 2 + B0 ^ 2 * β ^ 2 + c3 ^ 4) * (1 + om) ^ 2 := by
    have a1 : 8 * M ^ 2 * n ^ 2 ≤ 8 * M ^ 2 * (κ ^ 2 * (1 + om) ^ 2) :=
      mul_le_mul_of_nonneg_left hn2 (by positivity)
    have a2 : 8 * n ^ 2 ≤ 8 * (κ ^ 2 * (1 + om) ^ 2) := mul_le_mul_of_nonneg_left hn2 (by norm_num)
    have a3 : 8 * B0 ^ 2 * β ^ 2 ≤ 8 * B0 ^ 2 * β ^ 2 * (1 + om) ^ 2 :=
      le_mul_of_one_le_right (by positivity) hom1
    have a4 : 8 * c3 ^ 4 ≤ 8 * c3 ^ 4 * (1 + om) ^ 2 := le_mul_of_one_le_right (by positivity) hom1
    nlinarith
  calc A0 * (I2 ^ 2 + I1 ^ 4)
      ≤ A0 * (8 * ((M ^ 2 + 1) * κ ^ 2 + B0 ^ 2 * β ^ 2 + c3 ^ 4) * (1 + om) ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hA0
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
theorem s8p_X_L4 (hd : 1 ≤ d) (hs0 : 0 < s) (hsd : s < d) (h32 : 3 * s / 2 < d) (hρ : Mov2eRho d ρ)
    (hE : Mov2eEll d ρ) {M : ℝ} (hM : S8pRho d s ρ M) {β : ℝ} (hβ : 0 < β) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (φ : 𝓢R) (om : ℝ), s8p_W2 ρ φ ≤ β →
      Integrable (fun x => ‖fderiv ℝ (s8p_E d s β ρ φ) x‖ ^ 2) (HRS.Whole.withDensityReal ρ) →
      ∫ x, ‖fderiv ℝ (s8p_E d s β ρ φ) x‖ ^ 2 ∂(HRS.Whole.withDensityReal ρ) = om →
      Integrable (fun x => ‖fderiv ℝ (s8p_U d s ρ φ) x‖ ^ 4) (HRS.Whole.withDensityReal ρ) ∧
        ∫ x, ‖fderiv ℝ (s8p_U d s ρ φ) x‖ ^ 4 ∂(HRS.Whole.withDensityReal ρ) ≤ A * (1 + om) ^ 2 := by
  obtain ⟨τ, hτ0, hτ⟩ := s8p_DU_L2 hd hs0 hsd h32 hρ hE hM hβ
  obtain ⟨A0, hA00, hA0⟩ := s8p_master hM h32
  obtain ⟨B0, hB00, hB0, hLint⟩ := s8p_lgr_bounds hρ hE
  set L0 : ℝ := ∫ x, ρ x * ‖s8p_lgr ρ x‖ ^ 2 with hL0
  have hL00 : 0 ≤ L0 := integral_nonneg fun x => mul_nonneg (hρ.pos x).le (sq_nonneg _)
  have hM0 : 0 ≤ M := le_trans (hM.nonneg 0) (hM.le 0)
  set c3 : ℝ := (β + L0) / 2 with hc3
  set κ : ℝ := 2 * β ^ 2 * (9 + 8 * d * τ) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  refine ⟨8 * A0 * ((M ^ 2 + 1) * κ ^ 2 + B0 ^ 2 * β ^ 2 + c3 ^ 4), by positivity,
    fun φ om hW hint hom => ?_⟩
  haveI := mov2e_isProb hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  have hom0 : 0 ≤ om := hom ▸ integral_nonneg fun x => sq_nonneg _
  obtain ⟨hUint, hUle⟩ := hτ φ om hW hint hom
  have hsmU := s8p_U_smooth hd hs0.le hsd hρ hE φ
  have hsmE := s8p_E_smooth hd hs0.le hsd hρ hE β φ
  have hsmW := s8p_ws_smooth hρ φ
  -- the weighted integrals of ‖∇E‖², ‖∇U‖², ‖∇w‖²
  have hEint : Integrable (fun x => ρ x * ‖fderiv ℝ (s8p_E d s β ρ φ) x‖ ^ 2) :=
    (mov2e_integrable_mu hρ).1 hint
  have hUint' : Integrable (fun x => ρ x * ‖fderiv ℝ (s8p_U d s ρ φ) x‖ ^ 2) :=
    (mov2e_integrable_mu hρ).1 hUint
  have hEval : ∫ x, ρ x * ‖fderiv ℝ (s8p_E d s β ρ φ) x‖ ^ 2 = om := by
    rw [← mov2e_integral_mu hρ]; exact hom
  have hUval : ∫ x, ρ x * ‖fderiv ℝ (s8p_U d s ρ φ) x‖ ^ 2 ≤ 8 * (om + d * τ) := by
    rw [← mov2e_integral_mu hρ]; exact hUle
  set Dw : Euc d → ℝ := fun x => ‖fderiv ℝ (s8p_ws ρ φ) x‖ with hDw
  have hDwc : Continuous Dw := ((hsmW.continuous_fderiv (by simp)).norm)
  have hDwsq : ∀ x, Dw x ^ 2 ≤ 2 * β ^ 2 * (‖fderiv ℝ (s8p_E d s β ρ φ) x‖ ^ 2 +
      ‖fderiv ℝ (s8p_U d s ρ φ) x‖ ^ 2) := by
    intro x
    have h1 : Dw x ≤ β * (‖fderiv ℝ (s8p_E d s β ρ φ) x‖ + ‖fderiv ℝ (s8p_U d s ρ φ) x‖) := by
      simp only [hDw]
      rw [s8p_fderiv_ws_eq hd hs0.le hsd hρ hE hβ φ x, norm_smul, Real.norm_of_nonneg hβ.le]
      exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) hβ.le
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (‖fderiv ℝ (s8p_E d s β ρ φ) x‖ - ‖fderiv ℝ (s8p_U d s ρ φ) x‖), sq_nonneg β]
  have hDwint : Integrable (fun x => ρ x * Dw x ^ 2) := by
    refine Integrable.mono' ((hEint.add hUint').const_mul (2 * β ^ 2)) ?_
      (Filter.Eventually.of_forall fun x => ?_)
    · exact (hρ.data.smooth.continuous.mul (hDwc.pow 2)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hρ.pos x).le (sq_nonneg _))]
      have := mul_le_mul_of_nonneg_left (hDwsq x) (hρ.pos x).le
      simp only [Pi.add_apply]
      nlinarith [this]
  set n : ℝ := ∫ x, ρ x * Dw x ^ 2 with hn
  have hn0 : 0 ≤ n := integral_nonneg fun x => mul_nonneg (hρ.pos x).le (sq_nonneg _)
  have hnle : n ≤ κ * (1 + om) := by
    have h1 : n ≤ ∫ x, 2 * β ^ 2 * (ρ x * ‖fderiv ℝ (s8p_E d s β ρ φ) x‖ ^ 2 +
        ρ x * ‖fderiv ℝ (s8p_U d s ρ φ) x‖ ^ 2) := by
      refine integral_mono hDwint ((hEint.add hUint').const_mul (2 * β ^ 2)) fun x => ?_
      have := mul_le_mul_of_nonneg_left (hDwsq x) (hρ.pos x).le
      nlinarith [this]
    rw [integral_const_mul, integral_add hEint hUint', hEval] at h1
    have h2 : (om + ∫ x, ρ x * ‖fderiv ℝ (s8p_U d s ρ φ) x‖ ^ 2) ≤ om + 8 * (om + d * τ) := by linarith
    have h3 : 0 ≤ 2 * β ^ 2 := by positivity
    have h4 : (d : ℝ) * τ * 8 ≤ (d : ℝ) * τ * 8 * (1 + om) := by
      have : 0 ≤ (d : ℝ) * τ * 8 := by positivity
      nlinarith
    calc n ≤ 2 * β ^ 2 * (om + ∫ x, ρ x * ‖fderiv ℝ (s8p_U d s ρ φ) x‖ ^ 2) := h1
      _ ≤ 2 * β ^ 2 * (om + 8 * (om + d * τ)) := mul_le_mul_of_nonneg_left h2 h3
      _ ≤ κ * (1 + om) := by
          rw [hκ]
          nlinarith [mul_nonneg h3 hom0, mul_nonneg h3 (mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hτ0) hom0)]
  -- the master estimate for F = ‖∇U‖ against G = ‖∇h‖
  set Gh : Euc d → ℝ := fun y => ‖fderiv ℝ (mov2eH ρ φ) y‖ with hGhdef
  have hGh := s8p_Gh_good hρ φ
  have hGh0 : ∀ y, 0 ≤ Gh y := fun y => norm_nonneg _
  have hGh2 : Integrable (fun y => Gh y ^ 2) := by
    obtain ⟨m, hm⟩ := hGh.2.2
    refine Integrable.mono' (hGh.2.1.const_mul m) (hGh.1.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 : Gh y ≤ m := (le_abs_self _).trans (hm y)
    nlinarith [hGh0 y]
  set F : Euc d → ℝ := fun x => ‖fderiv ℝ (s8p_U d s ρ φ) x‖ with hF
  have hFm : Measurable F := (hsmU.continuous_fderiv (by simp)).norm.measurable
  have hFle : ∀ x, ENNReal.ofReal |F x| ≤ ∫⁻ y, ENNReal.ofReal (rieszKernel d s (x - y) * Gh y) := by
    intro x
    have hI := hGh.conv_int hs0 hsd x
    have hnn : 0 ≤ᵐ[volume] fun y => rieszKernel d s (x - y) * Gh y :=
      Filter.Eventually.of_forall fun y => mul_nonneg (s8p_riesz_nonneg hs0 _) (hGh0 y)
    rw [← ofReal_integral_eq_lintegral_ofReal hI hnn]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hF]; simp only
    rw [abs_of_nonneg (norm_nonneg _)]
    exact s8p_DU_norm_le hd hs0 hsd hρ φ x
  obtain ⟨hI4, hbd⟩ := hA0 Gh F hGh.1 hGh0 hGh.2.1 hGh2 hFm hFle
  -- bounds on ∫ Gh² and ∫ Gh
  have hGtq := s8p_Gt_sq hρ hE φ hB00 hB0
  have hGt1 := s8p_Gt_int_le hρ hE φ hLint
  have hρDw : Integrable (fun x => ρ x * Dw x) := by
    refine Integrable.mono' (hM.int.add hDwint) (hρ.data.smooth.continuous.mul hDwc).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hρ.pos x).le (norm_nonneg _))]
    show ρ x * Dw x ≤ ρ x + ρ x * Dw x ^ 2
    nlinarith [mul_nonneg (hρ.pos x).le (sq_nonneg (Dw x - 1)), (hρ.pos x).le]
  set m1 : ℝ := ∫ x, ρ x * Dw x with hm1
  have hm10 : 0 ≤ m1 := integral_nonneg fun x => mul_nonneg (hρ.pos x).le (norm_nonneg _)
  have hm1n : m1 ^ 2 ≤ n := s8p_cs_rho hM hρDw hDwint
  have hGhle : ∀ y, Gh y ≤ ρ y * Dw y + s8p_Gt ρ φ y := fun y => s8p_Gh_le hρ φ y
  have hGt0 := s8p_Gt_nonneg ρ φ
  have hI2 : ∫ y, Gh y ^ 2 ≤ 2 * M * n + 2 * (B0 * β) := by
    have hpt : ∀ y, Gh y ^ 2 ≤ 2 * M * (ρ y * Dw y ^ 2) + 2 * s8p_Gt ρ φ y ^ 2 := by
      intro y
      have h1 := pow_le_pow_left₀ (hGh0 y) (hGhle y) 2
      have hp := hρ.pos y
      have hρM := hM.le y
      have h2 : (ρ y * Dw y) ^ 2 ≤ M * (ρ y * Dw y ^ 2) := by
        have : (ρ y * Dw y) ^ 2 = ρ y * (ρ y * Dw y ^ 2) := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_right hρM (mul_nonneg hp.le (sq_nonneg _))
      nlinarith [sq_nonneg (ρ y * Dw y - s8p_Gt ρ φ y)]
    have hint2 : Integrable (fun y => 2 * M * (ρ y * Dw y ^ 2) + 2 * s8p_Gt ρ φ y ^ 2) :=
      (hDwint.const_mul (2 * M)).add (hGtq.1.const_mul 2)
    calc ∫ y, Gh y ^ 2 ≤ ∫ y, (2 * M * (ρ y * Dw y ^ 2) + 2 * s8p_Gt ρ φ y ^ 2) :=
          integral_mono hGh2 hint2 hpt
      _ = 2 * M * n + 2 * ∫ y, s8p_Gt ρ φ y ^ 2 := by
          rw [integral_add (hDwint.const_mul (2 * M)) (hGtq.1.const_mul 2), integral_const_mul,
            integral_const_mul]
      _ ≤ 2 * M * n + 2 * (B0 * β) := by
          have : ∫ y, s8p_Gt ρ φ y ^ 2 ≤ B0 * β :=
            hGtq.2.trans (mul_le_mul_of_nonneg_left hW hB00)
          linarith
  have hI1 : ∫ y, Gh y ≤ m1 + c3 := by
    have hint1 : Integrable (fun y => ρ y * Dw y + s8p_Gt ρ φ y) := hρDw.add (s8p_Gt_good hρ hE φ).2.1
    calc ∫ y, Gh y ≤ ∫ y, (ρ y * Dw y + s8p_Gt ρ φ y) := integral_mono hGh.2.1 hint1 hGhle
      _ = m1 + ∫ y, s8p_Gt ρ φ y := integral_add hρDw (s8p_Gt_good hρ hE φ).2.1
      _ ≤ m1 + c3 := by
          have h1 : s8p_W2 ρ φ ≤ β := hW
          have : ∫ y, s8p_Gt ρ φ y ≤ c3 := hGt1.trans (by rw [hc3]; linarith)
          linarith
  have hI20 : 0 ≤ ∫ y, Gh y ^ 2 := integral_nonneg fun y => sq_nonneg _
  have hI10 : 0 ≤ ∫ y, Gh y := integral_nonneg hGh0
  -- assemble
  have hc30 : 0 ≤ c3 := by rw [hc3]; positivity
  have hI20 : 0 ≤ ∫ y, Gh y ^ 2 := integral_nonneg fun y => sq_nonneg _
  have hI10 : 0 ≤ ∫ y, Gh y := integral_nonneg hGh0
  have hfin : ∫ x, ρ x * F x ^ 4 ≤ 8 * A0 * ((M ^ 2 + 1) * κ ^ 2 + B0 ^ 2 * β ^ 2 + c3 ^ 4) * (1 + om) ^ 2 :=
    hbd.trans (s8p_L4_alg hA00 hM0 hB00 hβ.le hc30 hκ0 hom0 hn0 hm10 hm1n hnle hI20 hI10 hI2 hI1)
  refine ⟨?_, ?_⟩
  · rw [mov2e_integrable_mu hρ]
    exact hI4
  · rw [mov2e_integral_mu hρ]
    exact hfin

end HRS.MS.Spec
