/-
# HRS.Equilibrium.PairMomentsT2 -- the second level of the three-particle estimate (EQ-01b)
-/
import HRS.Equilibrium.PairMomentsTriple
import HRS.Equilibrium.PairMomentsRow

open MeasureTheory ProbabilityTheory Filter Topology Function
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.PairMom

open HRS HRS.External HRS.Quad HRS.External.PoleVar

variable {d : ℕ} {s : ℝ}

section Ell

/-- `ℓ ≤ 5 r^{-1/4}`. -/
theorem ellEnv_le_rpow {x y : Torus d} (hxy : x ≠ y) :
    ellEnv x y ≤ 5 * rTrunc x y ^ (-(1 / 4 : ℝ)) := by
  set r := rTrunc x y with hr
  have hr0 : 0 < r := PairCorrAux.rTrunc_pos hxy
  have hr1 : r ≤ 1 := PairCorrAux.rTrunc_le_one x y
  have h1 : 1 ≤ r ^ (-(1 / 4 : ℝ)) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr0 hr1 (by norm_num)
  have h2 : Real.log (1 / r) ≤ 4 * r ^ (-(1 / 4 : ℝ)) := by
    have := Real.log_le_rpow_div (by positivity : (0 : ℝ) ≤ 1 / r) (by norm_num : (0 : ℝ) < 1 / 4)
    have h4 : (1 / r) ^ (1 / 4 : ℝ) = r ^ (-(1 / 4 : ℝ)) := by
      rw [one_div, Real.inv_rpow hr0.le, ← Real.rpow_neg hr0.le]
    rw [h4] at this
    calc Real.log (1 / r) ≤ r ^ (-(1 / 4 : ℝ)) / (1 / 4) := this
      _ = 4 * r ^ (-(1 / 4 : ℝ)) := by ring
  unfold ellEnv
  rw [← hr]
  linarith

theorem wEnv_le_two_rpow {x y : Torus d} (hxy : x ≠ y) {s : ℝ} (hs : 0 ≤ s) :
    wEnv s x y ≤ 2 * rTrunc x y ^ (-s) := by
  unfold wEnv
  have := rTrunc_rpow_one_le hxy hs
  linarith

theorem ellEnv_le_wEnv {x y : Torus d} (hxy : x ≠ y) {s : ℝ} (hs : 1 ≤ s) :
    ellEnv x y ≤ 5 * wEnv s x y := by
  have hr0 : 0 < rTrunc x y := PairCorrAux.rTrunc_pos hxy
  have hr1 : rTrunc x y ≤ 1 := PairCorrAux.rTrunc_le_one x y
  have h1 := ellEnv_le_rpow hxy
  have h2 : rTrunc x y ^ (-(1 / 4 : ℝ)) ≤ rTrunc x y ^ (-s) :=
    Real.rpow_le_rpow_of_exponent_ge hr0 hr1 (by linarith)
  have h3 : rTrunc x y ^ (-s) ≤ wEnv s x y := by unfold wEnv; linarith
  linarith

theorem one_le_ellEnv (x y : Torus d) : 1 ≤ ellEnv x y := by
  unfold ellEnv
  have := PairCorrAux.log_one_div_nonneg x y
  linarith

end Ell

section WEll

/-- `∫ w ℓ dμ ≤ Λ C`. -/
theorem lintegral_mu_wEll (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ρ : Torus d → ℝ} {Λ : ℝ}, (∀ x, ρ x ≤ Λ) → 0 ≤ Λ → ∀ x : Torus d,
      ∫⁻ y, ENNReal.ofReal (wEnv s x y * ellEnv x y) ∂(withDensityReal ρ) ≤ ENNReal.ofReal (Λ * C) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by rw [hcrit]; linarith
  have hα : s + 1 / 4 < d := by rw [hcrit]; linarith
  obtain ⟨C, hC0, hC⟩ := lintegral_mu_rpow (d := d) (by omega) (by linarith : 0 ≤ s + 1 / 4) hα
  refine ⟨10 * C, by positivity, fun {ρ Λ} hΛ hΛ0 x => ?_⟩
  have hatom := fun z => Calib.atomless_withDensityReal (by omega : 1 ≤ d) ρ z
  have hae : ∀ᵐ y ∂(withDensityReal ρ), x ≠ y :=
    (HRS.External.PoleVar.ae_ne_pt hatom x).mono fun y hy => Ne.symm hy
  have hmr : Measurable fun y => ENNReal.ofReal (rTrunc x y ^ (-(s + 1 / 4))) :=
    ENNReal.measurable_ofReal.comp ((measurable_rTrunc x).pow_const _)
  calc ∫⁻ y, ENNReal.ofReal (wEnv s x y * ellEnv x y) ∂(withDensityReal ρ)
      ≤ ∫⁻ y, ENNReal.ofReal 10 * ENNReal.ofReal (rTrunc x y ^ (-(s + 1 / 4))) ∂(withDensityReal ρ) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae] with y hy
        rw [← ENNReal.ofReal_mul (by norm_num)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := wEnv_le_two_rpow hy hs0.le
        have h2 := ellEnv_le_rpow hy
        have h3 := PairCorrAux.one_le_wEnv s x y
        have h4 := one_le_ellEnv x y
        calc wEnv s x y * ellEnv x y ≤ (2 * rTrunc x y ^ (-s)) * (5 * rTrunc x y ^ (-(1 / 4 : ℝ))) :=
              mul_le_mul h1 h2 (by linarith) (by
                have := Real.rpow_nonneg (PairCorrAux.rTrunc_nonneg x y) (-s); linarith)
          _ = 10 * rTrunc x y ^ (-(s + 1 / 4)) := by
              rw [neg_add, Real.rpow_add (PairCorrAux.rTrunc_pos hy)]; ring
    _ = ENNReal.ofReal 10 * ∫⁻ y, ENNReal.ofReal (rTrunc x y ^ (-(s + 1 / 4))) ∂(withDensityReal ρ) :=
        lintegral_const_mul _ hmr
    _ ≤ ENNReal.ofReal 10 * ENNReal.ofReal (Λ * C) := by gcongr; exact hC hΛ hΛ0 x
    _ = _ := by rw [← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring

end WEll

section LogExp

theorem sq_exp_neg_le {t : ℝ} (ht : 0 ≤ t) : t ^ 2 * Real.exp (-t) ≤ 2 := by
  have h1 : t ^ 2 / 2 ≤ Real.exp t := by
    have := Real.quadratic_le_exp_of_nonneg ht
    nlinarith [this]
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos t)]
  nlinarith

/-- `(log w)² e^{-κ w} ≤ 4 + 2 (log(1/κ))²` for `w ≥ 1`, `κ > 0`. -/
theorem log_sq_exp_le {κ w : ℝ} (hκ : 0 < κ) (hw : 1 ≤ w) :
    (Real.log w) ^ 2 * Real.exp (-κ * w) ≤ 4 + 2 * (Real.log (1 / κ)) ^ 2 := by
  have hw0 : 0 < w := by linarith
  have hlogw0 : 0 ≤ Real.log w := Real.log_nonneg hw
  have he1 : Real.exp (-κ * w) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have he0 : 0 < Real.exp (-κ * w) := Real.exp_pos _
  have hsq0 : 0 ≤ (Real.log (1 / κ)) ^ 2 := sq_nonneg _
  by_cases hkw : κ * w ≤ 1
  · -- w ≤ 1/κ
    have h1 : Real.log w ≤ Real.log (1 / κ) := by
      refine Real.log_le_log hw0 ?_
      rw [le_div_iff₀ hκ]; linarith
    have h2 : (Real.log w) ^ 2 ≤ (Real.log (1 / κ)) ^ 2 := pow_le_pow_left₀ hlogw0 h1 2
    calc (Real.log w) ^ 2 * Real.exp (-κ * w) ≤ (Real.log (1 / κ)) ^ 2 * 1 :=
          mul_le_mul h2 he1 he0.le hsq0
      _ ≤ _ := by linarith
  · push Not at hkw
    -- log w = log (κ w) + log (1/κ)
    have hlw : Real.log w = Real.log (κ * w) + Real.log (1 / κ) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1; field_simp
    have hlt0 : 0 ≤ Real.log (κ * w) := Real.log_nonneg hkw.le
    have hlt : Real.log (κ * w) ≤ κ * w := by
      have := Real.log_le_sub_one_of_pos (by positivity : 0 < κ * w)
      linarith
    have h3 : (Real.log w) ^ 2 ≤ 2 * (κ * w) ^ 2 + 2 * (Real.log (1 / κ)) ^ 2 := by
      rw [hlw]
      nlinarith [sq_nonneg (Real.log (κ * w) - Real.log (1 / κ)), mul_nonneg hlt0 hlt0,
        mul_le_mul hlt hlt hlt0 (by positivity : (0 : ℝ) ≤ κ * w)]
    have h4 : (κ * w) ^ 2 * Real.exp (-(κ * w)) ≤ 2 := sq_exp_neg_le (by positivity)
    have e : Real.exp (-κ * w) = Real.exp (-(κ * w)) := by congr 1; ring
    calc (Real.log w) ^ 2 * Real.exp (-κ * w)
        ≤ (2 * (κ * w) ^ 2 + 2 * (Real.log (1 / κ)) ^ 2) * Real.exp (-κ * w) :=
          mul_le_mul_of_nonneg_right h3 he0.le
      _ = 2 * ((κ * w) ^ 2 * Real.exp (-(κ * w))) + 2 * ((Real.log (1 / κ)) ^ 2 * Real.exp (-κ * w)) := by
          rw [e]; ring
      _ ≤ 2 * 2 + 2 * ((Real.log (1 / κ)) ^ 2 * 1) := by
          gcongr
      _ = 4 + 2 * (Real.log (1 / κ)) ^ 2 := by ring

end LogExp

section EllExp

theorem ellEnv_le_log {x y : Torus d} (hxy : x ≠ y) {s : ℝ} (hs : 0 < s) :
    ellEnv x y ≤ 1 + (1 / s) * Real.log (wEnv s x y) := by
  have hr0 : 0 < rTrunc x y := PairCorrAux.rTrunc_pos hxy
  have hw : rTrunc x y ^ (-s) ≤ wEnv s x y := by unfold wEnv; linarith
  have hpos : 0 < rTrunc x y ^ (-s) := Real.rpow_pos_of_pos hr0 _
  have h1 : Real.log (rTrunc x y ^ (-s)) ≤ Real.log (wEnv s x y) := Real.log_le_log hpos hw
  rw [Real.log_rpow hr0] at h1
  unfold ellEnv
  have : Real.log (1 / rTrunc x y) = -Real.log (rTrunc x y) := by
    rw [one_div, Real.log_inv]
  rw [this]
  have h2 : -Real.log (rTrunc x y) ≤ (1 / s) * Real.log (wEnv s x y) := by
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hs]
    linarith
  linarith

/-- `ℓ² e^{-(λ/2) g_+} ≤ C_ℓ L_N²`. -/
theorem ell_sq_exp_le (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∃ Cℓ : ℝ, 0 ≤ Cℓ ∧ ∀ N : ℕ, 2 ≤ N → ∀ x y : Torus d, x ≠ y →
      ellEnv x y ^ 2 * Real.exp (-(β / N / 2) * gPlus d s c (x - y)) ≤ Cℓ * logEN N ^ 2 := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by rw [hcrit]; linarith
  obtain ⟨A, hA, hAw⟩ := PairCorrAux.wEnv_le_gPlus hd hcrit c hc
  set a0 : ℝ := Real.log (2 * A / β) with ha0
  refine ⟨Real.exp β * (2 + 16 / s ^ 2 + 8 * a0 ^ 2 / s ^ 2), by positivity, fun N hN x y hxy => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hNp : (0 : ℝ) < N := by linarith
  have hLe := logEN_pos' (N := N) (by omega)
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hLeq : logEN N = 1 + Real.log N := PairCorrAux.logEN_eq N (by omega)
  set w := wEnv s x y with hwdef
  have hw1 : 1 ≤ w := PairCorrAux.one_le_wEnv s x y
  have hgp : w / A - 1 ≤ gPlus d s c (x - y) := by
    have := hAw x y
    rw [div_sub_one hA.ne', div_le_iff₀ hA]
    linarith
  set κ : ℝ := β / (2 * A * N) with hκdef
  have hκ : 0 < κ := by positivity
  have h1 : Real.exp (-(β / N / 2) * gPlus d s c (x - y)) ≤ Real.exp (β / 2) * Real.exp (-κ * w) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hl : 0 ≤ β / N / 2 := by positivity
    have := mul_le_mul_of_nonneg_left hgp hl
    have e : β / N / 2 * (w / A - 1) = κ * w - β / N / 2 := by
      rw [hκdef]; field_simp
    have hN2 : β / N / 2 ≤ β / 2 := by
      rw [div_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    nlinarith
  have h2 : ellEnv x y ^ 2 ≤ 2 + (2 / s ^ 2) * (Real.log w) ^ 2 := by
    have := ellEnv_le_log hxy hs0
    have h0 : 0 ≤ ellEnv x y := by linarith [one_le_ellEnv x y]
    have h3 : ellEnv x y ^ 2 ≤ (1 + (1 / s) * Real.log w) ^ 2 := pow_le_pow_left₀ h0 this 2
    have ha : (2 / s ^ 2) * (Real.log w) ^ 2 = 2 * ((1 / s) * Real.log w) ^ 2 := by field_simp
    rw [ha]
    nlinarith [sq_nonneg ((1 / s) * Real.log w - 1)]
  have h4 := log_sq_exp_le hκ hw1
  have h5 : Real.log (1 / κ) = a0 + Real.log N := by
    rw [hκdef, one_div, inv_div, ha0, ← Real.log_mul (by positivity) hNp.ne']
    congr 1; field_simp
  have h6 : (Real.log (1 / κ)) ^ 2 ≤ 2 * a0 ^ 2 + 2 * Real.log N ^ 2 := by
    rw [h5]; nlinarith [sq_nonneg (a0 - Real.log N)]
  have hlogL : Real.log N ≤ logEN N := by rw [hLeq]; linarith
  have he1 : Real.exp (-κ * w) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hE : 0 < Real.exp (β / 2) := Real.exp_pos _
  have hEβ : Real.exp (β / 2) ≤ Real.exp β := Real.exp_le_exp.2 (by linarith)
  calc ellEnv x y ^ 2 * Real.exp (-(β / N / 2) * gPlus d s c (x - y))
      ≤ (2 + (2 / s ^ 2) * (Real.log w) ^ 2) * (Real.exp (β / 2) * Real.exp (-κ * w)) :=
        mul_le_mul h2 h1 (Real.exp_pos _).le (by positivity)
    _ = Real.exp (β / 2) * (2 * Real.exp (-κ * w) + (2 / s ^ 2) * ((Real.log w) ^ 2 * Real.exp (-κ * w))) := by ring
    _ ≤ Real.exp (β / 2) * (2 * 1 + (2 / s ^ 2) * (4 + 2 * (Real.log (1 / κ)) ^ 2)) := by
        gcongr
    _ ≤ Real.exp (β / 2) * (2 + (2 / s ^ 2) * (4 + 2 * (2 * a0 ^ 2 + 2 * Real.log N ^ 2))) := by
        gcongr
        linarith
    _ ≤ Real.exp β * (2 + 16 / s ^ 2 + 8 * a0 ^ 2 / s ^ 2) * logEN N ^ 2 := by
        have hL2 : 1 ≤ logEN N ^ 2 := by nlinarith
        have hlog2 : Real.log N ^ 2 ≤ logEN N ^ 2 := pow_le_pow_left₀ hlogN0 hlogL 2
        have hs2 : 0 < s ^ 2 := by positivity
        have e : (2 + (2 / s ^ 2) * (4 + 2 * (2 * a0 ^ 2 + 2 * Real.log N ^ 2)))
            = 2 + 8 / s ^ 2 + 8 * a0 ^ 2 / s ^ 2 + 8 * Real.log N ^ 2 / s ^ 2 := by field_simp; ring
        rw [e]
        have h7 : 2 + 8 / s ^ 2 + 8 * a0 ^ 2 / s ^ 2 + 8 * Real.log N ^ 2 / s ^ 2 ≤
            (2 + 16 / s ^ 2 + 8 * a0 ^ 2 / s ^ 2) * logEN N ^ 2 := by
          have c1 : 0 ≤ 8 / s ^ 2 := by positivity
          have c2 : 0 ≤ 8 * a0 ^ 2 / s ^ 2 := by positivity
          have h8 : 8 * Real.log N ^ 2 / s ^ 2 ≤ 8 / s ^ 2 * logEN N ^ 2 := by
            calc 8 * Real.log N ^ 2 / s ^ 2 = (8 / s ^ 2) * Real.log N ^ 2 := by ring
              _ ≤ (8 / s ^ 2) * logEN N ^ 2 := mul_le_mul_of_nonneg_left hlog2 c1
          have key : (2 + 16 / s ^ 2 + 8 * a0 ^ 2 / s ^ 2) * logEN N ^ 2 -
              (2 + 8 / s ^ 2 + 8 * a0 ^ 2 / s ^ 2 + 8 * Real.log N ^ 2 / s ^ 2) =
              2 * (logEN N ^ 2 - 1) + (8 / s ^ 2) * (logEN N ^ 2 - 1) +
              (8 * a0 ^ 2 / s ^ 2) * (logEN N ^ 2 - 1) +
              ((8 / s ^ 2) * logEN N ^ 2 - 8 * Real.log N ^ 2 / s ^ 2) := by ring
          have hk : 0 ≤ (2 + 16 / s ^ 2 + 8 * a0 ^ 2 / s ^ 2) * logEN N ^ 2 -
              (2 + 8 / s ^ 2 + 8 * a0 ^ 2 / s ^ 2 + 8 * Real.log N ^ 2 / s ^ 2) := by
            rw [key]
            have h9 : 0 ≤ logEN N ^ 2 - 1 := by linarith
            have h10 : 0 ≤ (8 / s ^ 2) * logEN N ^ 2 - 8 * Real.log N ^ 2 / s ^ 2 := by linarith
            positivity
          linarith
        calc Real.exp (β / 2) * (2 + 8 / s ^ 2 + 8 * a0 ^ 2 / s ^ 2 + 8 * Real.log N ^ 2 / s ^ 2)
            ≤ Real.exp β * ((2 + 16 / s ^ 2 + 8 * a0 ^ 2 / s ^ 2) * logEN N ^ 2) :=
              mul_le_mul hEβ h7 (by positivity) (Real.exp_pos _).le
          _ = _ := by ring

end EllExp

section WEllExp

theorem measurable_w2_exp {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c e : ℝ) (x : Torus d) :
    Measurable fun y : Torus d => ENNReal.ofReal (wEnv s x y ^ 2 * Real.exp (-e * gPlus d s c (x - y))) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ s := by rw [hcrit]; linarith
  have hsd : s < d := by rw [hcrit]; linarith
  refine ENNReal.measurable_ofReal.comp ?_
  exact ((PairCorrAux.measurable_wEnv s x).pow_const 2).mul (Real.measurable_exp.comp
    (measurable_const.mul ((PoleCavityAux.measurable_gPlus hd hs0 hsd c).comp
      (measurable_const.sub measurable_id))))

/-- `∫ w² (L + ℓ)² e^{-λ g_+} dμ ≤ C L³` (`Q:eq:log-integral`). -/
theorem lintegral_wEll_exp (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d,
      ∫⁻ y, ENNReal.ofReal (wEnv s x y ^ 2 * (logEN N + ellEnv x y) ^ 2 *
        Real.exp (-(β / N) * gPlus d s c (x - y))) ∂(withDensityReal ρ) ≤ ENNReal.ofReal (C * logEN N ^ 3) := by
  have hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  obtain ⟨C1, hC1⟩ := critical_envelope_integrals hd hcrit β hβ ρ hρ c hc 1 one_pos
  obtain ⟨C2, hC2⟩ := critical_envelope_integrals hd hcrit β hβ ρ hρ c hc (1 / 2) (by norm_num)
  obtain ⟨Cl, hCl0, hCl⟩ := ell_sq_exp_le hd hcrit β hβ c hc
  have hatom := fun z => Calib.atomless_withDensityReal (by omega : 1 ≤ d) ρ z
  have hae : ∀ x : Torus d, ∀ᵐ y ∂(withDensityReal ρ), x ≠ y :=
    fun x => (HRS.External.PoleVar.ae_ne_pt hatom x).mono fun y hy => Ne.symm hy
  refine ⟨2 * max C1 0 + 2 * Cl * max C2 0, by positivity, fun N hN x => ?_⟩
  have hLe := logEN_pos' (N := N) (by omega)
  have hL0 : 0 ≤ logEN N := by linarith
  have hmw := measurable_w2_exp hd hcrit c (1 / 2 * (β / N)) x
  have hm1 := measurable_w2_exp hd hcrit c (β / N) x
  have hI1 : ∫⁻ y, ENNReal.ofReal (wEnv s x y ^ 2 * Real.exp (-(β / N) * gPlus d s c (x - y)))
      ∂(withDensityReal ρ) ≤ ENNReal.ofReal (max C1 0 * logEN N) := by
    have h := ((hC1 N hN).1 x).1
    simp only [one_mul] at h
    exact h.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hL0))
  have hI2 : ∫⁻ y, ENNReal.ofReal (wEnv s x y ^ 2 * Real.exp (-(1 / 2 * (β / N)) * gPlus d s c (x - y)))
      ∂(withDensityReal ρ) ≤ ENNReal.ofReal (max C2 0 * logEN N) := by
    refine ((hC2 N hN).1 x).1.trans ?_
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hL0)
  calc ∫⁻ y, ENNReal.ofReal (wEnv s x y ^ 2 * (logEN N + ellEnv x y) ^ 2 *
        Real.exp (-(β / N) * gPlus d s c (x - y))) ∂(withDensityReal ρ)
      ≤ ∫⁻ y, (ENNReal.ofReal (2 * logEN N ^ 2) * ENNReal.ofReal (wEnv s x y ^ 2 *
            Real.exp (-(β / N) * gPlus d s c (x - y))) +
          ENNReal.ofReal (2 * Cl * logEN N ^ 2) * ENNReal.ofReal (wEnv s x y ^ 2 *
            Real.exp (-(1 / 2 * (β / N)) * gPlus d s c (x - y)))) ∂(withDensityReal ρ) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae x] with y hy
        have hw1 := PairCorrAux.one_le_wEnv s x y
        have hg0 : 0 ≤ gPlus d s c (x - y) := hc _
        have hE2 : Real.exp (-(β / N) * gPlus d s c (x - y)) =
            Real.exp (-(β / N / 2) * gPlus d s c (x - y)) * Real.exp (-(1 / 2 * (β / N)) * gPlus d s c (x - y)) := by
          rw [← Real.exp_add]; congr 1; ring
        have hℓ := hCl N hN x y hy
        have hel0 := one_le_ellEnv x y
        have hE0 := Real.exp_pos (-(β / N) * gPlus d s c (x - y))
        have hE1 := Real.exp_pos (-(β / N / 2) * gPlus d s c (x - y))
        have hE3 := Real.exp_pos (-(1 / 2 * (β / N)) * gPlus d s c (x - y))
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hsq : (logEN N + ellEnv x y) ^ 2 ≤ 2 * logEN N ^ 2 + 2 * ellEnv x y ^ 2 := by
          nlinarith [sq_nonneg (logEN N - ellEnv x y)]
        calc wEnv s x y ^ 2 * (logEN N + ellEnv x y) ^ 2 * Real.exp (-(β / N) * gPlus d s c (x - y))
            ≤ wEnv s x y ^ 2 * (2 * logEN N ^ 2 + 2 * ellEnv x y ^ 2) *
                Real.exp (-(β / N) * gPlus d s c (x - y)) := by gcongr
          _ = 2 * logEN N ^ 2 * (wEnv s x y ^ 2 * Real.exp (-(β / N) * gPlus d s c (x - y))) +
              2 * (wEnv s x y ^ 2 * (ellEnv x y ^ 2 * Real.exp (-(β / N / 2) * gPlus d s c (x - y))) *
                Real.exp (-(1 / 2 * (β / N)) * gPlus d s c (x - y))) := by
              rw [hE2]; ring
          _ ≤ 2 * logEN N ^ 2 * (wEnv s x y ^ 2 * Real.exp (-(β / N) * gPlus d s c (x - y))) +
              2 * (wEnv s x y ^ 2 * (Cl * logEN N ^ 2) *
                Real.exp (-(1 / 2 * (β / N)) * gPlus d s c (x - y))) := by gcongr
          _ = _ := by ring
    _ = ENNReal.ofReal (2 * logEN N ^ 2) * ∫⁻ y, ENNReal.ofReal (wEnv s x y ^ 2 *
            Real.exp (-(β / N) * gPlus d s c (x - y))) ∂(withDensityReal ρ) +
        ENNReal.ofReal (2 * Cl * logEN N ^ 2) * ∫⁻ y, ENNReal.ofReal (wEnv s x y ^ 2 *
            Real.exp (-(1 / 2 * (β / N)) * gPlus d s c (x - y))) ∂(withDensityReal ρ) := by
        rw [lintegral_add_left (hm1.const_mul _), lintegral_const_mul _ hm1, lintegral_const_mul _ hmw]
    _ ≤ ENNReal.ofReal (2 * logEN N ^ 2) * ENNReal.ofReal (max C1 0 * logEN N) +
        ENNReal.ofReal (2 * Cl * logEN N ^ 2) * ENNReal.ofReal (max C2 0 * logEN N) := by
        gcongr
    _ ≤ _ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        nlinarith [le_refl (2 * max C1 0 * logEN N ^ 3), le_refl (2 * Cl * max C2 0 * logEN N ^ 3)]

end WEllExp

section Mean2

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ]

/-- **Refined mean under two pins** (`Q:eq:inner-triple-mean`): for `f` integrable with `μ[f] = 0`,
`|∑_k ∫ f dπ^{x,u}_k| ≤ m ∫ |f| (δ + C₂ min{1, (1 + q(z,x) + q(z,u))/N}) dμ`. -/
theorem mean_two_pins_le {V : WeakPotential μ} {β : ℝ} (hβ : 0 ≤ β) {m : ℕ} {δ C1 C2 : ℝ}
    (RD1 : RefDens V β (m + 1) δ C1) (RD2 : RefDens2 V β m C2) {f : Torus d → ℝ} (x u : Torus d)
    (hfμ : Integrable f μ) (h0 : ∫ y, f y ∂μ = 0)
    (hfπ : ∀ k : Fin m, Integrable f ((pinnedLaw V (β / ((m + 1 + 1 : ℕ) : ℝ)) m
      (pinsWith (pinsWith (fun e : Empty => e.elim) x) u)).map (fun Y => Y k)))
    {W : ℝ} (hW0 : 0 ≤ W)
    (hW : ∫⁻ z, ENNReal.ofReal (|f z| * (δ + C2 * min 1 ((1 / ((m + 1 + 1 : ℕ) : ℝ)) *
      (1 + V.q z x + V.q z u)))) ∂μ ≤ ENNReal.ofReal W) :
    |∑ k : Fin m, ∫ z, f z ∂((pinnedLaw V (β / ((m + 1 + 1 : ℕ) : ℝ)) m
      (pinsWith (pinsWith (fun e : Empty => e.elim) x) u)).map (fun Y => Y k))| ≤ m * W := by
  have hlam : 0 ≤ β / ((m + 1 + 1 : ℕ) : ℝ) := div_nonneg hβ (Nat.cast_nonneg _)
  have h1 : ∀ k : Fin m, |∫ z, f z ∂((pinnedLaw V (β / ((m + 1 + 1 : ℕ) : ℝ)) m
      (pinsWith (pinsWith (fun e : Empty => e.elim) x) u)).map (fun Y => Y k))| ≤ W := by
    intro k
    haveI : IsProbabilityMeasure (pinnedLaw V (β / ((m + 1 + 1 : ℕ) : ℝ)) m
        (pinsWith (pinsWith (fun e : Empty => e.elim) x) u)) := isProb_pinnedLaw V hlam m _
    refine abs_integral_marg_le (RD2.ac2 x u k) hfμ (hfπ k) h0 ?_ hW0 hW
    filter_upwards [RD2.cmp2 x u k, RD1.linf] with z hz1 hz2
    calc |(((pinnedLaw V (β / ((m + 1 + 1 : ℕ) : ℝ)) m (pinsWith (pinsWith (fun e : Empty => e.elim) x) u)).map
            (fun Y => Y k)).rnDeriv μ z).toReal - 1|
        ≤ |(((pinnedLaw V (β / ((m + 1 + 1 : ℕ) : ℝ)) m (pinsWith (pinsWith (fun e : Empty => e.elim) x) u)).map
            (fun Y => Y k)).rnDeriv μ z).toReal - (((pinnedLaw V (β / ((m + 1 + 1 : ℕ) : ℝ)) (m + 1 + 1)
              (fun e : Empty => e.elim)).map (fun Y => Y 0)).rnDeriv μ z).toReal| +
          |(((pinnedLaw V (β / ((m + 1 + 1 : ℕ) : ℝ)) (m + 1 + 1) (fun e : Empty => e.elim)).map
            (fun Y => Y 0)).rnDeriv μ z).toReal - 1| := abs_sub_le _ _ _
      _ ≤ _ := by linarith
  calc |∑ k : Fin m, ∫ z, f z ∂((pinnedLaw V (β / ((m + 1 + 1 : ℕ) : ℝ)) m
        (pinsWith (pinsWith (fun e : Empty => e.elim) x) u)).map (fun Y => Y k))|
      ≤ ∑ k : Fin m, |∫ z, f z ∂((pinnedLaw V (β / ((m + 1 + 1 : ℕ) : ℝ)) m
        (pinsWith (pinsWith (fun e : Empty => e.elim) x) u)).map (fun Y => Y k))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin m, W := Finset.sum_le_sum fun k _ => h1 k
    _ = m * W := by simp

end Mean2

/-! ### The second-level variance integral -/

section Lvl2Var

/-- The pole kernel `a(x,z) = w(x,z)² e^{-λ g_+(x-z)}`. -/
def aFun (s c lam : ℝ) (x z : Torus d) : ℝ := wEnv s x z ^ 2 * Real.exp (-lam * gPlus d s c (x - z))

theorem aFun_nonneg (s c lam : ℝ) (x z : Torus d) : 0 ≤ aFun s c lam x z := by
  unfold aFun; positivity

theorem measurable_aFun_uncurry (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c lam : ℝ) :
    Measurable fun p : Torus d × Torus d => aFun s c lam p.1 p.2 := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ s := by rw [hcrit]; linarith
  have hsd : s < d := by rw [hcrit]; linarith
  unfold aFun wEnv rTrunc
  have hdist : Measurable fun p : Torus d × Torus d => Torus.eucDist p.1 p.2 := by
    have : Continuous fun p : Torus d × Torus d => Torus.eucDist p.1 p.2 := by
      unfold Torus.eucDist
      refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => ?_)
      exact (continuous_norm.comp (((continuous_apply i).comp continuous_fst).sub
        ((continuous_apply i).comp continuous_snd))).pow 2
    exact this.measurable
  refine (measurable_const.add ((measurable_const.min hdist).pow_const _)).pow_const 2 |>.mul ?_
  exact Real.measurable_exp.comp (measurable_const.mul ((PoleCavityAux.measurable_gPlus hd hs0 hsd c).comp
    (measurable_fst.sub measurable_snd)))

end Lvl2Var

section Jint

variable {μ : Measure (Torus d)}

theorem aFun_symm (s c lam : ℝ) (x z : Torus d) : aFun s c lam x z = aFun s c lam z x := by
  unfold aFun
  rw [PairCorrAux.wEnv_symm s x z, ← neg_sub x z, gPlus_neg]

/-- `J(x,u) = ∫ a(x,z) a(u,z) dμ(z)`. -/
def Jfun (s c lam : ℝ) (μ : Measure (Torus d)) (x u : Torus d) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (aFun s c lam x z * aFun s c lam u z) ∂μ

theorem measurable_Jfun (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c lam : ℝ) [SFinite μ] (x : Torus d) :
    Measurable (Jfun s c lam μ x) := by
  have hm := measurable_aFun_uncurry (s := s) hd hcrit c lam
  have h1 : Measurable fun p : Torus d × Torus d => aFun s c lam x p.2 :=
    hm.comp (f := fun p : Torus d × Torus d => (x, p.2)) (measurable_const.prodMk measurable_snd)
  have h2 : Measurable fun p : Torus d × Torus d => ENNReal.ofReal (aFun s c lam x p.2 * aFun s c lam p.1 p.2) :=
    ENNReal.measurable_ofReal.comp (h1.mul hm)
  exact Measurable.lintegral_prod_right' (f := fun p : Torus d × Torus d =>
    ENNReal.ofReal (aFun s c lam x p.2 * aFun s c lam p.1 p.2)) h2

/-- `∫ J(x,u) dμ(u) ≤ B²` when `∫ a(y,z) dμ(z) ≤ B` for every `y`. -/
theorem lintegral_Jfun_le (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c lam : ℝ) [SFinite μ] (x : Torus d)
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ y : Torus d, ∫⁻ z, ENNReal.ofReal (aFun s c lam y z) ∂μ ≤ ENNReal.ofReal B) :
    ∫⁻ u, Jfun s c lam μ x u ∂μ ≤ ENNReal.ofReal B * ENNReal.ofReal B := by
  have hm := measurable_aFun_uncurry (s := s) hd hcrit c lam
  have h1 : Measurable fun p : Torus d × Torus d => aFun s c lam x p.2 :=
    hm.comp (f := fun p : Torus d × Torus d => (x, p.2)) (measurable_const.prodMk measurable_snd)
  have hmeas : Measurable fun p : Torus d × Torus d =>
      ENNReal.ofReal (aFun s c lam x p.2 * aFun s c lam p.1 p.2) :=
    ENNReal.measurable_ofReal.comp (h1.mul hm)
  unfold Jfun
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  calc ∫⁻ z, ∫⁻ u, ENNReal.ofReal (aFun s c lam x z * aFun s c lam u z) ∂μ ∂μ
      ≤ ∫⁻ z, ENNReal.ofReal (aFun s c lam x z) * ENNReal.ofReal B ∂μ := by
        refine lintegral_mono fun z => ?_
        have : ∀ u, ENNReal.ofReal (aFun s c lam x z * aFun s c lam u z) =
            ENNReal.ofReal (aFun s c lam x z) * ENNReal.ofReal (aFun s c lam z u) := by
          intro u
          rw [aFun_symm s c lam u z, ENNReal.ofReal_mul (aFun_nonneg s c lam x z)]
        simp_rw [this]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact mul_le_mul' le_rfl (hB z)
    _ = (∫⁻ z, ENNReal.ofReal (aFun s c lam x z) ∂μ) * ENNReal.ofReal B := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal B * ENNReal.ofReal B := mul_le_mul' (hB x) le_rfl

end Jint

section Var2

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ]

/-- The triple envelope `w(x,y) w(x,z) + w(x,y) w(y,z) + w(x,z) w(y,z)`. -/
def tEnv (s : ℝ) (x y z : Torus d) : ℝ :=
  wEnv s x y * wEnv s x z + wEnv s x y * wEnv s y z + wEnv s x z * wEnv s y z

theorem tEnv_nonneg (s : ℝ) (x y z : Torus d) : 0 ≤ tEnv s x y z := by
  have h1 := PairCorrAux.one_le_wEnv s x y
  have h2 := PairCorrAux.one_le_wEnv s x z
  have h3 := PairCorrAux.one_le_wEnv s y z
  unfold tEnv; positivity

/-- **The second-level variance integral** (`Q:eq:inner-triple-variance`):
`∫ |g₃(x,u,z)|² e^{M'+βγ+ψ_{x,u}(z)} dμ(z) ≤ 3K²E₂ [w(x,u)² (I(x) + I(u)) + J(x,u)]`. -/
theorem real_var2 {K E2 wxu wxz wuz e1 e2 : ℝ} (hE2 : 0 ≤ E2) (hxu : 0 ≤ wxu) (hxz : 0 ≤ wxz)
    (huz : 0 ≤ wuz) (he1 : 0 ≤ e1) (he1' : e1 ≤ 1) (he2 : 0 ≤ e2) (he2' : e2 ≤ 1) :
    (K * (wxu * wxz + wxu * wuz + wxz * wuz)) ^ 2 * (E2 * e1 * e2) ≤
      3 * K ^ 2 * E2 * (wxu ^ 2 * (wxz ^ 2 * e1) + wxu ^ 2 * (wuz ^ 2 * e2) + (wxz ^ 2 * e1) * (wuz ^ 2 * e2)) := by
  have h1 : (wxu * wxz + wxu * wuz + wxz * wuz) ^ 2 ≤
      3 * ((wxu * wxz) ^ 2 + (wxu * wuz) ^ 2 + (wxz * wuz) ^ 2) := by
    nlinarith [sq_nonneg (wxu * wxz - wxu * wuz), sq_nonneg (wxu * wxz - wxz * wuz),
      sq_nonneg (wxu * wuz - wxz * wuz)]
  have hK2 : 0 ≤ K ^ 2 * E2 := by positivity
  have e12 : e1 * e2 ≤ e1 := by nlinarith
  have e21 : e1 * e2 ≤ e2 := by nlinarith
  have e22 : e1 * e2 ≤ e1 * e2 := le_rfl
  calc (K * (wxu * wxz + wxu * wuz + wxz * wuz)) ^ 2 * (E2 * e1 * e2)
      = (K ^ 2 * E2) * ((wxu * wxz + wxu * wuz + wxz * wuz) ^ 2 * (e1 * e2)) := by ring
    _ ≤ (K ^ 2 * E2) * (3 * ((wxu * wxz) ^ 2 + (wxu * wuz) ^ 2 + (wxz * wuz) ^ 2) * (e1 * e2)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (by positivity)) hK2
    _ = (K ^ 2 * E2) * (3 * ((wxu * wxz) ^ 2 * (e1 * e2) + (wxu * wuz) ^ 2 * (e1 * e2) +
          (wxz * wuz) ^ 2 * (e1 * e2))) := by ring
    _ ≤ (K ^ 2 * E2) * (3 * (wxu ^ 2 * (wxz ^ 2 * e1) + wxu ^ 2 * (wuz ^ 2 * e2) +
          (wxz ^ 2 * e1) * (wuz ^ 2 * e2))) := by
        refine mul_le_mul_of_nonneg_left ?_ hK2
        have a1 : (wxu * wxz) ^ 2 * (e1 * e2) ≤ wxu ^ 2 * (wxz ^ 2 * e1) := by
          calc (wxu * wxz) ^ 2 * (e1 * e2) ≤ (wxu * wxz) ^ 2 * e1 :=
                mul_le_mul_of_nonneg_left e12 (by positivity)
            _ = _ := by ring
        have a2 : (wxu * wuz) ^ 2 * (e1 * e2) ≤ wxu ^ 2 * (wuz ^ 2 * e2) := by
          calc (wxu * wuz) ^ 2 * (e1 * e2) ≤ (wxu * wuz) ^ 2 * e2 :=
                mul_le_mul_of_nonneg_left e21 (by positivity)
            _ = _ := by ring
        have a3 : (wxz * wuz) ^ 2 * (e1 * e2) = (wxz ^ 2 * e1) * (wuz ^ 2 * e2) := by ring
        linarith
    _ = _ := by ring

theorem var2_bound (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {c Mmax M'max γmax Cq : ℝ} {V : WeakPotential μ}
    (hV : PotBound (d := d) s c Mmax M'max γmax Cq V) {β lam : ℝ} (hβ : 0 ≤ β) (hlam0 : 0 ≤ lam)
    (hlam : lam ≤ β) (hCq : 0 ≤ Cq) (hatom : ∀ z : Torus d, μ {z} = 0)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (K : ℝ) {g3 : Torus d → Torus d → Torus d → ℝ}
    (hg3 : ∀ x y z, x ≠ y → x ≠ z → y ≠ z → |g3 x y z| ≤ K * tEnv s x y z) {x u : Torus d}
    (hxu : x ≠ u) :
    ∫⁻ z, ‖g3 x u z‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
        pinField V lam (pinsWith (pinsWith (fun e : Empty => e.elim) x) u) z)) ∂μ ≤
      ENNReal.ofReal (3 * K ^ 2 * Real.exp (M'max + β * max γmax 0 + Mmax + 2 * (β * Cq))) *
        (ENNReal.ofReal (wEnv s x u ^ 2) * ((∫⁻ z, ENNReal.ofReal (aFun s c lam x z) ∂μ) +
          ∫⁻ z, ENNReal.ofReal (aFun s c lam u z) ∂μ) + Jfun s c lam μ x u) := by
  set E2 : ℝ := Real.exp (M'max + β * max γmax 0 + Mmax + 2 * (β * Cq)) with hE2
  have hE2p : 0 < E2 := Real.exp_pos _
  have hae : ∀ᵐ z ∂μ, z ≠ x ∧ z ≠ u :=
    (HRS.External.PoleVar.ae_ne_pt hatom x).and (HRS.External.PoleVar.ae_ne_pt hatom u)
  have hm := measurable_aFun_uncurry (s := s) hd hcrit c lam
  have hmx : Measurable fun z : Torus d => ENNReal.ofReal (aFun s c lam x z) :=
    ENNReal.measurable_ofReal.comp (hm.comp (f := fun z : Torus d => (x, z)) (measurable_const.prodMk measurable_id))
  have hmu : Measurable fun z : Torus d => ENNReal.ofReal (aFun s c lam u z) :=
    ENNReal.measurable_ofReal.comp (hm.comp (f := fun z : Torus d => (u, z)) (measurable_const.prodMk measurable_id))
  have hwxu := PairCorrAux.one_le_wEnv s x u
  have key : ∀ᵐ z ∂μ, ‖g3 x u z‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
        pinField V lam (pinsWith (pinsWith (fun e : Empty => e.elim) x) u) z)) ≤
      ENNReal.ofReal (3 * K ^ 2 * E2 * (wEnv s x u ^ 2 * aFun s c lam x z +
        wEnv s x u ^ 2 * aFun s c lam u z + aFun s c lam x z * aFun s c lam u z)) := by
    filter_upwards [hae] with z hz
    have hzx : x ≠ z := Ne.symm hz.1
    have hzu : u ≠ z := Ne.symm hz.2
    have hpe := pole2_exponent_le hV hβ hlam0 hlam hCq x u z hz.1 hz.2
    have hg := hg3 x u z hxu hzx hzu
    have hwxz := PairCorrAux.one_le_wEnv s x z
    have hwuz := PairCorrAux.one_le_wEnv s u z
    have hg1 : 0 ≤ gPlus d s c (x - z) := hc _
    have hg2 : 0 ≤ gPlus d s c (u - z) := hc _
    set e1 := Real.exp (-lam * gPlus d s c (x - z)) with he1
    set e2 := Real.exp (-lam * gPlus d s c (u - z)) with he2
    have he1' : e1 ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have he2' : e2 ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have he10 : 0 ≤ e1 := (Real.exp_pos _).le
    have he20 : 0 ≤ e2 := (Real.exp_pos _).le
    have hpole : Real.exp (V.M' + β * V.γ + pinField V lam
        (pinsWith (pinsWith (fun e : Empty => e.elim) x) u) z) ≤ E2 * e1 * e2 := by
      calc _ ≤ Real.exp ((M'max + β * max γmax 0 + Mmax + 2 * (β * Cq)) - lam * gPlus d s c (x - z) -
            lam * gPlus d s c (u - z)) := Real.exp_le_exp.2 hpe
        _ = E2 * e1 * e2 := by
            rw [hE2, he1, he2, ← Real.exp_add, ← Real.exp_add]
            congr 1; ring
    have h1 : ‖g3 x u z‖ₑ ^ 2 ≤ ENNReal.ofReal ((K * tEnv s x u z) ^ 2) := by
      rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      have := pow_le_pow_left₀ (abs_nonneg _) hg 2
      rwa [sq_abs] at this
    calc ‖g3 x u z‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
            pinField V lam (pinsWith (pinsWith (fun e : Empty => e.elim) x) u) z))
        ≤ ENNReal.ofReal ((K * tEnv s x u z) ^ 2) * ENNReal.ofReal (E2 * e1 * e2) :=
          mul_le_mul' h1 (ENNReal.ofReal_le_ofReal hpole)
      _ = ENNReal.ofReal ((K * tEnv s x u z) ^ 2 * (E2 * e1 * e2)) := (ENNReal.ofReal_mul (sq_nonneg _)).symm
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          unfold tEnv aFun
          exact real_var2 (K := K) hE2p.le (by linarith : 0 ≤ wEnv s x u) (by linarith : 0 ≤ wEnv s x z)
            (by linarith : 0 ≤ wEnv s u z) he10 he1' he20 he2'
  calc _ ≤ ∫⁻ z, ENNReal.ofReal (3 * K ^ 2 * E2 * (wEnv s x u ^ 2 * aFun s c lam x z +
        wEnv s x u ^ 2 * aFun s c lam u z + aFun s c lam x z * aFun s c lam u z)) ∂μ :=
        lintegral_mono_ae key
    _ = ∫⁻ z, ENNReal.ofReal (3 * K ^ 2 * E2) * (ENNReal.ofReal (wEnv s x u ^ 2) * ENNReal.ofReal (aFun s c lam x z) +
          ENNReal.ofReal (wEnv s x u ^ 2) * ENNReal.ofReal (aFun s c lam u z) +
          ENNReal.ofReal (aFun s c lam x z * aFun s c lam u z)) ∂μ := by
        refine lintegral_congr fun z => ?_
        have ha1 := aFun_nonneg s c lam x z
        have ha2 := aFun_nonneg s c lam u z
        have hw2 : 0 ≤ wEnv s x u ^ 2 := sq_nonneg _
        have hc0 : 0 ≤ 3 * K ^ 2 * E2 := by positivity
        have h1 : 0 ≤ wEnv s x u ^ 2 * aFun s c lam x z := mul_nonneg hw2 ha1
        have h2 : 0 ≤ wEnv s x u ^ 2 * aFun s c lam u z := mul_nonneg hw2 ha2
        have h3 : 0 ≤ aFun s c lam x z * aFun s c lam u z := mul_nonneg ha1 ha2
        rw [ENNReal.ofReal_mul hc0, ENNReal.ofReal_add (add_nonneg h1 h2) h3, ENNReal.ofReal_add h1 h2,
          ENNReal.ofReal_mul hw2, ENNReal.ofReal_mul hw2]
    _ = ENNReal.ofReal (3 * K ^ 2 * E2) * (ENNReal.ofReal (wEnv s x u ^ 2) * (∫⁻ z, ENNReal.ofReal (aFun s c lam x z) ∂μ +
          ∫⁻ z, ENNReal.ofReal (aFun s c lam u z) ∂μ) + Jfun s c lam μ x u) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        have hs1 : Measurable fun z : Torus d => ENNReal.ofReal (wEnv s x u ^ 2) * ENNReal.ofReal (aFun s c lam x z) :=
          hmx.const_mul _
        have hs2 : Measurable fun z : Torus d => ENNReal.ofReal (wEnv s x u ^ 2) * ENNReal.ofReal (aFun s c lam u z) :=
          hmu.const_mul _
        have hs12 : Measurable fun z : Torus d => ENNReal.ofReal (wEnv s x u ^ 2) * ENNReal.ofReal (aFun s c lam x z) +
            ENNReal.ofReal (wEnv s x u ^ 2) * ENNReal.ofReal (aFun s c lam u z) := hs1.add hs2
        rw [lintegral_add_left hs12, lintegral_add_left hs1, lintegral_const_mul _ hmx, lintegral_const_mul _ hmu,
          ← mul_add]
        rfl

end Var2

section TEnvInt

/-- `∫ tEnv dμ ≤ Λ (2 B w(x,u) + C_tp ℓ(x,u))`. -/
theorem lintegral_mu_tEnv (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) :
    ∃ B Ctp : ℝ, 0 ≤ B ∧ 0 ≤ Ctp ∧ ∀ {ρ : Torus d → ℝ} {Λ : ℝ}, (∀ x, ρ x ≤ Λ) → 0 ≤ Λ →
      ∀ x u : Torus d, x ≠ u →
      ∫⁻ z, ENNReal.ofReal (tEnv s x u z) ∂(withDensityReal ρ) ≤
        ENNReal.ofReal (Λ * (2 * B * wEnv s x u + Ctp * ellEnv x u)) := by
  obtain ⟨B, hB0, hB⟩ := lintegral_mu_w (s := s) hd hcrit
  obtain ⟨Ct, hCt0, hCt⟩ := PairCorrAux.twopole_vol (d := d) hd hcrit
  refine ⟨B, Ct, hB0, hCt0, fun {ρ Λ} hΛ hΛ0 x u hxu => ?_⟩
  have hw1 := PairCorrAux.one_le_wEnv s x u
  have hmx : Measurable fun z : Torus d => ENNReal.ofReal (wEnv s x z) :=
    ENNReal.measurable_ofReal.comp (PairCorrAux.measurable_wEnv s x)
  have hmu : Measurable fun z : Torus d => ENNReal.ofReal (wEnv s u z) :=
    ENNReal.measurable_ofReal.comp (PairCorrAux.measurable_wEnv s u)
  have hpt : ∀ z, ENNReal.ofReal (tEnv s x u z) = ENNReal.ofReal (wEnv s x u) * ENNReal.ofReal (wEnv s x z) +
      ENNReal.ofReal (wEnv s x u) * ENNReal.ofReal (wEnv s u z) +
      ENNReal.ofReal (wEnv s x z * wEnv s u z) := by
    intro z
    have h1 := PairCorrAux.one_le_wEnv s x z
    have h2 := PairCorrAux.one_le_wEnv s u z
    unfold tEnv
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
  simp_rw [hpt]
  have hs1 : Measurable fun z : Torus d => ENNReal.ofReal (wEnv s x u) * ENNReal.ofReal (wEnv s x z) := hmx.const_mul _
  have hs2 : Measurable fun z : Torus d => ENNReal.ofReal (wEnv s x u) * ENNReal.ofReal (wEnv s u z) := hmu.const_mul _
  have hs12 : Measurable fun z : Torus d => ENNReal.ofReal (wEnv s x u) * ENNReal.ofReal (wEnv s x z) +
      ENNReal.ofReal (wEnv s x u) * ENNReal.ofReal (wEnv s u z) := hs1.add hs2
  rw [lintegral_add_left hs12, lintegral_add_left hs1, lintegral_const_mul _ hmx, lintegral_const_mul _ hmu]
  have i1 := hB hΛ hΛ0 x
  have i2 := hB hΛ hΛ0 u
  have i3 : ∫⁻ z, ENNReal.ofReal (wEnv s x z * wEnv s u z) ∂(withDensityReal ρ) ≤
      ENNReal.ofReal (Λ * (Ct * ellEnv x u)) := by
    refine (PoleCavityAux.lintegral_mu_le_vol hΛ _).trans ?_
    rw [ENNReal.ofReal_mul hΛ0]
    exact mul_le_mul' le_rfl (hCt x u hxu)
  calc _ ≤ ENNReal.ofReal (wEnv s x u) * ENNReal.ofReal (Λ * B) + ENNReal.ofReal (wEnv s x u) * ENNReal.ofReal (Λ * B) +
        ENNReal.ofReal (Λ * (Ct * ellEnv x u)) := by gcongr
    _ = _ := by
        have := PairCorrAux.one_le_wEnv s x u
        have := one_le_ellEnv x u
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

/-- The capped triple-pole integral (`Q:eq:pin-product-integral`) against `μ`. -/
theorem lintegral_mu_tEnv_cap (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) :
    ∃ Cp : ℝ, 0 ≤ Cp ∧ ∀ {ρ : Torus d → ℝ} {Λ : ℝ}, (∀ x, ρ x ≤ Λ) → 0 ≤ Λ → ∀ lam : ℝ, 0 < lam →
      ∀ x u : Torus d, x ≠ u →
      ∫⁻ z, ENNReal.ofReal (tEnv s x u z * min 1 (lam * (1 + wEnv s x z + wEnv s u z))) ∂(withDensityReal ρ) ≤
        ENNReal.ofReal (Λ * (Cp * lam * wEnv s x u * (1 + |Real.log lam| + ellEnv x u))) := by
  obtain ⟨Cp, hCp0, hCp⟩ := PairCorrAux.pinprod_vol (d := d) hd hcrit
  refine ⟨Cp, hCp0, fun {ρ Λ} hΛ hΛ0 lam hlam x u hxu => ?_⟩
  refine (PoleCavityAux.lintegral_mu_le_vol hΛ _).trans ?_
  rw [ENNReal.ofReal_mul hΛ0]
  exact mul_le_mul' le_rfl (hCp lam hlam x u hxu)

end TEnvInt

end HRS.PairMom

end
