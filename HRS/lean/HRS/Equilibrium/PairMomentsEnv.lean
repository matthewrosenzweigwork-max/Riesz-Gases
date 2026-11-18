/-
# HRS.Equilibrium.PairMomentsEnv -- envelope integrals against `μ = ρ dx` (EQ-01b)

The pole envelope `w = 1 + r^{-s}`, `s = d/2`, integrated against a bounded density.
-/
import HRS.Equilibrium.PairMomentsRow

open MeasureTheory ProbabilityTheory Filter Topology Function
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.PairMom

open HRS HRS.External HRS.Quad

variable {d : ℕ} {s : ℝ}

/-- `∫ w dμ ≤ Λ B₀`. -/
theorem lintegral_mu_w (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {ρ : Torus d → ℝ} {Λ : ℝ}, (∀ x, ρ x ≤ Λ) → 0 ≤ Λ → ∀ x : Torus d,
      ∫⁻ y, ENNReal.ofReal (wEnv s x y) ∂(withDensityReal ρ) ≤ ENNReal.ofReal (Λ * B) := by
  have hcd := PairCorrAux.cdR_nonneg d
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by rw [hcrit]; linarith
  refine ⟨PairCorrAux.cdR d * ((1 / d + 1 / s) * 1 ^ s) + 2, by positivity, fun {ρ Λ} hΛ hΛ0 x => ?_⟩
  refine (PoleCavityAux.lintegral_mu_le_vol hΛ _).trans ?_
  rw [ENNReal.ofReal_mul hΛ0]
  exact mul_le_mul' le_rfl (PairCorrAux.radial_B0 hd hcrit x)

/-- `∫ w min{1, λ w} dμ ≤ Λ C λ (1 + |log λ|)`. -/
theorem lintegral_mu_cap (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ρ : Torus d → ℝ} {Λ : ℝ}, (∀ x, ρ x ≤ Λ) → 0 ≤ Λ → ∀ lam : ℝ, 0 < lam →
      ∀ x : Torus d,
      ∫⁻ y, ENNReal.ofReal (wEnv s x y * min 1 (lam * wEnv s x y)) ∂(withDensityReal ρ) ≤
        ENNReal.ofReal (Λ * (C * lam * (1 + |Real.log lam|))) := by
  obtain ⟨C, hC0, hC⟩ := PairCorrAux.cap_vol (d := d) hd hcrit
  refine ⟨C, hC0, fun {ρ Λ} hΛ hΛ0 lam hlam x => ?_⟩
  refine (PoleCavityAux.lintegral_mu_le_vol hΛ _).trans ?_
  rw [ENNReal.ofReal_mul hΛ0]
  exact mul_le_mul' le_rfl (hC lam hlam x)

/-- `∫ r^{-α} dx ≤ C` for `0 ≤ α < d` (Lebesgue measure on the torus, `r = min{1, |x-y|}`). -/
theorem lintegral_rTrunc_rpow (hd : 1 ≤ d) {α : ℝ} (hα0 : 0 ≤ α) (hα : α < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Torus d, ∫⁻ y, ENNReal.ofReal (rTrunc x y ^ (-α)) ≤ ENNReal.ofReal C := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set D : ℝ := d + 1 with hD
  have hD1 : 1 ≤ D := by rw [hD]; linarith
  have hD0 : 0 < D := by linarith
  set cc : ℝ := PairCorrAux.cdR d with hcc
  have hcc0 : 0 ≤ cc := PairCorrAux.cdR_nonneg d
  have hpe : (0 : ℝ) < (d : ℝ) - 1 - α + 1 := by linarith
  refine ⟨cc * (D ^ ((d : ℝ) - 1 - α + 1) / ((d : ℝ) - 1 - α + 1) + D * D ^ d),
    mul_nonneg hcc0 (add_nonneg (div_nonneg (Real.rpow_nonneg hD0.le _) hpe.le)
      (mul_nonneg hD0.le (pow_nonneg hD0.le _))), fun x => ?_⟩
  set F : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal ((min 1 t) ^ (-α)) with hF
  have hFm : Measurable F :=
    ENNReal.measurable_ofReal.comp ((measurable_const.min measurable_id).pow_const _)
  have h1 := PairCorrAux.lintegral_radial_torus hd x F hFm
  have e1 : ∀ y : Torus d, ENNReal.ofReal (rTrunc x y ^ (-α)) = F (Torus.eucDist x y) := fun y => rfl
  simp_rw [e1]
  refine h1.trans ?_
  have hp : (-1 : ℝ) < (d : ℝ) - 1 - α := by linarith
  have hpt : ∀ t ∈ Set.Ioc (0 : ℝ) D, ENNReal.ofReal (t ^ (d - 1)) * F t ≤
      ENNReal.ofReal (t ^ ((d : ℝ) - 1 - α)) + ENNReal.ofReal (D ^ d) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    by_cases h : t ≤ 1
    · have : F t = ENNReal.ofReal (t ^ (-α)) := by simp only [hF, min_eq_right h]
      rw [this, ← ENNReal.ofReal_mul (by positivity)]
      refine le_trans (le_of_eq ?_) le_self_add
      congr 1
      rw [show ((d : ℝ) - 1 - α) = ((d - 1 : ℕ) : ℝ) + (-α) by
        rw [Nat.cast_sub hd]; push_cast; ring, Real.rpow_add ht.1, Real.rpow_natCast]
    · push Not at h
      have : F t = ENNReal.ofReal 1 := by
        simp only [hF, min_eq_left h.le, Real.one_rpow]
      rw [this, ENNReal.ofReal_one, mul_one]
      refine le_trans ?_ le_add_self
      refine ENNReal.ofReal_le_ofReal ?_
      calc t ^ (d - 1) ≤ D ^ (d - 1) := pow_le_pow_left₀ ht.1.le ht.2 _
        _ ≤ D ^ d := pow_le_pow_right₀ hD1 (Nat.sub_le d 1)
  calc (d : ℝ≥0∞) * volume (Metric.ball (0 : Euc d) 1) *
        ∫⁻ t in Set.Ioc (0 : ℝ) D, ENNReal.ofReal (t ^ (d - 1)) * F t
      ≤ PairCorrAux.cd d * ∫⁻ t in Set.Ioc (0 : ℝ) D,
          (ENNReal.ofReal (t ^ ((d : ℝ) - 1 - α)) + ENNReal.ofReal (D ^ d)) := by
        refine mul_le_mul' le_rfl ?_
        exact setLIntegral_mono' measurableSet_Ioc hpt
    _ = PairCorrAux.cd d * (ENNReal.ofReal (D ^ ((d : ℝ) - 1 - α + 1) / ((d : ℝ) - 1 - α + 1)) +
          ENNReal.ofReal (D ^ d) * ENNReal.ofReal D) := by
        congr 1
        rw [lintegral_add_right _ measurable_const, PairCorrAux.lintegral_Ioc_rpow _ hp D hD0, setLIntegral_const,
          Real.volume_Ioc, sub_zero]
    _ = ENNReal.ofReal (cc * (D ^ ((d : ℝ) - 1 - α + 1) / ((d : ℝ) - 1 - α + 1) + D * D ^ d)) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
          PairCorrAux.cd_mul_ofReal]
        congr 2
        ring

theorem measurable_rTrunc (x : Torus d) : Measurable fun y : Torus d => rTrunc x y :=
  measurable_const.min (PairCorrAux.measurable_eucDist' x)

/-- `∫ r^{-α} dμ ≤ Λ C`. -/
theorem lintegral_mu_rpow (hd : 1 ≤ d) {α : ℝ} (hα0 : 0 ≤ α) (hα : α < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ρ : Torus d → ℝ} {Λ : ℝ}, (∀ x, ρ x ≤ Λ) → 0 ≤ Λ → ∀ x : Torus d,
      ∫⁻ y, ENNReal.ofReal (rTrunc x y ^ (-α)) ∂(withDensityReal ρ) ≤ ENNReal.ofReal (Λ * C) := by
  obtain ⟨C, hC0, hC⟩ := lintegral_rTrunc_rpow hd hα0 hα
  refine ⟨C, hC0, fun {ρ Λ} hΛ hΛ0 x => ?_⟩
  refine (PoleCavityAux.lintegral_mu_le_vol hΛ _).trans ?_
  rw [ENNReal.ofReal_mul hΛ0]
  exact mul_le_mul' le_rfl (hC x)

/-- Envelope data: a kernel envelope `Env` with its three row integrals against `μ`. -/
structure EnvBounds (s Cu : ℝ) (μ : Measure (Torus d)) (Env : Torus d → Torus d → ℝ) (BA BB BC : ℝ) :
    Prop where
  nonneg : ∀ x y, 0 ≤ Env x y
  A : ∀ x, ∫⁻ y, ENNReal.ofReal (Env x y) ∂μ ≤ ENNReal.ofReal BA
  B : ∀ x, ∫⁻ y, ENNReal.ofReal (Env x y ^ 2) ∂μ ≤ ENNReal.ofReal BB
  C : ∀ x, ∫⁻ y, ENNReal.ofReal (Env x y * (1 + Cu * wEnv s x y)) ∂μ ≤ ENNReal.ofReal BC

theorem rTrunc_rpow_one_le {x y : Torus d} (hxy : x ≠ y) {a : ℝ} (ha : 0 ≤ a) :
    1 ≤ rTrunc x y ^ (-a) :=
  Real.one_le_rpow_of_pos_of_le_one_of_nonpos (PairCorrAux.rTrunc_pos hxy) (PairCorrAux.rTrunc_le_one x y)
    (by linarith)

/-- Envelope data from a power bound `Env ≤ C_e r^{-a}` with `a < d`, `2a < d`, `a + s < d`. -/
theorem envBounds_of_rpow (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {a : ℝ} (ha0 : 0 ≤ a)
    (ha1 : a < d) (ha2 : 2 * a < d) (ha3 : a + s < d) (Ce Cu : ℝ) (hCe : 0 ≤ Ce) (hCu : 0 ≤ Cu)
    (ρ : Torus d → ℝ) {Λ : ℝ} (hΛ : ∀ x, ρ x ≤ Λ) (hΛ0 : 0 ≤ Λ)
    (Env : Torus d → Torus d → ℝ) (hE0 : ∀ x y, 0 ≤ Env x y)
    (hE : ∀ x y, x ≠ y → Env x y ≤ Ce * rTrunc x y ^ (-a)) :
    ∃ BA BB BC : ℝ, 0 ≤ BA ∧ 0 ≤ BB ∧ 0 ≤ BC ∧ EnvBounds (d := d) s Cu (withDensityReal ρ) Env BA BB BC := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by rw [hcrit]; linarith
  obtain ⟨Ca, hCa0, hCa⟩ := lintegral_mu_rpow (d := d) (by omega) ha0 ha1
  obtain ⟨Cb, hCb0, hCb⟩ := lintegral_mu_rpow (d := d) (by omega) (by linarith : 0 ≤ 2 * a) ha2
  obtain ⟨Cc, hCc0, hCc⟩ := lintegral_mu_rpow (d := d) (by omega) (by linarith : 0 ≤ a + s) ha3
  have hatom := fun z => Calib.atomless_withDensityReal (by omega : 1 ≤ d) ρ z
  have hae : ∀ x : Torus d, ∀ᵐ y ∂(withDensityReal ρ), x ≠ y :=
    fun x => (HRS.External.PoleVar.ae_ne_pt hatom x).mono fun y hy => Ne.symm hy
  have hmr : ∀ (b : ℝ) (x : Torus d), Measurable fun y => ENNReal.ofReal (rTrunc x y ^ (-b)) :=
    fun b x => ENNReal.measurable_ofReal.comp ((measurable_rTrunc x).pow_const _)
  refine ⟨Ce * (Λ * Ca), Ce ^ 2 * (Λ * Cb), Ce * (1 + 2 * Cu) * (Λ * Cc), by positivity, by positivity,
    by positivity, ⟨hE0, fun x => ?_, fun x => ?_, fun x => ?_⟩⟩
  · calc ∫⁻ y, ENNReal.ofReal (Env x y) ∂(withDensityReal ρ)
        ≤ ∫⁻ y, ENNReal.ofReal Ce * ENNReal.ofReal (rTrunc x y ^ (-a)) ∂(withDensityReal ρ) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hae x] with y hy
          rw [← ENNReal.ofReal_mul hCe]
          exact ENNReal.ofReal_le_ofReal (hE x y hy)
      _ = ENNReal.ofReal Ce * ∫⁻ y, ENNReal.ofReal (rTrunc x y ^ (-a)) ∂(withDensityReal ρ) :=
          lintegral_const_mul _ (hmr a x)
      _ ≤ ENNReal.ofReal Ce * ENNReal.ofReal (Λ * Ca) := by gcongr; exact hCa hΛ hΛ0 x
      _ = _ := (ENNReal.ofReal_mul hCe).symm
  · calc ∫⁻ y, ENNReal.ofReal (Env x y ^ 2) ∂(withDensityReal ρ)
        ≤ ∫⁻ y, ENNReal.ofReal (Ce ^ 2) * ENNReal.ofReal (rTrunc x y ^ (-(2 * a))) ∂(withDensityReal ρ) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hae x] with y hy
          rw [← ENNReal.ofReal_mul (sq_nonneg _)]
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 := hE x y hy
          have h2 : Env x y ^ 2 ≤ (Ce * rTrunc x y ^ (-a)) ^ 2 := pow_le_pow_left₀ (hE0 x y) h1 2
          calc Env x y ^ 2 ≤ (Ce * rTrunc x y ^ (-a)) ^ 2 := h2
            _ = Ce ^ 2 * rTrunc x y ^ (-(2 * a)) := by
                have : (rTrunc x y ^ (-a)) ^ 2 = rTrunc x y ^ (-(2 * a)) := by
                  rw [← Real.rpow_natCast, ← Real.rpow_mul (PairCorrAux.rTrunc_nonneg x y)]
                  congr 1; push_cast; ring
                rw [mul_pow, this]
      _ = ENNReal.ofReal (Ce ^ 2) * ∫⁻ y, ENNReal.ofReal (rTrunc x y ^ (-(2 * a))) ∂(withDensityReal ρ) :=
          lintegral_const_mul _ (hmr _ x)
      _ ≤ ENNReal.ofReal (Ce ^ 2) * ENNReal.ofReal (Λ * Cb) := by gcongr; exact hCb hΛ hΛ0 x
      _ = _ := (ENNReal.ofReal_mul (sq_nonneg _)).symm
  · calc ∫⁻ y, ENNReal.ofReal (Env x y * (1 + Cu * wEnv s x y)) ∂(withDensityReal ρ)
        ≤ ∫⁻ y, ENNReal.ofReal (Ce * (1 + 2 * Cu)) * ENNReal.ofReal (rTrunc x y ^ (-(a + s)))
          ∂(withDensityReal ρ) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hae x] with y hy
          rw [← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 := hE x y hy
          have hs1 : 1 ≤ rTrunc x y ^ (-s) := rTrunc_rpow_one_le hy hs0.le
          have hw : 1 + Cu * wEnv s x y ≤ (1 + 2 * Cu) * rTrunc x y ^ (-s) := by
            unfold wEnv
            nlinarith [mul_nonneg hCu (sub_nonneg.2 hs1)]
          have hr0 : 0 ≤ rTrunc x y ^ (-s) := (zero_le_one.trans hs1)
          calc Env x y * (1 + Cu * wEnv s x y) ≤ (Ce * rTrunc x y ^ (-a)) * ((1 + 2 * Cu) * rTrunc x y ^ (-s)) :=
                mul_le_mul h1 hw (by unfold wEnv; positivity) (by
                  have := Real.rpow_nonneg (PairCorrAux.rTrunc_nonneg x y) (-a)
                  positivity)
            _ = Ce * (1 + 2 * Cu) * rTrunc x y ^ (-(a + s)) := by
                rw [neg_add, Real.rpow_add (PairCorrAux.rTrunc_pos hy)]; ring
      _ = ENNReal.ofReal (Ce * (1 + 2 * Cu)) * ∫⁻ y, ENNReal.ofReal (rTrunc x y ^ (-(a + s)))
          ∂(withDensityReal ρ) := lintegral_const_mul _ (hmr _ x)
      _ ≤ ENNReal.ofReal (Ce * (1 + 2 * Cu)) * ENNReal.ofReal (Λ * Cc) := by gcongr; exact hCc hΛ hΛ0 x
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]

/-! ### The envelopes of `Q:eq:psi-size` -/

/-- The size envelope `1 + r^{2-s} + 1_{s=2}|log r|` of `ψ`. -/
def psiEnv (s : ℝ) (x y : Torus d) : ℝ :=
  1 + rTrunc x y ^ (2 - s) + if s = 2 then |Real.log (rTrunc x y)| else 0

/-- The envelope `1 + r^{1-s}` of `∇ψ`. -/
def gradEnv (s : ℝ) (x y : Torus d) : ℝ := 1 + rTrunc x y ^ (1 - s)

theorem psiEnv_nonneg (s : ℝ) (x y : Torus d) : 0 ≤ psiEnv s x y := by
  unfold psiEnv
  have h1 : 0 ≤ rTrunc x y ^ (2 - s) := Real.rpow_nonneg (PairCorrAux.rTrunc_nonneg x y) _
  split_ifs
  · positivity
  · linarith

theorem gradEnv_nonneg (s : ℝ) (x y : Torus d) : 0 ≤ gradEnv s x y := by
  unfold gradEnv
  have h1 : 0 ≤ rTrunc x y ^ (1 - s) := Real.rpow_nonneg (PairCorrAux.rTrunc_nonneg x y) _
  linarith

theorem measurable_psiEnv (s : ℝ) (x : Torus d) : Measurable (psiEnv s x) := by
  unfold psiEnv
  refine (measurable_const.add ((measurable_rTrunc x).pow_const _)).add ?_
  split_ifs
  · exact Real.measurable_log.comp (measurable_rTrunc x) |>.abs
  · exact measurable_const

theorem measurable_gradEnv (s : ℝ) (x : Torus d) : Measurable (gradEnv s x) := by
  unfold gradEnv
  exact measurable_const.add ((measurable_rTrunc x).pow_const _)

/-- Power bound for the size envelope: `psiEnv ≤ 6 r^{-a}`, `a = max(s-2,0) + 1/4`. -/
theorem psiEnv_le (s : ℝ) {x y : Torus d} (hxy : x ≠ y) :
    psiEnv s x y ≤ 6 * rTrunc x y ^ (-(max (s - 2) 0 + 1 / 4)) := by
  set r := rTrunc x y with hr
  have hr0 : 0 < r := PairCorrAux.rTrunc_pos hxy
  have hr1 : r ≤ 1 := PairCorrAux.rTrunc_le_one x y
  set a : ℝ := max (s - 2) 0 + 1 / 4 with ha
  have ha0 : 0 ≤ a := by rw [ha]; have := le_max_right (s - 2) 0; linarith
  have h1 : 1 ≤ r ^ (-a) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr0 hr1 (by linarith)
  have h2 : r ^ (2 - s) ≤ r ^ (-a) := by
    refine Real.rpow_le_rpow_of_exponent_ge hr0 hr1 ?_
    have := le_max_left (s - 2) 0
    rw [ha]; linarith
  have h3 : |Real.log r| ≤ 4 * r ^ (-a) := by
    have hlog : |Real.log r| = Real.log r⁻¹ := by
      rw [Real.log_inv, abs_of_nonpos (Real.log_nonpos hr0.le hr1)]
    rw [hlog]
    have := Real.log_le_rpow_div (inv_nonneg.2 hr0.le) (by norm_num : (0 : ℝ) < 1 / 4)
    have h4 : (r⁻¹) ^ (1 / 4 : ℝ) = r ^ (-(1 / 4 : ℝ)) := by
      rw [Real.inv_rpow hr0.le, ← Real.rpow_neg hr0.le]
    rw [h4] at this
    have h5 : r ^ (-(1 / 4 : ℝ)) ≤ r ^ (-a) := by
      refine Real.rpow_le_rpow_of_exponent_ge hr0 hr1 ?_
      have := le_max_right (s - 2) 0
      rw [ha]; linarith
    calc Real.log r⁻¹ ≤ r ^ (-(1 / 4 : ℝ)) / (1 / 4) := this
      _ = 4 * r ^ (-(1 / 4 : ℝ)) := by ring
      _ ≤ 4 * r ^ (-a) := by gcongr
  unfold psiEnv
  rw [← hr]
  split_ifs
  · linarith
  · linarith

theorem gradEnv_le {s : ℝ} (hs : 1 ≤ s) {x y : Torus d} (hxy : x ≠ y) :
    gradEnv s x y ≤ 2 * rTrunc x y ^ (-(s - 1)) := by
  unfold gradEnv
  have h1 : 1 ≤ rTrunc x y ^ (-(s - 1)) := rTrunc_rpow_one_le hxy (by linarith)
  have : rTrunc x y ^ (1 - s) = rTrunc x y ^ (-(s - 1)) := by congr 1; ring
  rw [this]; linarith

theorem psiEnv_bounds (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (Cu : ℝ) (hCu : 0 ≤ Cu)
    (ρ : Torus d → ℝ) {Λ : ℝ} (hΛ : ∀ x, ρ x ≤ Λ) (hΛ0 : 0 ≤ Λ) :
    ∃ BA BB BC : ℝ, 0 ≤ BA ∧ 0 ≤ BB ∧ 0 ≤ BC ∧
      EnvBounds (d := d) s Cu (withDensityReal ρ) (psiEnv s) BA BB BC := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ha : 0 ≤ max (s - 2) 0 + 1 / 4 := by have := le_max_right (s - 2) 0; linarith
  have key : ∀ b : ℝ, b = max (s - 2) 0 + 1 / 4 → b < d ∧ 2 * b < d ∧ b + s < d := by
    intro b hb
    rw [hb]
    rcases le_total (s - 2) 0 with h | h
    · rw [max_eq_right h]
      rw [hcrit] at h ⊢
      refine ⟨by linarith, by linarith, by linarith⟩
    · rw [max_eq_left h]
      rw [hcrit] at h ⊢
      refine ⟨by linarith, by linarith, by linarith⟩
  obtain ⟨k1, k2, k3⟩ := key _ rfl
  exact envBounds_of_rpow hd hcrit ha k1 k2 k3 6 Cu (by norm_num) hCu ρ hΛ hΛ0 (psiEnv s)
    (fun x y => psiEnv_nonneg s x y) (fun x y hxy => psiEnv_le s hxy)

theorem gradEnv_bounds (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (Cu : ℝ) (hCu : 0 ≤ Cu)
    (ρ : Torus d → ℝ) {Λ : ℝ} (hΛ : ∀ x, ρ x ≤ Λ) (hΛ0 : 0 ≤ Λ) :
    ∃ BA BB BC : ℝ, 0 ≤ BA ∧ 0 ≤ BB ∧ 0 ≤ BC ∧
      EnvBounds (d := d) s Cu (withDensityReal ρ) (gradEnv s) BA BB BC := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs1 : 1 ≤ s := by rw [hcrit]; linarith
  have ha : 0 ≤ s - 1 := by linarith
  have k1 : s - 1 < d := by rw [hcrit] at hs1 ⊢; linarith
  have k2 : 2 * (s - 1) < d := by rw [hcrit]; linarith
  have k3 : s - 1 + s < d := by rw [hcrit]; linarith
  exact envBounds_of_rpow hd hcrit ha k1 k2 k3 2 Cu (by norm_num) hCu ρ hΛ hΛ0 (gradEnv s)
    (fun x y => gradEnv_nonneg s x y) (fun x y hxy => gradEnv_le hs1 hxy)

end HRS.PairMom

end
