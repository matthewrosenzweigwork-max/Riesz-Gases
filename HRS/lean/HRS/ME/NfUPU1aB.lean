import HRS.Equilibrium.PairCorrection
import HRS.ME.PmU
import HRS.ME.NfUPU1aA

/-!
# Packet PU1a, part B (uniform pair-correlation envelope integrals)

Uniform copies (namespace `HRS.ME.NfU`) of the following lemmas of `HRS/Equilibrium/PairCorrection.lean`.
Conventions as in `docs/MAIN_E_NF_PLAN.md` (rule for uniform statements) and `NfUPU1aA.lean`.

* `exp_pow4_mu_unif` of `HRS.PairCorrAux.exp_pow4_mu` (l.1632). Constant chosen before `ρ`; uses `conj_pow_unif`.
  Statement changed only in the hypothesis on `ρ`: `SmoothPosDensity ρ` and `ρ ≤ Λ`, with `1 ≤ Λ`.
* `exp_moments_unif` of `HRS.PairCorrAux.exp_moments` (l.1772). The constant is chosen before `κ ∈ Icc κm κp`
  and before `ρ`. The original `κ` is replaced by a range `κ ∈ Icc κm κp` with `0 < κm ≤ κp`, because
  `critical_envelope_integrals` uses `κ = a * β`. The `κ`-dependent constants are bounded by their values at `κm`
  (`|log κ| ≤ |log κm| + |log κp|`, `1/κ ≤ 1/κm`).
* `critical_envelope_integrals_unif` of `HRS.critical_envelope_integrals` (l.1968). The constant is chosen after
  `a > 0` and before `β ∈ Icc βm βp` and `ρ`, using `RhoU d βm βp c₀ Λ₀ β ρ` (`hβ`, `rho`, `hup`).
  The bound `ρ ≤ Λ₀` comes from `RhoU.hup`, and `Λ₀` replaces the bound `Λ` of `exists_density_bound`.
  The equality-free form of the original hypotheses (`0 < β`) is `RhoU.hβpos`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace HRS.ME.NfU

open HRS HRS.PairCorrAux HRS.PoleCavityAux HRS.KernelAux HRS.KernelAux2 HRS.ME.PmU

variable {d : ℕ}

/-- Uniform `exp_pow4_mu`: the constant `max (24 * Cv) 384` depends on `Λ` (and `d, s, c`), not on `ρ`. -/
theorem exp_pow4_mu_unif {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ u : ℝ, 0 < u → u ≤ 1 → ∀ x : Torus d,
      ∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y) ^ 4 * Real.exp (-u * gPlus d s c (x - y)))
          ∂(withDensityReal ρ) ≤ ENNReal.ofReal (C * (1 / u) ^ 2) := by
  obtain ⟨Cv, hCv, hv⟩ := conj_pow_unif hd hcrit c hc 4 (by norm_num) Λ hΛ
  refine ⟨max (24 * Cv) 384, by positivity, fun ρ hρ hΛρ u hu hu1 x => ?_⟩
  have := PoleCavityAux.isProbabilityMeasure_mu hρ
  set H : ℝ := 1 / u with hH
  have hH1 : 1 ≤ H := by rw [hH, le_div_iff₀ hu]; linarith
  have hpt : ∀ y, ENNReal.ofReal (gPlus d s c (x - y) ^ 4 * Real.exp (-u * gPlus d s c (x - y))) ≤
      ENNReal.ofReal 24 * ENNReal.ofReal (gTrunc d s c H (x - y) ^ (4:ℝ)) := by
    intro y
    rw [← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := pow4_exp_le (gPlus d s c (x - y)) u (hc _) hu
    rw [show gTrunc d s c H (x - y) ^ (4:ℝ) = gTrunc d s c H (x - y) ^ 4 by
      rw [← Real.rpow_natCast]; norm_num]
    exact this
  calc _ ≤ ∫⁻ y, ENNReal.ofReal 24 * ENNReal.ofReal (gTrunc d s c H (x - y) ^ (4:ℝ)) ∂(withDensityReal ρ) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal 24 * ∫⁻ y, ENNReal.ofReal (gTrunc d s c H (x - y) ^ (4:ℝ)) ∂(withDensityReal ρ) := by
        rw [lintegral_const_mul']
        exact ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (max (24 * Cv) 384 * H ^ 2) := by
        rcases le_or_gt 2 H with h2 | h2
        · have := hv ρ hρ hΛρ H h2 x
          calc _ ≤ ENNReal.ofReal 24 * ENNReal.ofReal (Cv * H ^ ((4:ℝ) - 2)) := by gcongr
            _ = ENNReal.ofReal (24 * (Cv * H ^ ((4:ℝ) - 2))) := (ENNReal.ofReal_mul (by norm_num)).symm
            _ ≤ _ := by
              refine ENNReal.ofReal_le_ofReal ?_
              rw [show ((4:ℝ) - 2) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
              have := le_max_left (24 * Cv) 384
              have hH2 : 0 ≤ H ^ 2 := by positivity
              nlinarith
        · have hb : ∀ y, ENNReal.ofReal (gTrunc d s c H (x - y) ^ (4:ℝ)) ≤ ENNReal.ofReal 16 := by
            intro y
            refine ENNReal.ofReal_le_ofReal ?_
            have h0 : 0 ≤ gTrunc d s c H (x - y) := le_min (hc _) (by linarith)
            have : gTrunc d s c H (x - y) ≤ 2 := (min_le_right _ _).trans h2.le
            rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]
            calc gTrunc d s c H (x - y) ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ h0 this 4
              _ = 16 := by norm_num
          calc ENNReal.ofReal 24 * ∫⁻ y, ENNReal.ofReal (gTrunc d s c H (x - y) ^ (4:ℝ)) ∂(withDensityReal ρ)
              ≤ ENNReal.ofReal 24 * ∫⁻ y, ENNReal.ofReal 16 ∂(withDensityReal ρ) :=
                mul_le_mul' le_rfl (lintegral_mono hb)
            _ = ENNReal.ofReal 24 * ENNReal.ofReal 16 := by simp
            _ = ENNReal.ofReal 384 := by rw [← ENNReal.ofReal_mul (by norm_num)]; norm_num
            _ ≤ _ := by
              refine ENNReal.ofReal_le_ofReal ?_
              have := le_max_right (24 * Cv) 384
              have hH2 : 1 ≤ H ^ 2 := one_le_pow₀ hH1
              nlinarith
    _ = _ := by rw [hH]

set_option maxHeartbeats 1000000 in
/-- Uniform `exp_moments`: the constant depends on `Λ, κm, κp` (and `d, s, c`), not on `κ ∈ Icc κm κp` or `ρ`. -/
theorem exp_moments_unif {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (Λ : ℝ) (hΛ : 1 ≤ Λ) (κm κp : ℝ)
    (hκm : 0 < κm) (_hκ : κm ≤ κp) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ κ ∈ Set.Icc κm κp, ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d,
      (∫⁻ y, ENNReal.ofReal (wEnv s x y ^ 2 * Real.exp (-(κ / N) * gPlus d s c (x - y)))
          ∂(withDensityReal ρ) ≤ ENNReal.ofReal (C * logEN N)) ∧
      (∫⁻ y, ENNReal.ofReal (wEnv s x y ^ 4 * Real.exp (-(κ / N) * gPlus d s c (x - y)))
          ∂(withDensityReal ρ) ≤ ENNReal.ofReal (C * (N : ℝ) ^ 2)) := by
  obtain ⟨C5, hC5, h5⟩ := conj_expo_unif hd hcrit c hc Λ hΛ
  obtain ⟨C4, hC4, h4⟩ := exp_pow4_mu_unif hd hcrit c hc Λ hΛ
  obtain ⟨A, hA, hAw⟩ := wEnv_le_gPlus hd hcrit c hc
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = |Real.log κm| + |Real.log κp| := ⟨_, rfl⟩
  obtain ⟨Cu, hCu⟩ : ∃ Cu : ℝ, Cu = max (2 * A ^ 2 * (1 + C5 * (1 + K) + C5))
      (8 * A ^ 4 * (1 + C4 * (1 / κm + 1) ^ 2)) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hCu0 : 0 ≤ Cu := by rw [hCu]; exact le_max_of_le_left (by positivity)
  refine ⟨Cu, hCu0, fun κ hκI ρ hρ hΛρ N hN x => ?_⟩
  obtain ⟨hκ1, hκ2⟩ := hκI
  have hκpos : 0 < κ := lt_of_lt_of_le hκm hκ1
  have hlogK : |Real.log κ| ≤ K := by rw [hK]; exact abs_log_le_of_mem hκm hκ1 hκ2
  have hinvκ : 1 / κ ≤ 1 / κm := one_div_le_one_div_of_le hκm hκ1
  have hC2le : 2 * A ^ 2 * (1 + C5 * (1 + |Real.log κ|) + C5) ≤ Cu := by
    rw [hCu]
    refine le_max_of_le_left ?_
    have h1 : C5 * (1 + |Real.log κ|) ≤ C5 * (1 + K) :=
      mul_le_mul_of_nonneg_left (by linarith) hC5.le
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hC4le : 8 * A ^ 4 * (1 + C4 * (1 / κ + 1) ^ 2) ≤ Cu := by
    rw [hCu]
    refine le_max_of_le_right ?_
    have hsq : (1 / κ + 1) ^ 2 ≤ (1 / κm + 1) ^ 2 :=
      pow_le_pow_left₀ (by have := one_div_pos.2 hκpos; linarith) (by linarith) 2
    have h3 : 1 + C4 * (1 / κ + 1) ^ 2 ≤ 1 + C4 * (1 / κm + 1) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hsq hC4.le
      linarith
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  set C2 : ℝ := 2 * A ^ 2 * (1 + C5 * (1 + |Real.log κ|) + C5) with hC2
  set C4' : ℝ := 8 * A ^ 4 * (1 + C4 * (1 / κ + 1) ^ 2) with hC4'
  have := PoleCavityAux.isProbabilityMeasure_mu hρ
  have hdR : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hN2 : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0:ℝ) < N := by linarith
  set u : ℝ := min (κ / N) 1 with hu
  have hu0 : 0 < u := lt_min (by positivity) one_pos
  have hu1 : u ≤ 1 := min_le_right _ _
  have huk : u ≤ κ / N := min_le_left _ _
  have hlogu : |Real.log u| ≤ Real.log N + |Real.log κ| := by
    have hlN : 0 ≤ Real.log N := Real.log_nonneg hN1
    rcases le_or_gt 1 (κ / N) with h | h
    · rw [hu, min_eq_right h, Real.log_one]; simp; positivity
    · rw [hu, min_eq_left h.le, Real.log_div hκpos.ne' hN0.ne']
      calc |Real.log κ - Real.log N| ≤ |Real.log κ| + |Real.log N| := abs_sub _ _
        _ = _ := by rw [abs_of_nonneg hlN]; ring
  have hexp : ∀ g : ℝ, 0 ≤ g → Real.exp (-(κ / N) * g) ≤ Real.exp (-u * g) := by
    intro g hg
    exact Real.exp_le_exp.2 (by nlinarith)
  have hE1 : ∀ g : ℝ, 0 ≤ g → Real.exp (-u * g) ≤ 1 := by
    intro g hg
    exact Real.exp_le_one_iff.2 (by nlinarith)
  have hlogEN := logEN_eq N (by omega)
  have hlN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hC2n : 0 ≤ C2 := by positivity
  have hC4n : 0 ≤ C4' := by positivity
  constructor
  · -- second moment
    have hpt : ∀ y, ENNReal.ofReal (wEnv s x y ^ 2 * Real.exp (-(κ / N) * gPlus d s c (x - y))) ≤
        ENNReal.ofReal (2 * A ^ 2) * (ENNReal.ofReal (Real.exp (-u * gPlus d s c (x - y))) +
          ENNReal.ofReal (gPlus d s c (x - y) ^ 2 * Real.exp (-u * gPlus d s c (x - y)))) := by
      intro y
      have hg := hc (x - y)
      set g := gPlus d s c (x - y) with hgdef
      have hg0 : 0 ≤ g := hg
      rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hw := hAw x y
      have hw1 := one_le_wEnv s x y
      have hw2 : wEnv s x y ^ 2 ≤ (A * (1 + g)) ^ 2 := pow_le_pow_left₀ (by linarith) hw 2
      have he := hexp g hg0
      have hE0 := Real.exp_pos (-u * g)
      calc wEnv s x y ^ 2 * Real.exp (-(κ / N) * g)
          ≤ (A * (1 + g)) ^ 2 * Real.exp (-u * g) := by
            apply mul_le_mul hw2 he (Real.exp_pos _).le (by positivity)
        _ ≤ 2 * A ^ 2 * (Real.exp (-u * g) + g ^ 2 * Real.exp (-u * g)) := by
            have : (A * (1 + g)) ^ 2 ≤ 2 * A ^ 2 * (1 + g ^ 2) := by nlinarith [sq_nonneg (1 - g), sq_nonneg A]
            calc (A * (1 + g)) ^ 2 * Real.exp (-u * g) ≤ 2 * A ^ 2 * (1 + g ^ 2) * Real.exp (-u * g) :=
                  mul_le_mul_of_nonneg_right this hE0.le
              _ = _ := by ring
    calc ∫⁻ y, ENNReal.ofReal (wEnv s x y ^ 2 * Real.exp (-(κ / N) * gPlus d s c (x - y))) ∂(withDensityReal ρ)
        ≤ ∫⁻ y, ENNReal.ofReal (2 * A ^ 2) * (ENNReal.ofReal (Real.exp (-u * gPlus d s c (x - y))) +
          ENNReal.ofReal (gPlus d s c (x - y) ^ 2 * Real.exp (-u * gPlus d s c (x - y)))) ∂(withDensityReal ρ) :=
          lintegral_mono hpt
      _ = ENNReal.ofReal (2 * A ^ 2) * ((∫⁻ y, ENNReal.ofReal (Real.exp (-u * gPlus d s c (x - y))) ∂(withDensityReal ρ)) +
          ∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y) ^ 2 * Real.exp (-u * gPlus d s c (x - y))) ∂(withDensityReal ρ)) := by
          have hmx : Measurable (fun y : Torus d => ENNReal.ofReal (Real.exp (-u * gPlus d s c (x - y)))) := by
            have : Measurable (fun y : Torus d => gPlus d s c (x - y)) :=
              (PoleCavityAux.measurable_gPlus hd (by rw [hcrit]; positivity) (by rw [hcrit]; linarith) c).comp
                (measurable_const.sub measurable_id)
            fun_prop
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left hmx]
      _ ≤ ENNReal.ofReal (2 * A ^ 2) * (ENNReal.ofReal 1 + ENNReal.ofReal (C5 * (1 + |Real.log u|))) := by
          gcongr
          · calc ∫⁻ y, ENNReal.ofReal (Real.exp (-u * gPlus d s c (x - y))) ∂(withDensityReal ρ)
                ≤ ∫⁻ y, ENNReal.ofReal 1 ∂(withDensityReal ρ) :=
                  lintegral_mono fun y => ENNReal.ofReal_le_ofReal (hE1 _ (hc _))
              _ = ENNReal.ofReal 1 := by simp
          · exact h5 ρ hρ hΛρ u hu0 hu1 x
      _ = ENNReal.ofReal (2 * A ^ 2 * (1 + C5 * (1 + |Real.log u|))) := by
          rw [← ENNReal.ofReal_add (by norm_num) (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (Cu * logEN N) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hlogEN]
          have hm : C2 ≤ Cu := hC2le
          have : 2 * A ^ 2 * (1 + C5 * (1 + |Real.log u|)) ≤ C2 * (1 + Real.log N) := by
            rw [hC2]
            have step : 1 + C5 * (1 + |Real.log u|) ≤
                (1 + C5 * (1 + |Real.log κ|) + C5) * (1 + Real.log N) := by
              have e1 : C5 * (1 + |Real.log u|) ≤ C5 * (1 + Real.log N + |Real.log κ|) :=
                mul_le_mul_of_nonneg_left (by linarith) hC5.le
              have e2 := mul_nonneg hC5.le hlN
              have e3 := mul_nonneg (mul_nonneg hC5.le (abs_nonneg (Real.log κ))) hlN
              nlinarith [e1, e2, e3, hlN]
            calc 2 * A ^ 2 * (1 + C5 * (1 + |Real.log u|))
                ≤ 2 * A ^ 2 * ((1 + C5 * (1 + |Real.log κ|) + C5) * (1 + Real.log N)) :=
                  mul_le_mul_of_nonneg_left step (by positivity)
              _ = _ := by ring
          nlinarith [mul_le_mul_of_nonneg_right hm (by linarith : (0:ℝ) ≤ 1 + Real.log N)]
  · -- fourth moment
    have hpt : ∀ y, ENNReal.ofReal (wEnv s x y ^ 4 * Real.exp (-(κ / N) * gPlus d s c (x - y))) ≤
        ENNReal.ofReal (8 * A ^ 4) * (ENNReal.ofReal (Real.exp (-u * gPlus d s c (x - y))) +
          ENNReal.ofReal (gPlus d s c (x - y) ^ 4 * Real.exp (-u * gPlus d s c (x - y)))) := by
      intro y
      have hg := hc (x - y)
      set g := gPlus d s c (x - y) with hgdef
      have hg0 : 0 ≤ g := hg
      rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hw := hAw x y
      have hw1 := one_le_wEnv s x y
      have hw2 : wEnv s x y ^ 4 ≤ (A * (1 + g)) ^ 4 := pow_le_pow_left₀ (by linarith) hw 4
      have he := hexp g hg0
      have hE0 := Real.exp_pos (-u * g)
      calc wEnv s x y ^ 4 * Real.exp (-(κ / N) * g)
          ≤ (A * (1 + g)) ^ 4 * Real.exp (-u * g) := by
            apply mul_le_mul hw2 he (Real.exp_pos _).le (by positivity)
        _ ≤ 8 * A ^ 4 * (Real.exp (-u * g) + g ^ 4 * Real.exp (-u * g)) := by
            have : (A * (1 + g)) ^ 4 ≤ 8 * A ^ 4 * (1 + g ^ 4) := by
              have h1 : (1 + g) ^ 4 ≤ 8 * (1 + g ^ 4) := by
                nlinarith [sq_nonneg (1 - g), sq_nonneg (1 + g), sq_nonneg (g ^ 2 - 1),
                  sq_nonneg (g - 1), mul_nonneg hg0 hg0, sq_nonneg (g ^ 2 - g)]
              calc (A * (1 + g)) ^ 4 = A ^ 4 * (1 + g) ^ 4 := by ring
                _ ≤ A ^ 4 * (8 * (1 + g ^ 4)) := mul_le_mul_of_nonneg_left h1 (by positivity)
                _ = _ := by ring
            calc (A * (1 + g)) ^ 4 * Real.exp (-u * g) ≤ 8 * A ^ 4 * (1 + g ^ 4) * Real.exp (-u * g) :=
                  mul_le_mul_of_nonneg_right this hE0.le
              _ = _ := by ring
    have hinvu : 1 / u ≤ N * (1 / κ + 1) := by
      rcases le_or_gt 1 (κ / N) with h | h
      · rw [hu, min_eq_right h]
        have : (1:ℝ) ≤ N * (1 / κ + 1) := by
          have : 0 ≤ (N:ℝ) * (1 / κ) := by positivity
          have e : (N:ℝ) * (1 / κ + 1) = N * (1 / κ) + N := by ring
          linarith
        simpa using this
      · rw [hu, min_eq_left h.le]
        have : 1 / (κ / N) = N / κ := by field_simp
        rw [this]
        have : (N:ℝ) / κ = N * (1 / κ) := by ring
        rw [this]
        have e : (N:ℝ) * (1 / κ + 1) = N * (1 / κ) + N := by ring
        linarith
    calc ∫⁻ y, ENNReal.ofReal (wEnv s x y ^ 4 * Real.exp (-(κ / N) * gPlus d s c (x - y))) ∂(withDensityReal ρ)
        ≤ ∫⁻ y, ENNReal.ofReal (8 * A ^ 4) * (ENNReal.ofReal (Real.exp (-u * gPlus d s c (x - y))) +
          ENNReal.ofReal (gPlus d s c (x - y) ^ 4 * Real.exp (-u * gPlus d s c (x - y)))) ∂(withDensityReal ρ) :=
          lintegral_mono hpt
      _ = ENNReal.ofReal (8 * A ^ 4) * ((∫⁻ y, ENNReal.ofReal (Real.exp (-u * gPlus d s c (x - y))) ∂(withDensityReal ρ)) +
          ∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y) ^ 4 * Real.exp (-u * gPlus d s c (x - y))) ∂(withDensityReal ρ)) := by
          have hmx : Measurable (fun y : Torus d => ENNReal.ofReal (Real.exp (-u * gPlus d s c (x - y)))) := by
            have : Measurable (fun y : Torus d => gPlus d s c (x - y)) :=
              (PoleCavityAux.measurable_gPlus hd (by rw [hcrit]; positivity) (by rw [hcrit]; linarith) c).comp
                (measurable_const.sub measurable_id)
            fun_prop
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left hmx]
      _ ≤ ENNReal.ofReal (8 * A ^ 4) * (ENNReal.ofReal 1 + ENNReal.ofReal (C4 * (1 / u) ^ 2)) := by
          gcongr
          · calc ∫⁻ y, ENNReal.ofReal (Real.exp (-u * gPlus d s c (x - y))) ∂(withDensityReal ρ)
                ≤ ∫⁻ y, ENNReal.ofReal 1 ∂(withDensityReal ρ) :=
                  lintegral_mono fun y => ENNReal.ofReal_le_ofReal (hE1 _ (hc _))
              _ = ENNReal.ofReal 1 := by simp
          · exact h4 ρ hρ hΛρ u hu0 hu1 x
      _ = ENNReal.ofReal (8 * A ^ 4 * (1 + C4 * (1 / u) ^ 2)) := by
          rw [← ENNReal.ofReal_add (by norm_num) (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (Cu * (N : ℝ) ^ 2) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hm : C4' ≤ Cu := hC4le
          have hu2 : (1 / u) ^ 2 ≤ (N * (1 / κ + 1)) ^ 2 :=
            pow_le_pow_left₀ (one_div_nonneg.2 hu0.le) hinvu 2
          have hN2' : 1 ≤ (N : ℝ) ^ 2 := one_le_pow₀ hN1
          have : 8 * A ^ 4 * (1 + C4 * (1 / u) ^ 2) ≤ C4' * (N : ℝ) ^ 2 := by
            rw [hC4']
            have h1 : C4 * (1 / u) ^ 2 ≤ C4 * (1 / κ + 1) ^ 2 * (N : ℝ) ^ 2 := by
              calc C4 * (1 / u) ^ 2 ≤ C4 * (N * (1 / κ + 1)) ^ 2 := mul_le_mul_of_nonneg_left hu2 hC4.le
                _ = _ := by ring
            have h2 : 1 ≤ (N : ℝ) ^ 2 := hN2'
            have h8 : 0 ≤ 8 * A ^ 4 := by positivity
            calc 8 * A ^ 4 * (1 + C4 * (1 / u) ^ 2)
                ≤ 8 * A ^ 4 * ((N : ℝ) ^ 2 + C4 * (1 / κ + 1) ^ 2 * (N : ℝ) ^ 2) :=
                  mul_le_mul_of_nonneg_left (by linarith) h8
              _ = _ := by ring
          nlinarith [mul_le_mul_of_nonneg_right hm (by positivity : (0:ℝ) ≤ (N:ℝ) ^ 2)]

/-- Uniform `critical_envelope_integrals` (Lemma 4.11): for each `a > 0` the constant depends on `a`, `Λ₀`,
`βm, βp` (and `d, s, c`), not on `β ∈ Icc βm βp` or `ρ`. The thermal hypothesis is `RhoU d βm βp c₀ Λ₀ β ρ`. -/
theorem critical_envelope_integrals_unif {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (βm βp c₀ Λ₀ : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (hΛ : 1 ≤ Λ₀) :
    ∀ a > 0, ∃ C : ℝ, ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, RhoU d βm βp c₀ Λ₀ β ρ →
      ∀ N : ℕ, 2 ≤ N →
      (∀ x : Torus d,
        ∫⁻ y, ENNReal.ofReal (wEnv s x y ^ 2 * Real.exp (-(a * (β / N)) * gPlus d s c (x - y)))
            ∂(withDensityReal ρ) ≤ ENNReal.ofReal (C * logEN N) ∧
        ∫⁻ y, ENNReal.ofReal (wEnv s x y ^ 4 * Real.exp (-(a * (β / N)) * gPlus d s c (x - y)))
            ∂(withDensityReal ρ) ≤ ENNReal.ofReal (C * (N : ℝ) ^ 2)) ∧
      (∀ x y : Torus d, x ≠ y →
        ∫⁻ z, ENNReal.ofReal (wEnv s x z * wEnv s y z) ∂(withDensityReal ρ) ≤
          ENNReal.ofReal (C * ellEnv x y)) ∧
      (∀ x y : Torus d, x ≠ y →
        ∫⁻ z, ENNReal.ofReal
            ((wEnv s x y * wEnv s x z + wEnv s x y * wEnv s y z + wEnv s x z * wEnv s y z) *
              min 1 ((β / N) * (1 + wEnv s x z + wEnv s y z))) ∂(withDensityReal ρ) ≤
          ENNReal.ofReal (C * (β / N) * wEnv s x y * (logEN N + ellEnv x y))) := by
  intro a ha
  have hΛ0 : 0 < Λ₀ := by linarith
  obtain ⟨Ce, hCe0, hexp⟩ := exp_moments_unif hd hcrit c hc Λ₀ hΛ (a * βm) (a * βp)
    (mul_pos ha hβm) (mul_le_mul_of_nonneg_left hββ ha.le)
  obtain ⟨Cp, hCp0, hpole⟩ := PairCorrAux.twopole_vol (d := d) hd hcrit
  obtain ⟨Cq, hCq0, hpin⟩ := PairCorrAux.pinprod_vol (d := d) hd hcrit
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = |Real.log βm| + |Real.log βp| := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = max Ce (max (Λ₀ * Cp) (Λ₀ * Cq * (1 + K))) := ⟨_, rfl⟩
  have hCe : Ce ≤ C := by rw [hC]; exact le_max_left _ _
  have hC2 : Λ₀ * Cp ≤ C := by rw [hC]; exact (le_max_left _ _).trans (le_max_right _ _)
  have hC3 : Λ₀ * Cq * (1 + K) ≤ C := by rw [hC]; exact (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, fun β hβI ρ hU => ?_⟩
  have hβ0 : 0 < β := hU.hβpos
  have hκI : a * β ∈ Set.Icc (a * βm) (a * βp) :=
    ⟨mul_le_mul_of_nonneg_left hU.hβge ha.le, mul_le_mul_of_nonneg_left hU.hβle ha.le⟩
  have hKβ : |Real.log β| ≤ K := by rw [hK]; exact abs_log_le_of_mem hβm hU.hβge hU.hβle
  intro N hN
  refine ⟨fun x => ?_, fun x y hxy => ?_, fun x y hxy => ?_⟩
  · have hN1 : 1 ≤ N := by omega
    have hL : 0 ≤ logEN N := by
      rw [PairCorrAux.logEN_eq N hN1]; linarith [Real.log_nonneg (by exact_mod_cast hN1 : (1:ℝ) ≤ N)]
    have e : a * (β / N) = a * β / N := by ring
    rw [e]
    obtain ⟨h1, h2⟩ := hexp (a * β) hκI ρ hU.rho hU.hup N hN x
    exact ⟨h1.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCe hL)),
      h2.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCe (by positivity)))⟩
  · calc ∫⁻ z, ENNReal.ofReal (wEnv s x z * wEnv s y z) ∂(withDensityReal ρ)
        ≤ ENNReal.ofReal Λ₀ * ∫⁻ z, ENNReal.ofReal (wEnv s x z * wEnv s y z) :=
          PoleCavityAux.lintegral_mu_le_vol hU.hup _
      _ ≤ ENNReal.ofReal Λ₀ * ENNReal.ofReal (Cp * ellEnv x y) := by gcongr; exact hpole x y hxy
      _ = ENNReal.ofReal (Λ₀ * (Cp * ellEnv x y)) := (ENNReal.ofReal_mul hΛ0.le).symm
      _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have : 0 ≤ ellEnv x y := by
          unfold ellEnv; linarith [PairCorrAux.log_one_div_nonneg x y]
        calc Λ₀ * (Cp * ellEnv x y) = (Λ₀ * Cp) * ellEnv x y := by ring
          _ ≤ C * ellEnv x y := mul_le_mul_of_nonneg_right hC2 this
  · have hN1 : 1 ≤ N := by omega
    have hN0 : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hlam : 0 < β / N := by positivity
    have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
    have hlog : |Real.log (β / N)| ≤ |Real.log β| + Real.log N := by
      rw [Real.log_div hβ0.ne' hN0.ne']
      calc |Real.log β - Real.log N| ≤ |Real.log β| + |Real.log N| := abs_sub _ _
        _ = _ := by rw [abs_of_nonneg hlogN]
    have hell : 1 ≤ ellEnv x y := by
      unfold ellEnv; linarith [PairCorrAux.log_one_div_nonneg x y]
    have hLN := PairCorrAux.logEN_eq N hN1
    have hC3' : Λ₀ * Cq * (1 + |Real.log β|) ≤ C := by
      have h := mul_le_mul_of_nonneg_left (show 1 + |Real.log β| ≤ 1 + K by linarith)
        (show 0 ≤ Λ₀ * Cq by positivity)
      linarith [h, hC3]
    calc ∫⁻ z, ENNReal.ofReal
            ((wEnv s x y * wEnv s x z + wEnv s x y * wEnv s y z + wEnv s x z * wEnv s y z) *
              min 1 ((β / N) * (1 + wEnv s x z + wEnv s y z))) ∂(withDensityReal ρ)
        ≤ ENNReal.ofReal Λ₀ * ∫⁻ z, ENNReal.ofReal
            ((wEnv s x y * wEnv s x z + wEnv s x y * wEnv s y z + wEnv s x z * wEnv s y z) *
              min 1 ((β / N) * (1 + wEnv s x z + wEnv s y z))) :=
          PoleCavityAux.lintegral_mu_le_vol hU.hup _
      _ ≤ ENNReal.ofReal Λ₀ * ENNReal.ofReal (Cq * (β / N) * wEnv s x y *
            (1 + |Real.log (β / N)| + ellEnv x y)) := by
          gcongr; exact hpin (β / N) hlam x y hxy
      _ = ENNReal.ofReal (Λ₀ * (Cq * (β / N) * wEnv s x y * (1 + |Real.log (β / N)| + ellEnv x y))) :=
          (ENNReal.ofReal_mul hΛ0.le).symm
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hw1 := PairCorrAux.one_le_wEnv s x y
          have h1 : 1 + |Real.log (β / N)| + ellEnv x y ≤
              (1 + |Real.log β|) * (logEN N + ellEnv x y) := by
            rw [hLN]
            nlinarith [abs_nonneg (Real.log β), mul_nonneg (abs_nonneg (Real.log β)) hlogN,
              mul_nonneg (abs_nonneg (Real.log β)) (by linarith : (0:ℝ) ≤ ellEnv x y)]
          have h0 : 0 ≤ Λ₀ * Cq * ((β / N) * wEnv s x y) := by positivity
          calc Λ₀ * (Cq * (β / N) * wEnv s x y * (1 + |Real.log (β / N)| + ellEnv x y))
              = Λ₀ * Cq * ((β / N) * wEnv s x y) * (1 + |Real.log (β / N)| + ellEnv x y) := by ring
            _ ≤ Λ₀ * Cq * ((β / N) * wEnv s x y) * ((1 + |Real.log β|) * (logEN N + ellEnv x y)) :=
                mul_le_mul_of_nonneg_left h1 h0
            _ = (Λ₀ * Cq * (1 + |Real.log β|)) * (β / N) * wEnv s x y * (logEN N + ellEnv x y) := by ring
            _ ≤ C * (β / N) * wEnv s x y * (logEN N + ellEnv x y) := by
                have : 0 ≤ (β / N) * wEnv s x y * (logEN N + ellEnv x y) := by
                  have : 0 ≤ logEN N := by
                    rw [hLN]; linarith
                  positivity
                calc (Λ₀ * Cq * (1 + |Real.log β|)) * (β / N) * wEnv s x y * (logEN N + ellEnv x y)
                    = (Λ₀ * Cq * (1 + |Real.log β|)) * ((β / N) * wEnv s x y * (logEN N + ellEnv x y)) := by ring
                  _ ≤ C * ((β / N) * wEnv s x y * (logEN N + ellEnv x y)) :=
                      mul_le_mul_of_nonneg_right hC3' this
                  _ = _ := by ring

end HRS.ME.NfU
