import HRS.Equilibrium.PairMomentsT2
import HRS.Equilibrium.PairMomentsEnv
import HRS.Equilibrium.PairMomentsBase
import HRS.ME.PmU
import HRS.ME.NfUPU1aB

/-!
# Packet PU1b, part A (uniform envelope integrals, `β`-range and `ρ`-uniform)

Uniform copies (namespace `HRS.ME.NfU`) of the following lemmas (rule for uniform statements in
`docs/MAIN_E_NF_PLAN.md`). In each copy the constant is chosen after the fixed data `d, s, βm, βp, c₀, Λ₀`
(and the kernel data `c`, the envelope data `Env, Cu, …`) and before `β ∈ Set.Icc βm βp` and `ρ`.
The thermal hypothesis is `RhoU d βm βp c₀ Λ₀ β ρ` where the original has `SmoothPosDensity ρ` with
`0 < β`; the bound `ρ ≤ Λ` of the original envelope lemmas becomes `ρ ≤ Λ₀` (fixed, `1 ≤ Λ₀`).

* `ell_sq_exp_le_unif` of `HRS.PairMom.ell_sq_exp_le` (PairMomentsT2 l.173). The constant `Cℓ` is bounded by
  its value at `β = βp`; the only `β`-dependent quantity `a0 = log (2A/β)` is bounded by
  `|log (2A/βp)| + |log (2A/βm)|`. No density.
* `lintegral_wEll_exp_unif` of `HRS.PairMom.lintegral_wEll_exp` (PairMomentsT2 l.277). Uses
  `critical_envelope_integrals_unif` (PU1a) and `ell_sq_exp_le_unif`.
* `pole_w_integrals_unif` of `HRS.PairMom.pole_w_integrals` (PairMomentsBase l.380). The prefactor
  `exp (M'max + β γmax⁺ + Mmax + β Cq)` is bounded by its value at `βp`. Uses `critical_envelope_integrals_unif`.
* `envBounds_of_rpow_unif` of `HRS.PairMom.envBounds_of_rpow` (PairMomentsEnv l.130). Constants depend on
  `Λ₀` only (`lintegral_mu_rpow` is already uniform in `ρ`); the density hypothesis is `ρ ≤ Λ₀`.
* `psiEnv_bounds_unif` of `HRS.PairMom.psiEnv_bounds` (PairMomentsEnv l.273), `gradEnv_bounds_unif` of
  `HRS.PairMom.gradEnv_bounds` (PairMomentsEnv l.293). Via `envBounds_of_rpow_unif`.

The statements `pairVar_noLog_unif` and `mean2_large_unif` are in `NfUPU1bB.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace HRS.ME.NfU

open HRS HRS.External HRS.Quad HRS.External.PoleVar HRS.PairMom HRS.PairCorrAux HRS.PoleCavityAux
  HRS.KernelAux HRS.KernelAux2 HRS.ME.PmU

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
/-- Uniform `ell_sq_exp_le`: the constant `Cℓ` depends on `d, s, c, βm, βp` only. -/
theorem ell_sq_exp_le_unif {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (βm βp : ℝ)
    (hβm : 0 < βm) (hββ : βm ≤ βp) (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∃ Cℓ : ℝ, 0 ≤ Cℓ ∧ ∀ β ∈ Set.Icc βm βp, ∀ N : ℕ, 2 ≤ N → ∀ x y : Torus d, x ≠ y →
      ellEnv x y ^ 2 * Real.exp (-(β / N / 2) * gPlus d s c (x - y)) ≤ Cℓ * logEN N ^ 2 := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by rw [hcrit]; linarith
  obtain ⟨A, hA, hAw⟩ := PairCorrAux.wEnv_le_gPlus hd hcrit c hc
  set A0 : ℝ := |Real.log (2 * A / βp)| + |Real.log (2 * A / βm)| with hA0def
  refine ⟨Real.exp βp * (2 + 16 / s ^ 2 + 8 * A0 ^ 2 / s ^ 2), by positivity,
    fun β hβI N hN x y hxy => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hEβ' : Real.exp β ≤ Real.exp βp := Real.exp_le_exp.2 hβI.2
  have hlogA : |Real.log (2 * A / β)| ≤ A0 := by
    have h1 : 2 * A / βp ≤ 2 * A / β := div_le_div_of_nonneg_left (by linarith) hβ hβI.2
    have h2 : 2 * A / β ≤ 2 * A / βm := div_le_div_of_nonneg_left (by linarith) hβm hβI.1
    exact abs_log_le_of_mem (div_pos (by linarith) (by linarith)) h1 h2
  have ha0sq : (Real.log (2 * A / β)) ^ 2 ≤ A0 ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hlogA 2
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
  set a0 : ℝ := Real.log (2 * A / β) with ha0
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
    _ ≤ Real.exp βp * (2 + 16 / s ^ 2 + 8 * A0 ^ 2 / s ^ 2) * logEN N ^ 2 := by
        have hL2 : 1 ≤ logEN N ^ 2 := one_le_pow₀ hLe
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
        have h8' : 2 + 16 / s ^ 2 + 8 * a0 ^ 2 / s ^ 2 ≤ 2 + 16 / s ^ 2 + 8 * A0 ^ 2 / s ^ 2 := by
          have : 8 * a0 ^ 2 / s ^ 2 ≤ 8 * A0 ^ 2 / s ^ 2 :=
            div_le_div_of_nonneg_right (by linarith) (by positivity)
          linarith
        calc Real.exp (β / 2) * (2 + 8 / s ^ 2 + 8 * a0 ^ 2 / s ^ 2 + 8 * Real.log N ^ 2 / s ^ 2)
            ≤ Real.exp β * ((2 + 16 / s ^ 2 + 8 * a0 ^ 2 / s ^ 2) * logEN N ^ 2) :=
              mul_le_mul hEβ h7 (by positivity) (Real.exp_pos _).le
          _ ≤ Real.exp βp * ((2 + 16 / s ^ 2 + 8 * A0 ^ 2 / s ^ 2) * logEN N ^ 2) :=
              mul_le_mul hEβ' (mul_le_mul_of_nonneg_right h8' (by positivity)) (by positivity)
                (Real.exp_pos _).le
          _ = _ := by ring

/-- Uniform `lintegral_wEll_exp`: the constant depends on `d, s, c, βm, βp, c₀, Λ₀` only. -/
theorem lintegral_wEll_exp_unif {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (βm βp c₀ Λ₀ : ℝ)
    (hβm : 0 < βm) (hββ : βm ≤ βp) (hΛ : 1 ≤ Λ₀) (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, RhoU d βm βp c₀ Λ₀ β ρ →
      ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d,
      ∫⁻ y, ENNReal.ofReal (wEnv s x y ^ 2 * (logEN N + ellEnv x y) ^ 2 *
        Real.exp (-(β / N) * gPlus d s c (x - y))) ∂(withDensityReal ρ)
        ≤ ENNReal.ofReal (C * logEN N ^ 3) := by
  obtain ⟨C1, hC1⟩ := critical_envelope_integrals_unif hd hcrit c hc βm βp c₀ Λ₀ hβm hββ hΛ 1 one_pos
  obtain ⟨C2, hC2⟩ := critical_envelope_integrals_unif hd hcrit c hc βm βp c₀ Λ₀ hβm hββ hΛ (1 / 2)
    (by norm_num)
  obtain ⟨Cl, hCl0, hCl⟩ := ell_sq_exp_le_unif hd hcrit βm βp hβm hββ c hc
  refine ⟨2 * max C1 0 + 2 * Cl * max C2 0, by positivity, fun β hβI ρ hU N hN x => ?_⟩
  have hC1' := hC1 β hβI ρ hU
  have hC2' := hC2 β hβI ρ hU
  have hCl' := hCl β hβI
  have hβ : 0 < β := hU.hβpos
  have hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hU.rho.density
  have hLe := logEN_pos' (N := N) (by omega)
  have hL0 : 0 ≤ logEN N := by linarith
  have hmw := measurable_w2_exp hd hcrit c (1 / 2 * (β / N)) x
  have hm1 := measurable_w2_exp hd hcrit c (β / N) x
  have hatom := fun z => Calib.atomless_withDensityReal (by omega : 1 ≤ d) ρ z
  have hae : ∀ x : Torus d, ∀ᵐ y ∂(withDensityReal ρ), x ≠ y :=
    fun x => (HRS.External.PoleVar.ae_ne_pt hatom x).mono fun y hy => Ne.symm hy
  have hI1 : ∫⁻ y, ENNReal.ofReal (wEnv s x y ^ 2 * Real.exp (-(β / N) * gPlus d s c (x - y)))
      ∂(withDensityReal ρ) ≤ ENNReal.ofReal (max C1 0 * logEN N) := by
    have h := ((hC1' N hN).1 x).1
    simp only [one_mul] at h
    exact h.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hL0))
  have hI2 : ∫⁻ y, ENNReal.ofReal (wEnv s x y ^ 2 * Real.exp (-(1 / 2 * (β / N)) * gPlus d s c (x - y)))
      ∂(withDensityReal ρ) ≤ ENNReal.ofReal (max C2 0 * logEN N) := by
    refine ((hC2' N hN).1 x).1.trans ?_
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
        have hℓ := hCl' N hN x y hy
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

/-- Uniform `pole_w_integrals`: the constant depends on `d, s, c, βm, βp, c₀, Λ₀` and the potential data
`Mmax M'max γmax Cq` only; the potential `V` ranges over `PotBound` as in the original. -/
theorem pole_w_integrals_unif {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (βm βp c₀ Λ₀ : ℝ)
    (hβm : 0 < βm) (hββ : βm ≤ βp) (hΛ : 1 ≤ Λ₀) (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)
    (Mmax M'max γmax Cq : ℝ) (hCq : 0 ≤ Cq) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, RhoU d βm βp c₀ Λ₀ β ρ →
      ∀ (V : WeakPotential (withDensityReal ρ)),
      PotBound (d := d) s c Mmax M'max γmax Cq V → ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d,
      (∫⁻ y, ENNReal.ofReal (wEnv s x y ^ 2) * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
          pinField V (β / N) (pinsWith (fun e : Empty => e.elim) x) y)) ∂(withDensityReal ρ)
        ≤ ENNReal.ofReal (C * logEN N)) ∧
      (∫⁻ y, ENNReal.ofReal (wEnv s x y ^ 4) * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
          pinField V (β / N) (pinsWith (fun e : Empty => e.elim) x) y)) ∂(withDensityReal ρ)
        ≤ ENNReal.ofReal (C * (N : ℝ) ^ 2)) := by
  obtain ⟨C0, hC0⟩ := critical_envelope_integrals_unif hd hcrit c hc βm βp c₀ Λ₀ hβm hββ hΛ 1 one_pos
  set E0 : ℝ := Real.exp (M'max + βp * max γmax 0 + Mmax + βp * Cq) with hE0
  have hE0p : 0 < E0 := Real.exp_pos _
  refine ⟨E0 * max C0 0, by positivity, fun β hβI ρ hU V hV N hN x => ?_⟩
  have hβ0 : 0 < β := hU.hβpos
  have hβp : β ≤ βp := hU.hβle
  have hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hU.rho.density
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hNp : (0 : ℝ) < N := by linarith
  have hlam0 : 0 ≤ β / N := by positivity
  have hlam : β / N ≤ β := by
    rw [div_le_iff₀ hNp]; nlinarith
  have hatom := fun z => Calib.atomless_withDensityReal (by omega : 1 ≤ d) ρ z
  obtain ⟨h2, -, -⟩ := hC0 β hβI ρ hU N hN
  simp only [one_mul] at h2
  have hEβ : Real.exp (M'max + β * max γmax 0 + Mmax + β * Cq) ≤ E0 := by
    apply Real.exp_le_exp.2
    have e1 : β * max γmax 0 ≤ βp * max γmax 0 := mul_le_mul_of_nonneg_right hβp (le_max_right _ _)
    have e2 : β * Cq ≤ βp * Cq := mul_le_mul_of_nonneg_right hβp hCq
    linarith
  constructor
  · refine (lintegral_pole_le hV hβ0.le hlam0 hlam hCq hatom
      (fun y => ENNReal.ofReal (wEnv s x y ^ 2))).trans ?_
    have : ∀ y, ENNReal.ofReal (wEnv s x y ^ 2) * ENNReal.ofReal (Real.exp (-(β / N) * gPlus d s c (x - y)))
        = ENNReal.ofReal (wEnv s x y ^ 2 * Real.exp (-(β / N) * gPlus d s c (x - y))) := fun y =>
      (ENNReal.ofReal_mul (sq_nonneg _)).symm
    simp_rw [this]
    calc ENNReal.ofReal (Real.exp (M'max + β * max γmax 0 + Mmax + β * Cq)) * ∫⁻ y, ENNReal.ofReal (wEnv s x y ^ 2 *
          Real.exp (-(β / N) * gPlus d s c (x - y))) ∂(withDensityReal ρ)
        ≤ ENNReal.ofReal E0 * ENNReal.ofReal (C0 * logEN N) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal hEβ) (h2 x).1
      _ = ENNReal.ofReal (E0 * (C0 * logEN N)) := (ENNReal.ofReal_mul hE0p.le).symm
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have := logEN_pos' (N := N) (by omega)
          have : C0 ≤ max C0 0 := le_max_left _ _
          nlinarith [mul_nonneg hE0p.le (sub_nonneg.2 this)]
  · refine (lintegral_pole_le hV hβ0.le hlam0 hlam hCq hatom
      (fun y => ENNReal.ofReal (wEnv s x y ^ 4))).trans ?_
    have : ∀ y, ENNReal.ofReal (wEnv s x y ^ 4) * ENNReal.ofReal (Real.exp (-(β / N) * gPlus d s c (x - y)))
        = ENNReal.ofReal (wEnv s x y ^ 4 * Real.exp (-(β / N) * gPlus d s c (x - y))) := fun y =>
      (ENNReal.ofReal_mul (by positivity)).symm
    simp_rw [this]
    calc ENNReal.ofReal (Real.exp (M'max + β * max γmax 0 + Mmax + β * Cq)) * ∫⁻ y, ENNReal.ofReal (wEnv s x y ^ 4 *
          Real.exp (-(β / N) * gPlus d s c (x - y))) ∂(withDensityReal ρ)
        ≤ ENNReal.ofReal E0 * ENNReal.ofReal (C0 * (N : ℝ) ^ 2) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal hEβ) (h2 x).2
      _ = ENNReal.ofReal (E0 * (C0 * (N : ℝ) ^ 2)) := (ENNReal.ofReal_mul hE0p.le).symm
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have : C0 ≤ max C0 0 := le_max_left _ _
          nlinarith [mul_nonneg hE0p.le (sub_nonneg.2 this), sq_nonneg (N : ℝ)]

/-- Uniform `envBounds_of_rpow`: the constants `BA BB BC` depend on `Λ₀` (and `a, Ce, Cu`, `Env`), not on `ρ`. -/
theorem envBounds_of_rpow_unif {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {a : ℝ} (ha0 : 0 ≤ a)
    (ha1 : a < d) (ha2 : 2 * a < d) (ha3 : a + s < d) (Ce Cu : ℝ) (hCe : 0 ≤ Ce) (hCu : 0 ≤ Cu)
    (Λ₀ : ℝ) (hΛ : 1 ≤ Λ₀) (Env : Torus d → Torus d → ℝ) (hE0 : ∀ x y, 0 ≤ Env x y)
    (hE : ∀ x y, x ≠ y → Env x y ≤ Ce * rTrunc x y ^ (-a)) :
    ∃ BA BB BC : ℝ, 0 ≤ BA ∧ 0 ≤ BB ∧ 0 ≤ BC ∧ ∀ ρ : Torus d → ℝ, (∀ x, ρ x ≤ Λ₀) →
      EnvBounds (d := d) s Cu (withDensityReal ρ) Env BA BB BC := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by rw [hcrit]; linarith
  have hΛ0 : 0 ≤ Λ₀ := by linarith
  obtain ⟨Ca, hCa0, hCa⟩ := lintegral_mu_rpow (d := d) (by omega) ha0 ha1
  obtain ⟨Cb, hCb0, hCb⟩ := lintegral_mu_rpow (d := d) (by omega) (by linarith : 0 ≤ 2 * a) ha2
  obtain ⟨Cc, hCc0, hCc⟩ := lintegral_mu_rpow (d := d) (by omega) (by linarith : 0 ≤ a + s) ha3
  have hmr : ∀ (b : ℝ) (x : Torus d), Measurable fun y => ENNReal.ofReal (rTrunc x y ^ (-b)) :=
    fun b x => ENNReal.measurable_ofReal.comp ((measurable_rTrunc x).pow_const _)
  refine ⟨Ce * (Λ₀ * Ca), Ce ^ 2 * (Λ₀ * Cb), Ce * (1 + 2 * Cu) * (Λ₀ * Cc), by positivity,
    by positivity, by positivity, fun ρ hΛρ => ?_⟩
  have hatom := fun z => Calib.atomless_withDensityReal (by omega : 1 ≤ d) ρ z
  have hae : ∀ x : Torus d, ∀ᵐ y ∂(withDensityReal ρ), x ≠ y :=
    fun x => (HRS.External.PoleVar.ae_ne_pt hatom x).mono fun y hy => Ne.symm hy
  refine ⟨hE0, fun x => ?_, fun x => ?_, fun x => ?_⟩
  · calc ∫⁻ y, ENNReal.ofReal (Env x y) ∂(withDensityReal ρ)
        ≤ ∫⁻ y, ENNReal.ofReal Ce * ENNReal.ofReal (rTrunc x y ^ (-a)) ∂(withDensityReal ρ) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hae x] with y hy
          rw [← ENNReal.ofReal_mul hCe]
          exact ENNReal.ofReal_le_ofReal (hE x y hy)
      _ = ENNReal.ofReal Ce * ∫⁻ y, ENNReal.ofReal (rTrunc x y ^ (-a)) ∂(withDensityReal ρ) :=
          lintegral_const_mul _ (hmr a x)
      _ ≤ ENNReal.ofReal Ce * ENNReal.ofReal (Λ₀ * Ca) := by gcongr; exact hCa hΛρ hΛ0 x
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
      _ ≤ ENNReal.ofReal (Ce ^ 2) * ENNReal.ofReal (Λ₀ * Cb) := by gcongr; exact hCb hΛρ hΛ0 x
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
      _ ≤ ENNReal.ofReal (Ce * (1 + 2 * Cu)) * ENNReal.ofReal (Λ₀ * Cc) := by
          gcongr; exact hCc hΛρ hΛ0 x
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]

/-- Uniform `psiEnv_bounds`: the constants depend on `Λ₀` and `Cu` only. -/
theorem psiEnv_bounds_unif {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (Cu : ℝ) (hCu : 0 ≤ Cu)
    (Λ₀ : ℝ) (hΛ : 1 ≤ Λ₀) :
    ∃ BA BB BC : ℝ, 0 ≤ BA ∧ 0 ≤ BB ∧ 0 ≤ BC ∧ ∀ ρ : Torus d → ℝ, (∀ x, ρ x ≤ Λ₀) →
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
  exact envBounds_of_rpow_unif hd hcrit ha k1 k2 k3 6 Cu (by norm_num) hCu Λ₀ hΛ (psiEnv s)
    (fun x y => psiEnv_nonneg s x y) (fun x y hxy => psiEnv_le s hxy)

/-- Uniform `gradEnv_bounds`: the constants depend on `Λ₀` and `Cu` only. -/
theorem gradEnv_bounds_unif {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (Cu : ℝ) (hCu : 0 ≤ Cu)
    (Λ₀ : ℝ) (hΛ : 1 ≤ Λ₀) :
    ∃ BA BB BC : ℝ, 0 ≤ BA ∧ 0 ≤ BB ∧ 0 ≤ BC ∧ ∀ ρ : Torus d → ℝ, (∀ x, ρ x ≤ Λ₀) →
      EnvBounds (d := d) s Cu (withDensityReal ρ) (gradEnv s) BA BB BC := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs1 : 1 ≤ s := by rw [hcrit]; linarith
  have ha : 0 ≤ s - 1 := by linarith
  have k1 : s - 1 < d := by rw [hcrit] at hs1 ⊢; linarith
  have k2 : 2 * (s - 1) < d := by rw [hcrit]; linarith
  have k3 : s - 1 + s < d := by rw [hcrit]; linarith
  exact envBounds_of_rpow_unif hd hcrit ha k1 k2 k3 2 Cu (by norm_num) hCu Λ₀ hΛ (gradEnv s)
    (fun x y => gradEnv_nonneg s x y) (fun x y hxy => gradEnv_le hs1 hxy)

end HRS.ME.NfU
