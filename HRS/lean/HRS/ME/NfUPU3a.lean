import HRS.Equilibrium.PinStep
import HRS.ME.PmU

/-!
# Packet PU3a (uniform pin-step estimates, part a)

Uniform versions (namespace `HRS.ME.NfU`) of the four lemmas of `HRS/Equilibrium/PinStep.lean`:

* `u0_step_unif` of `HRS.PinAux.u0_step` (l.595),
* `u1_step_unif` of `HRS.PinAux.u1_step` (l.705),
* `tstar_bounds_unif` of `HRS.PinAux.tstar_bounds` (l.825),
* `pin_step_set_unif` of `HRS.PinAux.pin_step_set` (l.1071).

Conventions (see `docs/MAIN_E_NF_PLAN.md`, rule for uniform statements):

* Fixed data before `β, ρ`: `βm βp c₀ Λ₀` as in `RhoU`, the kernel data, and the split parameters.
  The auxiliary constant `Γ` of the environment facts is `pinGamma βm` in the applications, which
  bounds `pinGamma β` for all `β ∈ [βm, βp]`.
* The constants (`∃ P0 P1`, `∃ C`) are chosen before `∀ β ∈ Icc βm βp, ∀ ρ, RhoU …`.
* The original equality `V.γ = γ₀` is replaced by `V.γ = γ` with a new variable `γ`, quantified after
  `ρ` with `0 ≤ γ ≤ Γ`. The environment facts at `γ` come from those at `Γ` by `envFacts_mono`.
  The constant depends on `Γ` only, through a monotone formula.
* In `pin_step_set_unif` the equalities `V.γ = pinGamma β`, `V.M = β * pinGamma β + 1` stay as
  hypotheses of the per-`β` clause (they are valid on the whole range, since `β` is quantified first).
  Only the constant is uniform.
* `0 ≤ Λ₀` is a fixed datum (`rhoU_exists` gives `1 ≤ Λ₀`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace HRS.ME.NfU

open HRS HRS.PinAux HRS.External HRS.ME.PmU

variable {d : ℕ}

/-- The environment facts are monotone in the kernel constant `γ`. -/
theorem envFacts_mono {s : ℝ} {q : Torus d → ℝ} {Γ γ C0 C1 C2 cl Cw A' : ℝ}
    (hE : EnvFacts d s q Γ C0 C1 C2 cl Cw A') (hγΓ : γ ≤ Γ) :
    EnvFacts d s q γ C0 C1 C2 cl Cw A' where
  C0_nn := hE.C0_nn
  C1_nn := hE.C1_nn
  C2_nn := hE.C2_nn
  cl_nn := hE.cl_nn
  Cw_nn := hE.Cw_nn
  A'_nn := hE.A'_nn
  int_w := hE.int_w
  twopole := hE.twopole
  wEll := hE.wEll
  ell_le := hE.ell_le
  kern := fun z x => by linarith [hE.kern z x]
  low := hE.low

/-- Uniform `u0_step`: the constants `P0, P1` are chosen before `β, ρ` (and before `γ`). -/
theorem u0_step_unif {s Γ C0 C1 C2 cl Cw A' : ℝ} {q : Torus d → ℝ}
    (hE : EnvFacts d s q Γ C0 C1 C2 cl Cw A') (βm βp c₀ Λ₀ Kb : ℝ) (hβm : 0 < βm)
    (hββ : βm ≤ βp) (hΓ : 0 ≤ Γ) (hΛ0 : 0 ≤ Λ₀) (hq0 : ∀ z, 0 ≤ q z) (hqm : Measurable q)
    (hKb : 0 ≤ Kb) (a : ℕ) :
    ∃ P0 P1 : ℝ, 0 ≤ P0 ∧ 0 ≤ P1 ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ,
      RhoU d βm βp c₀ Λ₀ β ρ →
      ∀ γ : ℝ, 0 ≤ γ → γ ≤ Γ → ∀ (V : WeakPotential (withDensityReal ρ))
      (hVq : ∀ x y, V.q x y = q (x - y)) (hVγ : V.γ = γ)
      (lam K1 : ℝ) (n m : ℕ) [NeZero n] (b : Fin m → Torus d),
      0 ≤ lam → 0 < K1 → K1 ≤ Kb → m ≤ a → (n : ℝ) * lam ≤ β →
      ∀ z : Torus d, (∀ k, z ≠ b k) →
        Tstar (withDensityReal ρ) (fieldOmega V lam K1) n
          (fun z => pinD (withDensityReal ρ) q lam K1 b z
            + ∫ w, pinD (withDensityReal ρ) q lam K1 b w ∂(withDensityReal ρ)) z
          ≤ lam * (P0 + P1 * ∑ k, ellEnv z (b k)) := by
  have hβp0 : 0 ≤ βp := by linarith
  set Kf : ℝ := Kb * (1 + Kb) with hKf
  have hKf0 : 0 ≤ Kf := by positivity
  have hCw0 := hE.Cw_nn
  have hC00 := hE.C0_nn
  have hC10 := hE.C1_nn
  set c1u : ℝ := Kb * Cw + (Kb + 2 * Kb ^ 2) * a * Γ with hc1u
  have hc1u0 : 0 ≤ c1u := by positivity
  refine ⟨βp * Kf * c1u * (Cw * Λ₀ * C0 + 2 * Γ * (1 + a * Λ₀ * C0)),
    βp * Kf * c1u * Cw * Λ₀ * C1, by positivity, by positivity, ?_⟩
  intro β hβ ρ U γ hγ0 hγΓ V hVq hVγ lam K1 n m _ b hlam hK1 hKK hm hnl z hz
  have hβ0 : 0 ≤ β := U.hβpos.le
  have hβle : β ≤ βp := U.hβle
  have hρ : SmoothPosDensity ρ := U.rho
  have hΛ : ∀ x, ρ x ≤ Λ₀ := U.hup
  have hEγ := envFacts_mono hE hγΓ
  have : IsProbabilityMeasure (withDensityReal ρ) := PoleCavityAux.isProbabilityMeasure_mu hρ
  set c1 : ℝ := Kb * Cw + (Kb + 2 * Kb ^ 2) * a * γ with hc1
  have hc10 : 0 ≤ c1 := by positivity
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have hgood := pinD_goodF (μ := withDensityReal ρ) V hVq hqm hq0 hlam hK1.le b
  set ū : Torus d → ℝ := fun x => lam * c1 * (1 + ∑ k, wEnv s x (b k)) with hū
  have hū0 : ∀ x, 0 ≤ ū x := fun x => by
    have : 0 ≤ ∑ k, wEnv s x (b k) := Finset.sum_nonneg fun k _ => wEnv_pos s _ _
    simp only [hū]; positivity
  have hūm : Measurable ū := by
    simp only [hū]
    refine measurable_const.mul (measurable_const.add (Finset.measurable_sum _ fun k _ => ?_))
    exact measurable_wEnv_left s (b k)
  have hle : ∀ᵐ x ∂(withDensityReal ρ),
      (pinD (withDensityReal ρ) q lam K1 b x + ∫ w, pinD (withDensityReal ρ) q lam K1 b w ∂(withDensityReal ρ)) ≤ ū x :=
    Filter.Eventually.of_forall fun x => v0_le hEγ hγ0 hqm hq0 V hVq hVγ hlam hK1 hKK hm b x
  have hJ1 : ∫⁻ x, ENNReal.ofReal (ū x * wEnv s z x) ∂(withDensityReal ρ)
      ≤ ENNReal.ofReal (lam * c1 * (Λ₀ * (C0 + ∑ k, C1 * ellEnv z (b k)))) := by
    calc ∫⁻ x, ENNReal.ofReal (ū x * wEnv s z x) ∂(withDensityReal ρ)
        = ∫⁻ x, ENNReal.ofReal (lam * c1) * ENNReal.ofReal ((1 + ∑ k, wEnv s x (b k)) * wEnv s z x)
            ∂(withDensityReal ρ) := by
          refine lintegral_congr fun x => ?_
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1; simp only [hū]; ring
      _ = ENNReal.ofReal (lam * c1) * ∫⁻ x, ENNReal.ofReal ((1 + ∑ k, wEnv s x (b k)) * wEnv s z x)
            ∂(withDensityReal ρ) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (lam * c1) * ENNReal.ofReal (Λ₀ * (C0 + ∑ k, C1 * ellEnv z (b k))) := by
          gcongr; exact J_w hEγ hΛ hΛ0 b z hz
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]
  have hJ2 : ∫⁻ x, ENNReal.ofReal (ū x) ∂(withDensityReal ρ)
      ≤ ENNReal.ofReal (lam * c1 * (1 + a * Λ₀ * C0)) := by
    have hm' : (m : ℝ) ≤ a := by exact_mod_cast hm
    calc ∫⁻ x, ENNReal.ofReal (ū x) ∂(withDensityReal ρ)
        = ∫⁻ x, ENNReal.ofReal (lam * c1) * ENNReal.ofReal (1 + ∑ k, wEnv s x (b k))
            ∂(withDensityReal ρ) := by
          refine lintegral_congr fun x => ?_
          rw [← ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal (lam * c1) * ∫⁻ x, ENNReal.ofReal (1 + ∑ k, wEnv s x (b k))
            ∂(withDensityReal ρ) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (lam * c1) * ENNReal.ofReal (1 + Λ₀ * m * C0) := by
          gcongr; exact J_one hEγ hρ hΛ hΛ0 b
      _ ≤ ENNReal.ofReal (lam * c1) * ENNReal.ofReal (1 + a * Λ₀ * C0) := by
          refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
          have := hE.C0_nn
          nlinarith [mul_nonneg hΛ0 this, mul_le_mul_of_nonneg_right hm' (mul_nonneg hΛ0 this)]
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]
  have hmain := Tstar_weight_bound hEγ hρ V hVq hVγ hlam hK1.le hn hgood ū hūm hū0 hle z
    (J1 := lam * c1 * (Λ₀ * (C0 + ∑ k, C1 * ellEnv z (b k))))
    (J2 := lam * c1 * (1 + a * Λ₀ * C0)) (by
      have : 0 ≤ ∑ k, C1 * ellEnv z (b k) := Finset.sum_nonneg fun k _ => mul_nonneg hE.C1_nn (ellEnv_nonneg _ _)
      positivity) (by positivity) hJ1 hJ2
  refine hmain.trans ?_
  set Sℓ : ℝ := ∑ k, ellEnv z (b k) with hSℓ
  have hSℓ0 : 0 ≤ Sℓ := Finset.sum_nonneg fun k _ => ellEnv_nonneg _ _
  have hsum : ∑ k, C1 * ellEnv z (b k) = C1 * Sℓ := by rw [hSℓ, Finset.mul_sum]
  rw [hsum]
  set X : ℝ := ((n : ℝ) - 1) * (K1 * (1 + K1) * lam) with hX
  have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hXle : X ≤ βp * Kf := by
    have h1 : K1 * (1 + K1) ≤ Kf := by
      rw [hKf]; exact mul_le_mul hKK (by linarith) (by linarith) hKb
    calc X = ((n : ℝ) - 1) * lam * (K1 * (1 + K1)) := by rw [hX]; ring
      _ ≤ (n * lam) * (K1 * (1 + K1)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          nlinarith
      _ ≤ β * Kf := mul_le_mul hnl h1 (by positivity) hβ0
      _ ≤ βp * Kf := mul_le_mul_of_nonneg_right hβle hKf0
  calc ((n : ℝ) - 1) * ((K1 * (1 + K1) * lam * Cw) * (lam * c1 * (Λ₀ * (C0 + C1 * Sℓ)))
        + (2 * (K1 * (1 + K1) * lam) * γ) * (lam * c1 * (1 + a * Λ₀ * C0)))
      = X * (lam * c1 * (Cw * Λ₀ * (C0 + C1 * Sℓ) + 2 * γ * (1 + a * Λ₀ * C0))) := by
        rw [hX]; ring
    _ ≤ (βp * Kf) * (lam * c1 * (Cw * Λ₀ * (C0 + C1 * Sℓ) + 2 * γ * (1 + a * Λ₀ * C0))) :=
        mul_le_mul_of_nonneg_right hXle (by positivity)
    _ ≤ (βp * Kf) * (lam * c1u * (Cw * Λ₀ * (C0 + C1 * Sℓ) + 2 * Γ * (1 + a * Λ₀ * C0))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hc1le : c1 ≤ c1u := by
          have : (Kb + 2 * Kb ^ 2) * a * γ ≤ (Kb + 2 * Kb ^ 2) * a * Γ :=
            mul_le_mul_of_nonneg_left hγΓ (by positivity)
          rw [hc1, hc1u]; linarith
        have hYle : 2 * γ * (1 + a * Λ₀ * C0) ≤ 2 * Γ * (1 + a * Λ₀ * C0) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        have hY : 0 ≤ Cw * Λ₀ * (C0 + C1 * Sℓ) + 2 * γ * (1 + a * Λ₀ * C0) := by positivity
        exact mul_le_mul (mul_le_mul_of_nonneg_left hc1le hlam) (by linarith) hY (by positivity)
    _ = lam * (βp * Kf * c1u * (Cw * Λ₀ * C0 + 2 * Γ * (1 + a * Λ₀ * C0))
          + βp * Kf * c1u * Cw * Λ₀ * C1 * Sℓ) := by ring

/-- Uniform `u1_step`: the constant `P4` is chosen before `β, ρ, γ`. -/
theorem u1_step_unif {s Γ C0 C1 C2 cl Cw A' : ℝ} {q : Torus d → ℝ}
    (hE : EnvFacts d s q Γ C0 C1 C2 cl Cw A') (βm βp c₀ Λ₀ Kb : ℝ) (hβm : 0 < βm)
    (hββ : βm ≤ βp) (hΓ : 0 ≤ Γ) (hΛ0 : 0 ≤ Λ₀) (hKb : 0 ≤ Kb) (a : ℕ) (P3 : ℝ) (hP3 : 0 ≤ P3) :
    ∃ P4 : ℝ, 0 ≤ P4 ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ,
      RhoU d βm βp c₀ Λ₀ β ρ →
      ∀ γ : ℝ, 0 ≤ γ → γ ≤ Γ → ∀ (V : WeakPotential (withDensityReal ρ))
      (hVq : ∀ x y, V.q x y = q (x - y)) (hVγ : V.γ = γ)
      (lam K1 : ℝ) (n m : ℕ) [NeZero n] (b : Fin m → Torus d),
      0 ≤ lam → 0 < K1 → K1 ≤ Kb → m ≤ a → (n : ℝ) * lam ≤ β →
      ∀ u : Torus d → ℝ, GoodF u →
        (∀ᵐ x ∂(withDensityReal ρ), u x ≤ lam * P3 * (1 + ∑ k, ellEnv x (b k))) →
        ∀ z : Torus d, Tstar (withDensityReal ρ) (fieldOmega V lam K1) n u z ≤ lam * P4 := by
  have hβp0 : 0 ≤ βp := by linarith
  set Kf : ℝ := Kb * (1 + Kb) with hKf
  have hKf0 : 0 ≤ Kf := by positivity
  have hCw0 := hE.Cw_nn
  have hC00 := hE.C0_nn
  have hC20 := hE.C2_nn
  have hcl0 := hE.cl_nn
  refine ⟨βp * Kf * P3 * (Cw * Λ₀ * (C0 + a * C2) + 2 * Γ * (1 + a * Λ₀ * (cl * C0))),
    by positivity, ?_⟩
  intro β hβ ρ U γ hγ0 hγΓ V hVq hVγ lam K1 n m _ b hlam hK1 hKK hm hnl u hu hule z
  have hβ0 : 0 ≤ β := U.hβpos.le
  have hβle : β ≤ βp := U.hβle
  have hρ : SmoothPosDensity ρ := U.rho
  have hΛ : ∀ x, ρ x ≤ Λ₀ := U.hup
  have hEγ := envFacts_mono hE hγΓ
  have : IsProbabilityMeasure (withDensityReal ρ) := PoleCavityAux.isProbabilityMeasure_mu hρ
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have hm' : (m : ℝ) ≤ a := by exact_mod_cast hm
  set ū : Torus d → ℝ := fun x => lam * P3 * (1 + ∑ k, ellEnv x (b k)) with hū
  have hSℓ : ∀ x, 0 ≤ ∑ k, ellEnv x (b k) := fun x => Finset.sum_nonneg fun k _ => ellEnv_nonneg _ _
  have hū0 : ∀ x, 0 ≤ ū x := fun x => by
    have := hSℓ x
    simp only [hū]; positivity
  have hūm : Measurable ū := by
    simp only [hū]
    refine measurable_const.mul (measurable_const.add (Finset.measurable_sum _ fun k _ => ?_))
    exact measurable_ellEnv (b k)
  have hJ1 : ∫⁻ x, ENNReal.ofReal (ū x * wEnv s z x) ∂(withDensityReal ρ)
      ≤ ENNReal.ofReal (lam * P3 * (Λ₀ * (C0 + a * C2))) := by
    calc ∫⁻ x, ENNReal.ofReal (ū x * wEnv s z x) ∂(withDensityReal ρ)
        = ∫⁻ x, ENNReal.ofReal (lam * P3) * ENNReal.ofReal ((1 + ∑ k, ellEnv x (b k)) * wEnv s z x)
            ∂(withDensityReal ρ) := by
          refine lintegral_congr fun x => ?_
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1; simp only [hū]; ring
      _ = ENNReal.ofReal (lam * P3) * ∫⁻ x, ENNReal.ofReal ((1 + ∑ k, ellEnv x (b k)) * wEnv s z x)
            ∂(withDensityReal ρ) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (lam * P3) * ENNReal.ofReal (Λ₀ * (C0 + m * C2)) := by
          gcongr; exact J_ell hEγ hΛ hΛ0 b z
      _ ≤ ENNReal.ofReal (lam * P3) * ENNReal.ofReal (Λ₀ * (C0 + a * C2)) := by
          refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
          exact mul_le_mul_of_nonneg_left (by nlinarith [mul_le_mul_of_nonneg_right hm' hC20]) hΛ0
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]
  have hJ2 : ∫⁻ x, ENNReal.ofReal (ū x) ∂(withDensityReal ρ)
      ≤ ENNReal.ofReal (lam * P3 * (1 + a * Λ₀ * (cl * C0))) := by
    calc ∫⁻ x, ENNReal.ofReal (ū x) ∂(withDensityReal ρ)
        = ∫⁻ x, ENNReal.ofReal (lam * P3) * ENNReal.ofReal (1 + ∑ k, ellEnv x (b k))
            ∂(withDensityReal ρ) := by
          refine lintegral_congr fun x => ?_
          rw [← ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal (lam * P3) * ∫⁻ x, ENNReal.ofReal (1 + ∑ k, ellEnv x (b k))
            ∂(withDensityReal ρ) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (lam * P3) * ENNReal.ofReal (1 + Λ₀ * m * (cl * C0)) := by
          gcongr; exact J_one_ell hEγ hρ hΛ hΛ0 b
      _ ≤ ENNReal.ofReal (lam * P3) * ENNReal.ofReal (1 + a * Λ₀ * (cl * C0)) := by
          refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
          have h0 : 0 ≤ Λ₀ * (cl * C0) := by positivity
          nlinarith [mul_le_mul_of_nonneg_right hm' h0]
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]
  have hmain := Tstar_weight_bound hEγ hρ V hVq hVγ hlam hK1.le hn hu ū hūm hū0 hule z
    (J1 := lam * P3 * (Λ₀ * (C0 + a * C2))) (J2 := lam * P3 * (1 + a * Λ₀ * (cl * C0)))
    (by positivity) (by positivity) hJ1 hJ2
  refine hmain.trans ?_
  set X : ℝ := ((n : ℝ) - 1) * (K1 * (1 + K1) * lam) with hX
  have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hXle : X ≤ βp * Kf := by
    have h1 : K1 * (1 + K1) ≤ Kf := by
      rw [hKf]; exact mul_le_mul hKK (by linarith) (by linarith) hKb
    calc X = ((n : ℝ) - 1) * lam * (K1 * (1 + K1)) := by rw [hX]; ring
      _ ≤ (n * lam) * (K1 * (1 + K1)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          nlinarith
      _ ≤ β * Kf := mul_le_mul hnl h1 (by positivity) hβ0
      _ ≤ βp * Kf := mul_le_mul_of_nonneg_right hβle hKf0
  calc ((n : ℝ) - 1) * ((K1 * (1 + K1) * lam * Cw) * (lam * P3 * (Λ₀ * (C0 + a * C2)))
        + (2 * (K1 * (1 + K1) * lam) * γ) * (lam * P3 * (1 + a * Λ₀ * (cl * C0))))
      = X * (lam * P3 * (Cw * Λ₀ * (C0 + a * C2) + 2 * γ * (1 + a * Λ₀ * (cl * C0)))) := by
        rw [hX]; ring
    _ ≤ (βp * Kf) * (lam * P3 * (Cw * Λ₀ * (C0 + a * C2) + 2 * γ * (1 + a * Λ₀ * (cl * C0)))) :=
        mul_le_mul_of_nonneg_right hXle (by positivity)
    _ ≤ (βp * Kf) * (lam * P3 * (Cw * Λ₀ * (C0 + a * C2) + 2 * Γ * (1 + a * Λ₀ * (cl * C0)))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hY : 2 * γ * (1 + a * Λ₀ * (cl * C0)) ≤ 2 * Γ * (1 + a * Λ₀ * (cl * C0)) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        linarith
    _ = lam * (βp * Kf * P3 * (Cw * Λ₀ * (C0 + a * C2) + 2 * Γ * (1 + a * Λ₀ * (cl * C0)))) := by
        ring

/-- Pure arithmetic of the final step of `tstar_bounds_unif` (kept in a clean context). -/
theorem tstar_arith {lam c1 P0 P1 P4 A' cl Sq Sw Sl D T a m : ℝ}
    (hlam : 0 ≤ lam) (hc1 : 0 ≤ c1) (hP0 : 0 ≤ P0) (hP1 : 0 ≤ P1) (hP4 : 0 ≤ P4) (hA : 0 ≤ A')
    (hcl : 0 ≤ cl) (hSq : 0 ≤ Sq) (ha : 0 ≤ a) (hm : m ≤ a) (hSw : Sw ≤ A' * (m + Sq))
    (hSl : Sl ≤ cl * (A' * (m + Sq))) (hD : D ≤ lam * c1 * (1 + Sw))
    (hT : T ≤ lam * (P0 + P1 * Sl)) :
    D + T + 2 * (lam * P4) ≤
      (c1 + (P0 + P1) + 2 * P4 + (c1 * A' + (P0 + P1) * cl * A') * (a + 1)) * lam * (1 + Sq) := by
  have hSw' : Sw ≤ A' * (a + Sq) :=
    hSw.trans (mul_le_mul_of_nonneg_left (by linarith) hA)
  have hSl' : Sl ≤ cl * (A' * (a + Sq)) :=
    hSl.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hA) hcl)
  have hA1 : lam * c1 * (1 + Sw) ≤ lam * (c1 + c1 * A' * (a + Sq)) := by
    have h := mul_le_mul_of_nonneg_left (show 1 + Sw ≤ 1 + A' * (a + Sq) by linarith)
      (show (0 : ℝ) ≤ lam * c1 by positivity)
    linarith
  have h4 : P1 * Sl ≤ P1 * (cl * (A' * (a + Sq))) := mul_le_mul_of_nonneg_left hSl' hP1
  have h5 : 0 ≤ P0 * (cl * A' * (a + Sq)) := by positivity
  have hsum : P0 + P1 * Sl ≤ (P0 + P1) + (P0 + P1) * cl * A' * (a + Sq) := by
    linarith
  have hA2 : T ≤ lam * ((P0 + P1) + (P0 + P1) * cl * A' * (a + Sq)) :=
    hT.trans (mul_le_mul_of_nonneg_left hsum hlam)
  have hfin := final_arith hlam hc1 hP0 hP1 hP4 hA hcl hSq ha
  linarith

/-- Uniform `tstar_bounds`: the constant `C` is chosen before `β, ρ, γ`. -/
theorem tstar_bounds_unif {s Γ C0 C1 C2 cl Cw A' : ℝ} {q : Torus d → ℝ}
    (hd : 1 ≤ d) (hE : EnvFacts d s q Γ C0 C1 C2 cl Cw A') (βm βp c₀ Λ₀ Kb : ℝ) (hβm : 0 < βm)
    (hββ : βm ≤ βp) (hΓ : 0 ≤ Γ) (hΛ0 : 0 ≤ Λ₀) (hq0 : ∀ z, 0 ≤ q z) (hqm : Measurable q)
    (hKb : 0 ≤ Kb) (a : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ,
      RhoU d βm βp c₀ Λ₀ β ρ →
      ∀ γ : ℝ, 0 ≤ γ → γ ≤ Γ → ∀ (V : WeakPotential (withDensityReal ρ))
      (hVq : ∀ x y, V.q x y = q (x - y)) (hVγ : V.γ = γ)
      (lam K1 : ℝ) (n m : ℕ) [NeZero n] (b : Fin m → Torus d),
      0 ≤ lam → 0 < K1 → K1 ≤ Kb → m ≤ a → (n : ℝ) * lam ≤ β →
      ∃ B2 : ℝ,
        (∀ z, Tstar (withDensityReal ρ) (fieldOmega V lam K1) n
          (Tstar (withDensityReal ρ) (fieldOmega V lam K1) n
            (fun z => pinD (withDensityReal ρ) q lam K1 b z
              + ∫ w, pinD (withDensityReal ρ) q lam K1 b w ∂(withDensityReal ρ))) z ≤ B2) ∧
        (∀ᵐ z ∂(withDensityReal ρ),
          (pinD (withDensityReal ρ) q lam K1 b z
              + ∫ w, pinD (withDensityReal ρ) q lam K1 b w ∂(withDensityReal ρ))
            + Tstar (withDensityReal ρ) (fieldOmega V lam K1) n
                (fun z => pinD (withDensityReal ρ) q lam K1 b z
                  + ∫ w, pinD (withDensityReal ρ) q lam K1 b w ∂(withDensityReal ρ)) z
            + 2 * B2 ≤ C * lam * (1 + ∑ k, q (z - b k))) := by
  obtain ⟨P0, P1, hP0, hP1, hu0⟩ := u0_step_unif hE βm βp c₀ Λ₀ Kb hβm hββ hΓ hΛ0 hq0 hqm hKb a
  obtain ⟨P4, hP4, hu1⟩ := u1_step_unif hE βm βp c₀ Λ₀ Kb hβm hββ hΓ hΛ0 hKb a (P0 + P1)
    (add_nonneg hP0 hP1)
  set c1u : ℝ := Kb * Cw + (Kb + 2 * Kb ^ 2) * a * Γ with hc1u
  have hCw0 := hE.Cw_nn
  have hA0 := hE.A'_nn
  have hcl0 := hE.cl_nn
  have hc10 : 0 ≤ c1u := by positivity
  refine ⟨c1u + (P0 + P1) + 2 * P4 + (c1u * A' + (P0 + P1) * cl * A') * (a + 1),
    by positivity, ?_⟩
  intro β hβI ρ U γ hγ0 hγΓ V hVq hVγ lam K1 n m _ b hlam hK1 hKK hm hnl
  have hβ0 : 0 ≤ β := U.hβpos.le
  have hρ : SmoothPosDensity ρ := U.rho
  have : IsProbabilityMeasure (withDensityReal ρ) := PoleCavityAux.isProbabilityMeasure_mu hρ
  have hEγ := envFacts_mono hE hγΓ
  have hc1le : Kb * Cw + (Kb + 2 * Kb ^ 2) * a * γ ≤ c1u := by
    have : (Kb + 2 * Kb ^ 2) * a * γ ≤ (Kb + 2 * Kb ^ 2) * a * Γ :=
      mul_le_mul_of_nonneg_left hγΓ (by positivity)
    rw [hc1u]; linarith
  have hker := fieldOmega_ker (μ := withDensityReal ρ) V hlam hK1.le
  have hgood := pinD_goodF (μ := withDensityReal ρ) V hVq hqm hq0 hlam hK1.le b
  have hu1good := hgood.Tstar (n := n) hker
  refine ⟨lam * P4, fun z => ?_, ?_⟩
  · refine hu1 β hβI ρ U γ hγ0 hγΓ V hVq hVγ lam K1 n m b hlam hK1 hKK hm hnl _ hu1good ?_ z
    filter_upwards [ae_not_mem_pins hd ρ b] with x hx
    refine (hu0 β hβI ρ U γ hγ0 hγΓ V hVq hVγ lam K1 n m b hlam hK1 hKK hm hnl x hx).trans ?_
    have hS : 0 ≤ ∑ k, ellEnv x (b k) := Finset.sum_nonneg fun k _ => ellEnv_nonneg _ _
    linarith [mul_nonneg hlam hP1, mul_nonneg (mul_nonneg hlam hP0) hS]
  · filter_upwards [ae_not_mem_pins hd ρ b] with z hz
    have hW0 : 0 ≤ 1 + ∑ k, wEnv s z (b k) := by
      have := Finset.sum_nonneg (fun k (_ : k ∈ Finset.univ) => wEnv_pos s z (b k))
      linarith
    have h1 := v0_le hEγ hγ0 hqm hq0 V hVq hVγ hlam hK1 hKK hm b z
    have h1' := h1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc1le hlam) hW0)
    have h2 := hu0 β hβI ρ U γ hγ0 hγΓ V hVq hVγ lam K1 n m b hlam hK1 hKK hm hnl z hz
    set Sq : ℝ := ∑ k, q (z - b k) with hSq
    have hSq0 : 0 ≤ Sq := Finset.sum_nonneg fun k _ => hq0 _
    have hm' : (m : ℝ) ≤ a := by exact_mod_cast hm
    have hSw : ∑ k, wEnv s z (b k) ≤ A' * (m + Sq) := by
      calc ∑ k, wEnv s z (b k) ≤ ∑ k, A' * (1 + q (z - b k)) :=
            Finset.sum_le_sum fun k _ => hE.low z (b k)
        _ = A' * (m + Sq) := by
            rw [← Finset.mul_sum, Finset.sum_add_distrib]; simp [hSq]
    have hSl : ∑ k, ellEnv z (b k) ≤ cl * (A' * (m + Sq)) := by
      calc ∑ k, ellEnv z (b k) ≤ ∑ k, cl * wEnv s z (b k) :=
            Finset.sum_le_sum fun k _ => hE.ell_le z (b k)
        _ = cl * ∑ k, wEnv s z (b k) := by rw [Finset.mul_sum]
        _ ≤ cl * (A' * (m + Sq)) := mul_le_mul_of_nonneg_left hSw hcl0
    exact tstar_arith hlam hc10 hP0 hP1 hP4 hA0 hcl0 hSq0 (Nat.cast_nonneg a) hm' hSw hSl h1' h2


/-- `pinGamma` is antitone: `pinGamma β ≤ pinGamma βm` for `βm ≤ β`. -/
theorem pinGamma_le_of_le {βm β : ℝ} (hβm : 0 < βm) (h : βm ≤ β) : pinGamma β ≤ pinGamma βm := by
  unfold pinGamma
  exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left h (by positivity))

/-- Uniform `pin_step_set`: the constant `C` is chosen before `β, ρ`. The per-`β` clause keeps the
equalities `V.γ = pinGamma β`, `V.M = β * pinGamma β + 1` (valid for each `β ∈ [βm, βp]`). -/
theorem pin_step_set_unif {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (βm βp c₀ Λ₀ : ℝ)
    (hβm : 0 < βm) (hββ : βm ≤ βp) (hΛ0 : 0 ≤ Λ₀)
    (q : Torus d → ℝ) (hq0 : ∀ z, 0 ≤ q z) (hqm : Measurable q) (Cq : ℝ)
    (hqenv : ∀ z, z ≠ 0 → q z ≤ Cq * (1 + Torus.eucDist z 0 ^ (-s)))
    (hdec : ∃ k : Torus d → ℝ, Torus.IsSmooth k ∧ ∃ c : ℝ, ∀ z, z ≠ 0 →
      periodicRiesz d s z = q z + k z + c) (a : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, RhoU d βm βp c₀ Λ₀ β ρ →
      ∀ (V : WeakPotential (withDensityReal ρ)) (_ : ∀ x y, V.q x y = q (x - y))
        (_ : V.γ = pinGamma β) (_ : V.M = β * pinGamma β + 1) (_ : V.M' = 1)
        (N n m : ℕ) [NeZero n], a + 1 ≤ N → n ≤ N → m ≤ a + 1 → ∀ (b : Fin m → Torus d)
        (ψ ψ' : Torus d → ℝ) (M₁ M₁' : ℝ), IsField (withDensityReal ρ) ψ V.M M₁ →
        IsField (withDensityReal ρ) ψ' V.M M₁' → M₁ ≤ 1 + β * pinGamma β →
        M₁' ≤ 1 + β * pinGamma β → (∀ z, |ψ' z - ψ z| ≤ pinDelta q (β / N) b z) →
        ∀ (i0 : Fin n) (A : Set (Torus d)), MeasurableSet A →
        |((fieldLaw V ψ' (β / N) n).map (fun x => x i0)).real A
          - ((fieldLaw V ψ (β / N) n).map (fun x => x i0)).real A|
          ≤ ∫ z in A, C * (β / N) * (1 + ∑ k, q (z - b k)) ∂(withDensityReal ρ) := by
  have hβm0 : 0 < pinGamma βm := pinGamma_pos hβm
  obtain ⟨C0, C1, C2, cl, Cw, A', hE⟩ := exists_env hd hcrit q hq0 Cq hqenv hdec (pinGamma βm) hβm0.le
  obtain ⟨C, hC0, hC⟩ := tstar_bounds_unif (by omega) hE βm βp c₀ Λ₀ (Real.exp 5) hβm hββ hβm0.le
    hΛ0 hq0 hqm (Real.exp_pos 5).le (a + 1)
  refine ⟨C, hC0, ?_⟩
  intro β hβI ρ U V hVq hVγ hVM hVM' N n m _ hNa hnN hma b ψ ψ' M₁ M₁' hψ hψ' hM₁ hM₁' hdiff i0 A hA
  have hβ : 0 < β := U.hβpos
  have : IsProbabilityMeasure (withDensityReal ρ) := PoleCavityAux.isProbabilityMeasure_mu U.rho
  set γ₀ := pinGamma β with hγ₀def
  have hγ₀ : 0 < γ₀ := pinGamma_pos hβ
  have hγΓ : γ₀ ≤ pinGamma βm := pinGamma_le_of_le hβm hβI.1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam : 0 ≤ β / N := by positivity
  have hnl : (n : ℝ) * (β / N) ≤ β := by
    have : (n : ℝ) ≤ N := by exact_mod_cast hnN
    calc (n : ℝ) * (β / N) = (n / N) * β := by ring
      _ ≤ 1 * β := by
          refine mul_le_mul_of_nonneg_right ?_ hβ.le
          rw [div_le_one hNpos]; exact this
      _ = β := one_mul _
  set Λf : ℝ := 1 + 2 * β * γ₀ with hΛf
  have hg : β * γ₀ = 1 / (16 * Real.exp 10) := beta_mul_pinGamma hβ
  have hE5 : 1 ≤ Real.exp 5 := Real.one_le_exp (by norm_num)
  have hexp10 : Real.exp 10 = Real.exp 5 * Real.exp 5 := by rw [← Real.exp_add]; norm_num
  have hg1 : β * γ₀ ≤ 1 := by
    rw [hg]; rw [div_le_one (by positivity)]
    nlinarith [Real.exp_pos 10, Real.add_one_le_exp (10 : ℝ)]
  set K1 : ℝ := Real.exp (V.M + Λf) with hK1
  have hK1pos : 0 < K1 := Real.exp_pos _
  have hK1le : K1 ≤ Real.exp 5 := by
    rw [hK1]
    refine Real.exp_le_exp.2 ?_
    rw [hVM, hΛf]; nlinarith
  have hnum := pin_numeric (g := β * γ₀) hE5 (by rw [hg, hexp10]) hK1pos.le hK1le
  have hlg : (n : ℝ) * (β / N) * γ₀ ≤ β * γ₀ := mul_le_mul_of_nonneg_right hnl hγ₀.le
  have hΛ1 : M₁ + (β / N) * n * V.γ ≤ Λf := by
    rw [hVγ, hΛf]
    have : (β / N) * n * γ₀ = (n : ℝ) * (β / N) * γ₀ := by ring
    nlinarith
  have hΛ2 : M₁' + (β / N) * n * V.γ ≤ Λf := by
    rw [hVγ, hΛf]
    have : (β / N) * n * γ₀ = (n : ℝ) * (β / N) * γ₀ := by ring
    nlinarith
  have hr : (n : ℝ) * (4 * Real.exp (V.M + Λf) * (β / N) * V.γ) < 1 := by
    rw [hVγ, ← hK1]
    have : (n : ℝ) * (4 * K1 * (β / N) * γ₀) = 4 * K1 * ((n : ℝ) * (β / N) * γ₀) := by ring
    rw [this]
    calc 4 * K1 * ((n : ℝ) * (β / N) * γ₀) ≤ 4 * K1 * (β * γ₀) :=
          mul_le_mul_of_nonneg_left hlg (by positivity)
      _ < 1 := hnum.1
  have hε : ((n : ℝ) - 1) * (2 * (2 * (Real.exp (V.M + Λf) * (1 + Real.exp (V.M + Λf)) * (β / N))
      * V.γ)) ≤ 1 / 2 := by
    rw [hVγ, ← hK1]
    have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
      linarith
    have hn2 : ((n : ℝ) - 1) * (β / N) * γ₀ ≤ β * γ₀ := by
      refine le_trans (mul_le_mul_of_nonneg_right ?_ hγ₀.le) hlg
      nlinarith [div_nonneg hβ.le hNpos.le]
    have e : ((n : ℝ) - 1) * (2 * (2 * (K1 * (1 + K1) * (β / N)) * γ₀))
        = 4 * (K1 * (1 + K1)) * (((n : ℝ) - 1) * (β / N) * γ₀) := by ring
    rw [e]
    calc 4 * (K1 * (1 + K1)) * (((n : ℝ) - 1) * (β / N) * γ₀) ≤ 4 * (K1 * (1 + K1)) * (β * γ₀) :=
          mul_le_mul_of_nonneg_left hn2 (by positivity)
      _ ≤ 1 / 2 := hnum.2
  obtain ⟨B2, hB2, hΨ⟩ := hC β hβI ρ U γ₀ hγ₀.le hγΓ V hVq hVγ (β / N) K1 n m b hlam hK1pos hK1le hma hnl
  obtain ⟨hDm, hD0, hDb⟩ := pinD_props (μ := withDensityReal ρ) hqm hq0 hlam hK1pos.le b
  have hδi := integrable_pinDelta V hVq (β / N) b
  have hI : ∫ w, |ψ' w - ψ w| ∂(withDensityReal ρ) ≤ ∫ w, pinDelta q (β / N) b w ∂(withDensityReal ρ) :=
    integral_mono (hψ'.integrable.sub hψ.integrable).abs hδi fun w => hdiff w
  have hD : ∀ z, min (Real.exp (V.M + Λf)) (Real.exp (V.M + Λf) * |ψ' z - ψ z|
        + Real.exp (V.M + Λf) * Real.exp (V.M + Λf) * ∫ w, |ψ' w - ψ w| ∂(withDensityReal ρ))
      ≤ pinD (withDensityReal ρ) q (β / N) K1 b z := by
    intro z
    rw [← hK1]
    unfold pinD
    exact min_le_min le_rfl (add_le_add (mul_le_mul_of_nonneg_left (hdiff z) hK1pos.le)
      (mul_le_mul_of_nonneg_left hI (by positivity)))
  have hΨi : Integrable (fun z => C * (β / N) * (1 + ∑ k, q (z - b k))) (withDensityReal ρ) := by
    refine Integrable.const_mul ((integrable_const _).add (integrable_finsetSum _ fun k _ => ?_)) _
    have := integrable_q_left V (b k)
    simpa [hVq] using this
  have hfin := field_marginal_set_bound (V := V) hψ hψ' hlam hΛ1 hΛ2 hr hε hDm hD0 hDb hD
    (B2 := B2) (by rw [← hK1]; exact hB2) hΨi (by rw [← hK1]; exact hΨ) i0 hA
  exact hfin

end HRS.ME.NfU
