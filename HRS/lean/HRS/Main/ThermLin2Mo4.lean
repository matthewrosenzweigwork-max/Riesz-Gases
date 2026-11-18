import HRS.Main.ThermLin2Mo2
import HRS.Main.ThermLin2Mo3

/-!
# THERMLIN2 Mo4: `tl2_noise_cost` (C4)

Uses `tl2_rho_sup_decay_proof` (Mo2) and `tl2_traceNorm_covForm_diff_proof` (Mo3), i.e. no plan statement as a black box.
Pointwise bound of the integrand by `B e^{-c₁ a}` with `c₁ = min (2c₀) κ`, then the length `a + T` of the interval.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P

variable {d : ℕ}

/-- `x ↦ S.ρ t x` is continuous for `t ≥ 0`. -/
theorem tl2Mo_rho_continuous (S : HRS.Main.PreparedData d) {t : ℝ} (ht : 0 ≤ t) : Continuous (S.ρ t) := by
  have hjc := HRS.Q40b.q40b_jointCont (by have := S.hd; omega) (HRS.T25.t25_traj S) t
  have h1 : Continuous fun x : Torus d => (t, x) := Continuous.prodMk continuous_const continuous_id
  exact hjc.comp_continuous h1 (fun x => ⟨⟨ht, le_rfl⟩, Set.mem_univ _⟩)

/-- `S.ρ t` is a probability density for `t ≥ 0`. -/
theorem tl2Mo_rho_density (S : HRS.Main.PreparedData d) {t : ℝ} (ht : 0 ≤ t) : IsProbDensity (S.ρ t) :=
  (HRS.Q40b.q40b_meanField (by have := S.hd; omega) (HRS.T25.t25_traj S) (T := t + 1) (by linarith)).density t
    ⟨ht, by linarith⟩

/-- C4 (proof): uses `tl2_rho_sup_decay_proof`, `tl2_traceNorm_covForm_diff_proof`. -/
theorem tl2_noise_cost_proof (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (m : ℝ) (hm : (d : ℝ) + 2 < m) (T : ℝ) (hT : 0 < T)
    (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ a : ℝ, 0 ≤ a →
      ∫⁻ r in Set.Icc (0 : ℝ) (a + T), ENNReal.ofReal (Real.exp (-c₀ * max (a - r) 0) ^ 2 *
        traceNormForm (covDensT m S.β⁻¹ (a + T) S.ρ r - tl2CbDens S ρβ m (a + T) r)) ≤
        ENNReal.ofReal (C * Real.exp (-c * a)) := by
  have hq : 0 ≤ S.β⁻¹ := inv_nonneg.2 S.hβ.le
  obtain ⟨C₂, κ, hC₂, hκ, hρ⟩ := tl2_rho_sup_decay_proof S h
  obtain ⟨C₃, hC₃, hTr⟩ := tl2_traceNorm_covForm_diff_proof m hm S.β⁻¹ hq
  obtain ⟨hsm, -⟩ := HRS.ThermLin.thermlin_thermal_smooth_pos S h
  have hβc : Continuous ρβ := HRS.StaticLimitAux.continuous_of_smooth hsm
  have hβP : IsProbDensity ρβ := h.1
  set B : ℝ := C₃ * C₂ with hB
  have hB0 : 0 ≤ B := mul_nonneg hC₃ hC₂
  set c₁ : ℝ := min (2 * c₀) κ with hc₁
  have hc₁0 : 0 < c₁ := lt_min (by linarith) hκ
  have hc₁a : c₁ ≤ 2 * c₀ := min_le_left _ _
  have hc₁b : c₁ ≤ κ := min_le_right _ _
  refine ⟨B * (2 / c₁ + T), c₁ / 2, by positivity, by positivity, fun a ha => ?_⟩
  -- pointwise bound
  have hpt : ∀ r ∈ Set.Icc (0 : ℝ) (a + T), Real.exp (-c₀ * max (a - r) 0) ^ 2 *
        traceNormForm (covDensT m S.β⁻¹ (a + T) S.ρ r - tl2CbDens S ρβ m (a + T) r) ≤
        B * Real.exp (-c₁ * a) := by
    intro r hr
    have hr0 : 0 ≤ r := hr.1
    have e1 : covDensT m S.β⁻¹ (a + T) S.ρ r = covForm m S.β⁻¹ (withDensityReal (S.ρ r)) := by
      simp [covDensT, hr]
    have e2 : tl2CbDens S ρβ m (a + T) r = covForm m S.β⁻¹ (withDensityReal ρβ) := by
      simp [tl2CbDens, covDensT, hr]
    rw [e1, e2]
    have h3 := hTr (S.ρ r) ρβ (tl2Mo_rho_continuous S hr0) hβc (tl2Mo_rho_density S hr0) hβP
    have h4 : ∫ x, |S.ρ r x - ρβ x| ≤ C₂ * Real.exp (-κ * r) := by
      have := integral_mono_of_nonneg (μ := (volume : Measure (Torus d))) (f := fun x => |S.ρ r x - ρβ x|)
        (g := fun _ => C₂ * Real.exp (-κ * r)) (Filter.Eventually.of_forall fun x => abs_nonneg _)
        (integrable_const _) (Filter.Eventually.of_forall fun x => hρ r hr0 x)
      simpa using this
    have h5 : traceNormForm (covForm m S.β⁻¹ (withDensityReal (S.ρ r)) - covForm m S.β⁻¹ (withDensityReal ρβ)) ≤
        B * Real.exp (-κ * r) := by
      calc _ ≤ C₃ * ∫ x, |S.ρ r x - ρβ x| := h3
        _ ≤ C₃ * (C₂ * Real.exp (-κ * r)) := mul_le_mul_of_nonneg_left h4 hC₃
        _ = _ := by rw [hB]; ring
    have hsq : Real.exp (-c₀ * max (a - r) 0) ^ 2 = Real.exp (-(2 * c₀) * max (a - r) 0) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hmax0 : 0 ≤ max (a - r) 0 := le_max_right _ _
    have h6 : Real.exp (-c₀ * max (a - r) 0) ^ 2 ≤ Real.exp (-c₁ * max (a - r) 0) := by
      rw [hsq]; apply Real.exp_le_exp.2; nlinarith
    have h7 : Real.exp (-κ * r) ≤ Real.exp (-c₁ * r) := by
      apply Real.exp_le_exp.2; nlinarith
    have h8 : Real.exp (-c₁ * max (a - r) 0) * Real.exp (-c₁ * r) ≤ Real.exp (-c₁ * a) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.2
      have : a ≤ max (a - r) 0 + r := by
        have := le_max_left (a - r) 0; linarith
      nlinarith
    calc Real.exp (-c₀ * max (a - r) 0) ^ 2 * _ ≤ Real.exp (-c₀ * max (a - r) 0) ^ 2 * (B * Real.exp (-κ * r)) :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
      _ ≤ Real.exp (-c₁ * max (a - r) 0) * (B * Real.exp (-c₁ * r)) :=
          mul_le_mul h6 (mul_le_mul_of_nonneg_left h7 hB0) (by positivity) (by positivity)
      _ = B * (Real.exp (-c₁ * max (a - r) 0) * Real.exp (-c₁ * r)) := by ring
      _ ≤ B * Real.exp (-c₁ * a) := mul_le_mul_of_nonneg_left h8 hB0
  calc _ ≤ ∫⁻ r in Set.Icc (0 : ℝ) (a + T), ENNReal.ofReal (B * Real.exp (-c₁ * a)) :=
        setLIntegral_mono measurable_const fun r hr => ENNReal.ofReal_le_ofReal (hpt r hr)
    _ = ENNReal.ofReal (B * Real.exp (-c₁ * a) * (a + T)) := by
        rw [setLIntegral_const, Real.volume_Icc, sub_zero, ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have hu : (c₁ / 2) * a ≤ Real.exp ((c₁ / 2) * a) := by
          have := Real.add_one_le_exp ((c₁ / 2) * a); linarith
        have hexp : Real.exp (-c₁ * a) = Real.exp (-(c₁ / 2) * a) * Real.exp (-(c₁ / 2) * a) := by
          rw [← Real.exp_add]; congr 1; ring
        have hone : Real.exp (-(c₁ / 2) * a) ≤ 1 := by
          rw [Real.exp_le_one_iff]; nlinarith
        have hae : a * Real.exp (-(c₁ / 2) * a) ≤ 2 / c₁ := by
          have h1 : (c₁ / 2 * a) * Real.exp (-(c₁ / 2) * a) ≤ 1 := by
            have hpos := Real.exp_pos (-(c₁ / 2) * a)
            have : Real.exp ((c₁ / 2) * a) * Real.exp (-(c₁ / 2) * a) = 1 := by
              rw [← Real.exp_add]; simp
            nlinarith
          rw [le_div_iff₀ hc₁0]
          nlinarith
        have hpos := Real.exp_pos (-(c₁ / 2) * a)
        have : (a + T) * Real.exp (-c₁ * a) ≤ (2 / c₁ + T) * Real.exp (-(c₁ / 2) * a) := by
          rw [hexp]
          have h1 := mul_le_mul_of_nonneg_right hae hpos.le
          have h2 : T * (Real.exp (-(c₁ / 2) * a) * Real.exp (-(c₁ / 2) * a)) ≤ T * Real.exp (-(c₁ / 2) * a) :=
            mul_le_mul_of_nonneg_left (by nlinarith) hT.le
          nlinarith
        calc B * Real.exp (-c₁ * a) * (a + T) = B * ((a + T) * Real.exp (-c₁ * a)) := by ring
          _ ≤ B * ((2 / c₁ + T) * Real.exp (-(c₁ / 2) * a)) := mul_le_mul_of_nonneg_left this hB0
          _ = B * (2 / c₁ + T) * Real.exp (-(c₁ / 2) * a) := by ring

example := (@tl2_noise_cost_proof : type_of% @tl2_noise_cost)

end HRS.ThermLin.Plan2
