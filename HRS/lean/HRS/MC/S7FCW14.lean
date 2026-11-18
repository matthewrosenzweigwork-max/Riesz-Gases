import HRS.MC.S7FCDefs
import HRS.MC.S7FCD3A1
import HRS.MC.S7FCD3A3
import HRS.MC.S7FCD3A4
import HRS.MC.S7FCD3B
import HRS.MC.S7WQ
import HRS.MC.S7S7cAux1

/-!
# FC-D3 assembly: `s7_FC_D3_initial` (time-zero `W_q` convergence of `η_N` to a centred Gaussian `ν`)

Route (plan `scope_d3.md`, sections L6-L8), all inputs already proved:
* `d3_hG` (L1): the susceptibility covariance is the response-representative covariance;
* `d3_zeta_weak` (L5): weak convergence of `law ζ_{N+1}` to `ν`;
* `d3_zeta_pow` (L3): uniform `2m`-th moments of `‖ζ_{N+1}‖`;
* `s7_WQ_weak_ui_wasserstein_proof`: `W_q(law ζ_{N+1}, ν) → 0`;
* `d3_eta_sub_zeta` (L4) with `wassersteinE_le_of_coupling`: `W_q(law η_{N+1}, law ζ_{N+1}) ≤ C/√(N+1)`;
* `wassersteinE_triangle` and a squeeze in `ℝ≥0∞`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCW14

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec

variable {d : ℕ}

theorem S7FCW14_ofReal_rpow_inv {c q : ℝ} (hq : 1 ≤ q) (hc : 0 ≤ c) :
    (ENNReal.ofReal (c ^ q)) ^ (1 / q) = ENNReal.ofReal c := by
  have hq0 : 0 < q := by linarith
  rw [one_div, ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hc q) (inv_nonneg.2 hq0.le),
    Real.rpow_rpow_inv hc hq0.ne']

theorem S7FCW14_lint_bound {Ω B : Type*} [MeasurableSpace Ω] [NormedAddCommGroup B] (P : Measure Ω)
    [IsProbabilityMeasure P] {q c : ℝ} (hq : 1 ≤ q) (X Y : Ω → B) (h : ∀ ω, ‖X ω - Y ω‖ ≤ c) :
    ∫⁻ ω, ENNReal.ofReal (‖X ω - Y ω‖ ^ q) ∂P ≤ ENNReal.ofReal (c ^ q) := by
  have hq0 : 0 ≤ q := by linarith
  calc ∫⁻ ω, ENNReal.ofReal (‖X ω - Y ω‖ ^ q) ∂P
      ≤ ∫⁻ _ω, ENNReal.ofReal (c ^ q) ∂P :=
        lintegral_mono fun ω =>
          ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (norm_nonneg _) (h ω) hq0)
    _ = ENNReal.ofReal (c ^ q) := by rw [lintegral_const, measure_univ, mul_one]

theorem s7_FC_D3_initial_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (ν : Measure (NegSobolev d r))
    [IsProbabilityMeasure ν]
    (hν : IsCenteredGaussianWithCov r ν
      (susceptibilityCov (periodicRiesz d R.D.s) (withDensityReal R.ρ₀) R.β₀))
    (q : ℝ) (hq : 1 ≤ q) :
    Tendsto (fun N : ℕ => wassersteinE q
        (law (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀))
          (fun X => etaE r X (withDensityReal R.ρ₀))) ν) atTop (𝓝 0) := by
  have hd : 2 ≤ d := R.hd
  have hs0 : 0 ≤ R.D.s := R.D.hs0
  have hs : R.D.s < (d : ℝ) / 2 := R.hs
  have hγ : 0 ≤ R.β₀ := by
    rcases R.hβ₀ with h | h
    · exact h.le
    · rw [h.2]
  have hρ : SmoothPosDensity R.ρ₀ := R.hρ₀
  have hr2 : (d : ℝ) < 2 * r := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    rw [hr]; linarith
  haveI hμ0 : IsProbabilityMeasure (withDensityReal R.ρ₀) := HRS.MC.SEdge.B3.b3_prob hρ
  have hQ : ∀ n : ℕ, IsProbabilityMeasure (sed_Q d R.D.s (n + 1) R.β₀ R.ρ₀) :=
    fun n => HRS.MC.SEdge.B4b.b4b_isProb hd hs0 hs hγ hρ (n + 1) (by omega)
  have hζm : ∀ n : ℕ, Measurable (zetaE r (sed_Q d R.D.s (n + 1) R.β₀ R.ρ₀)) := fun n =>
    haveI := hQ n
    HRS.MC.Sec7.S7c.s7c_zeta_meas (by omega : 1 ≤ n + 1) hr2 (sed_Q d R.D.s (n + 1) R.β₀ R.ρ₀)
  have hηm : ∀ n : ℕ, Measurable (fun X : Config d (n + 1) => etaE r X (withDensityReal R.ρ₀)) :=
    fun n => (HRS.measurable_ofMeasureDiff_empirical (m := r) hr2 (withDensityReal R.ρ₀)
      (by omega : 1 ≤ n + 1)).const_smul (Real.sqrt ((n + 1 : ℕ) : ℝ))
  -- the measures `μ n = law ζ_{n+1}`
  obtain ⟨μ, hμdef⟩ : ∃ μ : ℕ → Measure (NegSobolev d r), μ = fun n =>
      law (sed_Q d R.D.s (n + 1) R.β₀ R.ρ₀) (zetaE r (sed_Q d R.D.s (n + 1) R.β₀ R.ρ₀)) := ⟨_, rfl⟩
  have hμn : ∀ n, μ n = law (sed_Q d R.D.s (n + 1) R.β₀ R.ρ₀)
      (zetaE r (sed_Q d R.D.s (n + 1) R.β₀ R.ρ₀)) := fun n => by rw [hμdef]
  have hμP : ∀ n, IsProbabilityMeasure (μ n) := fun n => by
    rw [hμn n]
    haveI := hQ n
    exact (Measure.isProbabilityMeasure_map_iff (hζm n).aemeasurable).2 inferInstance
  haveI : ∀ n, IsProbabilityMeasure (μ n) := hμP
  have hPη : ∀ n : ℕ, IsProbabilityMeasure
      (law (sed_Q d R.D.s (n + 1) R.β₀ R.ρ₀) (fun X : Config d (n + 1) => etaE r X (withDensityReal R.ρ₀))) :=
    fun n => by
      haveI := hQ n
      exact (Measure.isProbabilityMeasure_map_iff (hηm n).aemeasurable).2 inferInstance
  -- Gaussian in response-representative form and weak convergence of `ζ`
  have hG := HRS.MC.Sec7.FCD3.d3_hG hd hs0 hs hγ hρ hν
  have hzw := HRS.MC.Sec7.FCD3B.d3_zeta_weak hd hs0 hs hγ hρ hr ν hG
  have hweakμ : ∀ F : NegSobolev d r → ℝ, Continuous F → (∃ M, ∀ x, |F x| ≤ M) →
      Tendsto (fun n => ∫ x, F x ∂(μ n)) atTop (𝓝 (∫ x, F x ∂ν)) := by
    intro F hF hb
    refine Tendsto.congr (fun n => ?_) (hzw F hF hb)
    rw [hμn n, integral_map (hζm n).aemeasurable hF.aestronglyMeasurable]
  -- uniform moments of order `q + δ = 2m`
  obtain ⟨m, hqm⟩ := exists_nat_gt q
  have hexp : q + (2 * (m : ℝ) - q) = ((2 * m : ℕ) : ℝ) := by push_cast; ring
  have hδ : 0 < 2 * (m : ℝ) - q := by linarith
  obtain ⟨C₁, hC₁⟩ := HRS.MC.Sec7.FCD3.d3_zeta_pow hd hs0 hs hγ hρ hr m
  have hmom : ∃ C : ℝ, ∀ n : ℕ, Integrable (fun x : NegSobolev d r => ‖x‖ ^ (q + (2 * (m : ℝ) - q)))
      (μ n) ∧ ∫ x, ‖x‖ ^ (q + (2 * (m : ℝ) - q)) ∂(μ n) ≤ C := by
    refine ⟨C₁, fun n => ?_⟩
    obtain ⟨hint, hle⟩ := hC₁ (n + 1) (by omega)
    rw [hμn n, hexp]
    simp only [Real.rpow_natCast]
    refine ⟨?_, ?_⟩
    · exact (integrable_map_measure (continuous_norm.pow (2 * m)).aestronglyMeasurable
        (hζm n).aemeasurable).2 hint
    · exact le_trans (le_of_eq (integral_map (hζm n).aemeasurable
        (continuous_norm.pow (2 * m)).aestronglyMeasurable)) hle
  -- `W_q(law ζ_{n+1}, ν) → 0`
  have hW := HRS.MC.Sec7.WQ.s7_WQ_weak_ui_wasserstein_proof μ ν hweakμ q (2 * (m : ℝ) - q) hq hδ hmom
  -- the coupling bound `W_q(law η_{n+1}, law ζ_{n+1}) ≤ C/√(n+1)`
  obtain ⟨C₂, hC₂0, hC₂⟩ := HRS.MC.Sec7.FCD3.d3_eta_sub_zeta hd hs0 hs hγ hρ hr
  have hcoup : ∀ n : ℕ, wassersteinE q
      (law (sed_Q d R.D.s (n + 1) R.β₀ R.ρ₀) (fun X : Config d (n + 1) => etaE r X (withDensityReal R.ρ₀)))
      (μ n) ≤ ENNReal.ofReal (C₂ / Real.sqrt ((n + 1 : ℕ) : ℝ)) := by
    intro n
    rw [hμn n]
    haveI := hQ n
    have hc : 0 ≤ C₂ / Real.sqrt ((n + 1 : ℕ) : ℝ) := div_nonneg hC₂0 (Real.sqrt_nonneg _)
    refine (HRS.wassersteinE_le_of_coupling (sed_Q d R.D.s (n + 1) R.β₀ R.ρ₀) q hq
      (fun X : Config d (n + 1) => etaE r X (withDensityReal R.ρ₀))
      (zetaE r (sed_Q d R.D.s (n + 1) R.β₀ R.ρ₀)) (hηm n).aemeasurable (hζm n).aemeasurable).trans ?_
    refine (ENNReal.rpow_le_rpow (S7FCW14_lint_bound _ hq _ _
      (fun ω => hC₂ (n + 1) (by omega) ω) ) (one_div_nonneg.2 (by linarith))).trans ?_
    exact le_of_eq (S7FCW14_ofReal_rpow_inv hq hc)
  -- squeeze
  have hT : Tendsto (fun n : ℕ => ENNReal.ofReal (C₂ / Real.sqrt ((n + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1))
    have h2 : Tendsto (fun n : ℕ => ENNReal.ofReal (C₂ / Real.sqrt ((n + 1 : ℕ) : ℝ)))
        atTop (𝓝 (ENNReal.ofReal 0)) :=
      ENNReal.tendsto_ofReal ((tendsto_const_nhds : Tendsto (fun _ : ℕ => C₂) atTop (𝓝 C₂)).div_atTop h1)
    rw [ENNReal.ofReal_zero] at h2
    exact h2
  have hsum := hW.add hT
  rw [zero_add] at hsum
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum ?_ ?_
  · intro n
    exact zero_le
  intro n
  show wassersteinE q (law (sed_Q d R.D.s (n + 1) R.β₀ R.ρ₀)
      (fun X : Config d (n + 1) => etaE r X (withDensityReal R.ρ₀))) ν ≤
    wassersteinE q (μ n) ν + ENNReal.ofReal (C₂ / Real.sqrt ((n + 1 : ℕ) : ℝ))
  calc wassersteinE q (law (sed_Q d R.D.s (n + 1) R.β₀ R.ρ₀)
        (fun X : Config d (n + 1) => etaE r X (withDensityReal R.ρ₀))) ν
      ≤ wassersteinE q (law (sed_Q d R.D.s (n + 1) R.β₀ R.ρ₀)
          (fun X : Config d (n + 1) => etaE r X (withDensityReal R.ρ₀))) (μ n) +
          wassersteinE q (μ n) ν :=
        wassersteinE_triangle q hq _ _ _
    _ ≤ ENNReal.ofReal (C₂ / Real.sqrt ((n + 1 : ℕ) : ℝ)) + wassersteinE q (μ n) ν :=
        add_le_add (hcoup n) le_rfl
    _ = wassersteinE q (μ n) ν + ENNReal.ofReal (C₂ / Real.sqrt ((n + 1 : ℕ) : ℝ)) := add_comm _ _

end HRS.MC.Sec7.S7FCW14

end
