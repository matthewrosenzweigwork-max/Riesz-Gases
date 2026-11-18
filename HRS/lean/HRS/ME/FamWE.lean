/-
# HRS.ME.FamW (packet W4b): the lower bound of `critical_family_sharpness`

`critical_family_sharpness_lower` is the lower conjunct of the frozen `HRS.Main.critical_family_sharpness`
(`H:eq:critical-family-sharpness`), with constants `c`, `N₀` chosen before the density family `ρ`.

Mechanism.  Let `R = 16 (1 + β ĝ(k))`, `v₀ = 1/(2 (1 + β ĝ(k))) = 8/R`.
* `rateVarN N 0 → v₀` (`rateVarN_zero_tendsto`, with the uniform density and `susceptibilityCov_one_cos`),
  so `rateVarN N 0 ≥ v₀/2` for large `N`;
* `∫₀^R rateVarN N ≤ 2` and `rateVarN' = √N E[Y³]` give `∫₀^R |√N E Y_{N,θ}³| dθ ≥ v₀/2 - 2/R = v₀/4`
  (`rate_variation_lower`);
* `|E Y³| ≤ 3 √(32 D²) · W₂(law Y, Gaussian)` pointwise (`third_moment_pointwise`), with `D` the
  sub-Gaussian constant of Lemma 4.19, independent of `ρ` because the thermal density is unique
  (`thermal_eq_of_thermal`);
* integrating, `v₀/4 ≤ √N · K · ∫⁻ W₂`, i.e. the stated bound with `c = v₀/(4K)`, `K = 3 √(32 D²)`.
-/
import HRS.ME.FamWA
import HRS.ME.FamWB
import HRS.ME.FamWC
import HRS.ME.FamWD
import HRS.ME.FamVC

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.ME.FamW

variable {d : ℕ} {s : ℝ}

/-- Two thermal densities of the same continuous potential coincide. -/
theorem thermal_eq_of_thermal (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (k : Lattice d) (θ : ℝ) (ρ ρ' : Torus d → ℝ)
    (hρ : IsThermalDensity (periodicRiesz d s) (rateV k β θ) β ρ)
    (hρ' : IsThermalDensity (periodicRiesz d s) (rateV k β θ) β ρ') : ρ = ρ' := by
  have hVc : Continuous (rateV k β θ) := Q32c.q32c_rateV_continuous k θ
  obtain ⟨hpos, hcont⟩ := Q41.q41_thermal_pos_cont hd hs0 hsd hβ hVc hρ
  obtain ⟨hpos', hcont'⟩ := Q41.q41_thermal_pos_cont hd hs0 hsd hβ hVc hρ'
  exact (PDE.MFThermal.thermal_unique hd s hs0 hsd β hβ (rateV k β θ) ρ ρ' hρ hcont hpos
    hρ' hcont' hpos').symm

/-- **Pointwise third-moment bound.**  If the finite-`N` law of `Y_{N,θ}` and the Gaussian
`N(0, v)` satisfy the sub-Gaussian tail bound with constant `D`, then
`|E Y³| ≤ 3 √(32 D²) · W₂(law Y, N(0,v))`. -/
theorem third_moment_pointwise (hd : 2 ≤ d) (hs : (d : ℝ) / 2 ≤ s) (hsd : s < d) {β : ℝ}
    (hβ : 0 < β) (k : Lattice d) {N : ℕ} (hN : 0 < N) (θ v D : ℝ) (hD : 0 < D)
    (htail : ∀ x : ℝ, 0 ≤ x →
      rateGibbs d s k β θ N {X | x < |rateY d s k β N θ X|} +
          gaussianReal 0 v.toNNReal {z | x < |z|} ≤ ENNReal.ofReal (4 * Real.exp (-x ^ 2 / (2 * D)))) :
    ENNReal.ofReal |∫ X, rateY d s k β N θ X ^ 3 ∂(rateGibbs d s k β θ N)| ≤
      ENNReal.ofReal (3 * Real.sqrt (32 * D ^ 2)) *
        wassersteinE 2 ((rateGibbs d s k β θ N).map (rateY d s k β N θ)) (gaussianReal 0 v.toNNReal) := by
  haveI := rateGibbs_isProb' hd hs hsd hβ k hN θ
  have hY : Measurable (rateY d s k β N θ) := HRS.ME.FamV.measurable_rateY s k β θ N
  haveI hP : IsProbabilityMeasure ((rateGibbs d s k β θ N).map (rateY d s k β N θ)) :=
    (Measure.isProbabilityMeasure_map_iff hY.aemeasurable).2 inferInstance
  haveI hQ : IsProbabilityMeasure (gaussianReal 0 v.toNNReal) := inferInstance
  have hPtail : ∀ x : ℝ, 0 ≤ x →
      ((rateGibbs d s k β θ N).map (rateY d s k β N θ)) {z | x < |z|} ≤
        ENNReal.ofReal (4 * Real.exp (-x ^ 2 / (2 * D))) := fun x hx => by
    have hm : MeasurableSet {z : ℝ | x < |z|} := measurableSet_lt measurable_const measurable_abs
    rw [Measure.map_apply hY hm]
    exact le_trans (le_self_add) (htail x hx)
  have hQtail : ∀ x : ℝ, 0 ≤ x → gaussianReal 0 v.toNNReal {z | x < |z|} ≤
      ENNReal.ofReal (4 * Real.exp (-x ^ 2 / (2 * D))) := fun x hx =>
    le_trans (le_add_self) (htail x hx)
  obtain ⟨hP4, hPB⟩ := fourth_moment_of_tail _ D hD hPtail
  obtain ⟨hQ4, hQB⟩ := fourth_moment_of_tail _ D hD hQtail
  have h := third_moment_le_wasserstein _ _ (32 * D ^ 2) (by positivity) hP4 hQ4 hPB hQB
    (gaussianReal_third_moment_zero v.toNNReal)
  have hint : ∫ z, z ^ 3 ∂((rateGibbs d s k β θ N).map (rateY d s k β N θ)) =
      ∫ X, rateY d s k β N θ X ^ 3 ∂(rateGibbs d s k β θ N) :=
    integral_map hY.aemeasurable (by fun_prop : Continuous fun z : ℝ => z ^ 3).aestronglyMeasurable
  rw [hint] at h
  exact h


/-- **W4b.**  The lower bound of the frozen `HRS.Main.critical_family_sharpness`, with the constants `c`
and `N₀` chosen before the density family `ρ`. -/
theorem critical_family_sharpness_lower {d : ℕ} (hd : 2 ≤ d) {β : ℝ} (hβ : 0 < β) (k : Lattice d)
    (hk : k ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ ρ : ℝ → Torus d → ℝ,
      (∀ θ, IsThermalDensity (periodicRiesz d ((d : ℝ) / 2)) (rateV k β θ) β (ρ θ)) →
      ∀ N : ℕ, N₀ ≤ N →
        ENNReal.ofReal (c * (N : ℝ) ^ (-(1 : ℝ) / 2)) ≤
          ∫⁻ θ in Set.Icc (0 : ℝ) (16 * (1 + β * rieszCoeff d ((d : ℝ) / 2) k)),
            wassersteinE 2 (Main.rateLaw d ((d : ℝ) / 2) k β N θ)
              (Main.rateGaussian d ((d : ℝ) / 2) k β (ρ θ)) := by
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = (d : ℝ) / 2 := ⟨_, rfl⟩
  rw [← hsdef]
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ s := by rw [hsdef]; positivity
  have hsd : s < d := by rw [hsdef]; linarith
  have hs : (d : ℝ) / 2 ≤ s := hsdef.symm.le
  have hd1 : 1 ≤ d := by omega
  obtain ⟨g, hgdef⟩ : ∃ g : ℝ, g = rieszCoeff d s k := ⟨_, rfl⟩
  rw [← hgdef]
  have hg : 0 ≤ g := by rw [hgdef]; exact (rieszCoeff_pos hd hs0 hsd k hk).le
  have h1g : 0 < 1 + β * g := by positivity
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = 16 * (1 + β * g) := ⟨_, rfl⟩
  rw [← hRdef]
  obtain ⟨v0, hv0def⟩ : ∃ v0 : ℝ, v0 = 1 / (2 * (1 + β * g)) := ⟨_, rfl⟩
  have hRpos : 0 < R := by rw [hRdef]; positivity
  have hv0 : 0 < v0 := by rw [hv0def]; positivity
  have hRv : 2 / R = v0 / 4 := by
    rw [hRdef, hv0def]; field_simp; ring
  -- a canonical thermal family
  have hex : ∀ θ : ℝ, ∃ ρ : Torus d → ℝ,
      IsThermalDensity (periodicRiesz d s) (rateV k β θ) β ρ := fun θ =>
    let ⟨ρ, h, _, _⟩ := PDE.MFThermalAssembly.thermal_exists_continuous hd1 s hs0 hsd
      (rateV k β θ) (Q32c.q32c_rateV_continuous k θ) β hβ
    ⟨ρ, h⟩
  choose ρs hρs using hex
  obtain ⟨D, hD2, hDtail⟩ := response_subGaussian_proof hd hs hsd β hβ k hk ρs hρs 0 R
  have hDpos : 0 < D := by linarith
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 3 * Real.sqrt (32 * D ^ 2) := ⟨_, rfl⟩
  have hKpos : 0 < K := by rw [hKdef]; positivity
  -- the variance at `θ = 0` converges to `v0`
  have hlim := rateVarN_zero_tendsto hd hs hsd hβ k hk (ρs 0) (hρs 0)
  have hcov0 : susceptibilityCov (periodicRiesz d s) (withDensityReal (ρs 0)) β
      (Torus.cosMode k) (Torus.cosMode k) = v0 := by
    rw [thermal_rateV_zero hd hs0 hsd hβ k (ρs 0) (hρs 0), hv0def, hgdef]
    exact susceptibilityCov_one_cos hd hs0 hsd hβ k hk
  rw [hcov0] at hlim
  obtain ⟨N1, hN1⟩ := eventually_atTop.1
    (hlim.eventually (lt_mem_nhds (show v0 / 2 < v0 by linarith)))
  refine ⟨v0 / (4 * K), by positivity, max N1 2, fun ρ hρ N hN => ?_⟩
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hN1' : N1 ≤ N := le_trans (le_max_left _ _) hN
  have hN0 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.2 hNr
  have hV : v0 / 2 < rateVarN d s k β N 0 := hN1 N hN1'
  have hvar := rate_variation_lower hd hs hsd hβ k hk hN2 hRpos
  obtain ⟨F, hFdef⟩ : ∃ F : ℝ → ℝ, F = fun θ =>
      |Real.sqrt N * ∫ X, rateY d s k β N θ X ^ 3 ∂(rateGibbs d s k β θ N)| := ⟨_, rfl⟩
  have hFge : v0 / 4 ≤ ∫ θ in (0 : ℝ)..R, F θ := by
    rw [hFdef]; rw [hRv] at hvar; linarith
  have hint : IntegrableOn F (Set.Ioc 0 R) := by
    by_contra hni
    have h0 : ∫ θ in (0 : ℝ)..R, F θ = 0 := by
      rw [intervalIntegral.integral_of_le hRpos.le]; exact integral_undef hni
    linarith
  have hlow : ENNReal.ofReal (v0 / 4) ≤ ∫⁻ θ in Set.Icc (0 : ℝ) R, ENNReal.ofReal (F θ) :=
    calc ENNReal.ofReal (v0 / 4) ≤ ENNReal.ofReal (∫ θ in (0 : ℝ)..R, F θ) :=
          ENNReal.ofReal_le_ofReal hFge
      _ = ENNReal.ofReal (∫ θ in Set.Ioc 0 R, F θ) := by
          rw [intervalIntegral.integral_of_le hRpos.le]
      _ = ∫⁻ θ in Set.Ioc 0 R, ENNReal.ofReal (F θ) :=
          ofReal_integral_eq_lintegral_ofReal hint
            (Eventually.of_forall fun θ => by rw [hFdef]; exact abs_nonneg _)
      _ = ∫⁻ θ in Set.Icc (0 : ℝ) R, ENNReal.ofReal (F θ) := setLIntegral_congr Ioc_ae_eq_Icc
  have hpt : ∀ θ ∈ Set.Icc (0 : ℝ) R, ENNReal.ofReal (F θ) ≤
      ENNReal.ofReal (Real.sqrt N * K) *
        wassersteinE 2 (Main.rateLaw d s k β N θ) (Main.rateGaussian d s k β (ρ θ)) := by
    intro θ hθ
    have hρeq : ρ θ = ρs θ := thermal_eq_of_thermal hd hs0 hsd hβ k θ _ _ (hρ θ) (hρs θ)
    have hp := third_moment_pointwise hd hs hsd hβ k hN0 θ
      (susceptibilityCov (periodicRiesz d s) (withDensityReal (ρs θ)) β
        (Torus.cosMode k) (Torus.cosMode k)) D hDpos (fun x hx => hDtail x hx N hN2 θ hθ)
    rw [← hKdef] at hp
    have hG : Main.rateGaussian d s k β (ρ θ) = gaussianReal 0
        (susceptibilityCov (periodicRiesz d s) (withDensityReal (ρs θ)) β
          (Torus.cosMode k) (Torus.cosMode k)).toNNReal := by
      rw [hρeq]; rfl
    rw [hG]
    have hL : Main.rateLaw d s k β N θ = (rateGibbs d s k β θ N).map (rateY d s k β N θ) := rfl
    rw [hL, hFdef]
    show ENNReal.ofReal |Real.sqrt N * _| ≤ _
    rw [abs_mul, abs_of_pos hsqrt, ENNReal.ofReal_mul hsqrt.le, ENNReal.ofReal_mul hsqrt.le, mul_assoc]
    exact mul_le_mul' le_rfl hp
  have hmono : ∫⁻ θ in Set.Icc (0 : ℝ) R, ENNReal.ofReal (F θ) ≤
      ENNReal.ofReal (Real.sqrt N * K) *
        ∫⁻ θ in Set.Icc (0 : ℝ) R,
          wassersteinE 2 (Main.rateLaw d s k β N θ) (Main.rateGaussian d s k β (ρ θ)) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact setLIntegral_mono' measurableSet_Icc hpt
  have hsq : (N : ℝ) ^ (-(1 : ℝ) / 2) = 1 / Real.sqrt N := by
    rw [show -(1 : ℝ) / 2 = -(1 / 2) by ring, Real.rpow_neg hNr.le, ← Real.sqrt_eq_rpow]
    simp
  have hak : 0 < Real.sqrt N * K := by positivity
  have hc : v0 / (4 * K) * (N : ℝ) ^ (-(1 : ℝ) / 2) = v0 / 4 * (1 / (Real.sqrt N * K)) := by
    rw [hsq]; field_simp
  calc ENNReal.ofReal (v0 / (4 * K) * (N : ℝ) ^ (-(1 : ℝ) / 2))
      = ENNReal.ofReal (v0 / 4) * ENNReal.ofReal (1 / (Real.sqrt N * K)) := by
        rw [hc, ENNReal.ofReal_mul (by positivity)]
    _ ≤ (ENNReal.ofReal (Real.sqrt N * K) *
          ∫⁻ θ in Set.Icc (0 : ℝ) R,
            wassersteinE 2 (Main.rateLaw d s k β N θ) (Main.rateGaussian d s k β (ρ θ))) *
          ENNReal.ofReal (1 / (Real.sqrt N * K)) := by
        gcongr
        exact le_trans hlow hmono
    _ = (ENNReal.ofReal (1 / (Real.sqrt N * K)) * ENNReal.ofReal (Real.sqrt N * K)) *
          ∫⁻ θ in Set.Icc (0 : ℝ) R,
            wassersteinE 2 (Main.rateLaw d s k β N θ) (Main.rateGaussian d s k β (ρ θ)) := by ring
    _ = ∫⁻ θ in Set.Icc (0 : ℝ) R,
            wassersteinE 2 (Main.rateLaw d s k β N θ) (Main.rateGaussian d s k β (ρ θ)) := by
        rw [← ENNReal.ofReal_mul (by positivity), one_div_mul_cancel hak.ne', ENNReal.ofReal_one,
          one_mul]

end HRS.ME.FamW
