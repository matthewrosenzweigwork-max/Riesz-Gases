import HRS.MS.MovSchAux8

/-!
# S64 (S6.9), part 4: clauses (2) and (4) of `mov_moving_reference` (static identity, dynamic parts)

Namespace `HRS.MS.MovSch`, prefix `s64_`.
* `s64_canon_eq_mod`: `canonicalGibbs = modulatedGibbs (ρ₀ dx)` for `N ≥ 1` (via the densities `Z_can⁻¹ e^{-βH_N}`);
* `s64_modGibbs_translate`: `modulatedGibbs (ρ₀(· - a) dx) = canonicalGibbs.map (X ↦ X + a)`;
* `s64_ref2_static`: the density identity of clause (2);
* `s64_ref2_dyn`: the dynamical part of clause (2), from `GibbsInvariant` (translation of the particle solution, S6.8(1) with `-a₀`);
* `s64_ref4`: clause (4), from `GibbsEntropyContraction` and the data-processing inequality for `klDiv`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovSch

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s64_canon_eq_mod {s q β : ℝ} (hs0 : 0 ≤ s) (hq : 0 < q) (hβ : 0 < β) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsThermalDensity (HRS.Whole.rieszKernel d s) (HRS.Whole.confinement q) β ρ) {N : ℕ} (hN : 1 ≤ N) :
    HRS.Whole.canonicalGibbs (HRS.Whole.rieszKernel d s) (HRS.Whole.confinement q) N β =
      HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β (HRS.Whole.withDensityReal ρ) := by
  have hZ := s64_Zpos (d := d) hs0 hq hβ hN
  have hK := s64_K_pos hs0 hq hβ hρ hN
  rw [s64_modGibbs_density hρ.1 hK]
  unfold HRS.Whole.canonicalGibbs
  rw [← HRS.MS.Canon.cn_withDensity_const_mul _ _ (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hZ).ne')]
  congr 1
  funext X
  rw [s64_movQ_thermal hs0 hq hβ hρ hN X, ← ENNReal.ofReal_inv_of_pos hZ,
    ← ENNReal.ofReal_mul (inv_pos.2 hZ).le]

theorem s64_modGibbs_translate {s q β : ℝ} (hs0 : 0 ≤ s) (hq : 0 < q) (hβ : 0 < β) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsThermalDensity (HRS.Whole.rieszKernel d s) (HRS.Whole.confinement q) β ρ) {N : ℕ} (hN : 1 ≤ N)
    (a : Euc d) :
    HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β (HRS.Whole.withDensityReal (fun x => ρ (x - a))) =
      (HRS.Whole.canonicalGibbs (HRS.Whole.rieszKernel d s) (HRS.Whole.confinement q) N β).map
        (movtr_cfgEquiv d N a) := by
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := HRS.MS.Wr.wr13a_isProb_density hρ.1
  rw [s64_withDensityReal_translate, movtr_modulatedGibbs_translate, s64_canon_eq_mod hs0 hq hβ hρ hN]
  rfl

lemma s64_map_cancel {N : ℕ} (μ : Measure (EucConfig d N)) (a : Euc d) :
    (μ.map (movtr_cfgEquiv d N a)).map (movtr_cfgEquiv d N (-a)) = μ := by
  rw [Measure.map_map (movtr_cfgEquiv d N (-a)).measurable (movtr_cfgEquiv d N a).measurable]
  have : (movtr_cfgEquiv d N (-a)) ∘ (movtr_cfgEquiv d N a) = id := by
    funext X i
    simp [movtr_cfgEquiv_apply]
  rw [this, Measure.map_id]

lemma s64_isProbDensity_translate {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) (a : Euc d) :
    HRS.Whole.IsProbDensity (fun x => ρ (x - a)) :=
  ⟨fun x => HRS.Whole.IsProbDensity.nonneg hρ _, hρ.measurable.comp (measurable_sub_const a), by
    rw [integral_sub_right_eq_self (fun x => ρ x) a]
    exact hρ.integral_one⟩

theorem s64_ref2_static {s q β : ℝ} (hs0 : 0 ≤ s) (hq : 0 < q) (hβ : 0 < β) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsThermalDensity (HRS.Whole.rieszKernel d s) (HRS.Whole.confinement q) β ρ) {N : ℕ} (hN : 1 ≤ N)
    (a : Euc d) :
    HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β (HRS.Whole.withDensityReal (fun x => ρ (x - a))) =
      (volume : Measure (EucConfig d N)).withDensity (fun X =>
        ENNReal.ofReal (movQDensity d s β N (fun x => ρ (x - a)) X)) := by
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := HRS.MS.Wr.wr13a_isProb_density hρ.1
  refine s64_modGibbs_density (s64_isProbDensity_translate hρ.1 a) ?_
  rw [s64_withDensityReal_translate, movtr_gibbsNormalizer_translate]
  exact s64_K_pos hs0 hq hβ hρ hN

end HRS.MS.MovSch

end
