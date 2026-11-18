import HRS.MC.S7PIF4A
import HRS.MC.S7PIM1
import HRS.MC.S7PIM3
import HRS.MC.S7PIF1Dual

/-!
# Packet piF4, part B: pointwise-in-time integrability of `ℬ̃_N`, the centring of `ζ_N`, constancy of the Itô integral

* `S7PIF4_tilde_integrable`: `ω ↦ ℬ̃_N^r(X_r ω) ∈ E_m` is integrable for every `r ≥ 0` and `N ≥ 1`;
* `S7PIF4_zeta_eval`: `ζ_N^u(g) = √N (flucPair - E flucPair)` for smooth `g`;
* `S7PIF4_mart_const`: an Itô integral of an integrand vanishing outside `[0,τ]` is constant after `τ` (for all times at once).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIF4

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIM

variable {d : ℕ}

/-- `ℬ̃_N^r` is integrable in `E_m` (not only the centred field of M1). -/
theorem S7PIF4_tilde_integrable (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) {N : ℕ} (hN : 1 ≤ N)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hreal : PreparedRealization R.D P
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) X₀ W X)
    {r : ℝ} (hr : 0 ≤ r) :
    Integrable (fun ω => quadFieldTilde m R.D.s (withDensityReal (R.ρ r)) (X r.toNNReal ω)) P := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hN0 : 0 < N := hN
  have hS := hreal.solution 0
  rcases Nat.lt_or_ge N 2 with h1 | h2
  · have hN1 : N = 1 := by omega
    subst hN1
    obtain ⟨C1, hC1⟩ := S7PIM_tilde_bdd_one R (m := m) (by linarith)
    exact Integrable.of_bound (S7PIM_tilde_measurable R m X hS.adapted hr).aestronglyMeasurable C1
      (Filter.Eventually.of_forall fun ω => hC1 r hr (X r.toNNReal ω))
  · have hr' : (d : ℝ) < 2 * (2 * (d : ℝ) + 6 - 2) := by linarith
    have hrm : 2 * (d : ℝ) + 6 ≤ m := by linarith
    have hint := S7PIM_integrable_tilde R _ rfl h2 P X₀ W X hreal hr
    have h := (HRS.MD.EQInterp.embedCLM (d := d) hrm).integrable_comp hint
    refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
    exact (S7PIM_tilde_embed R hr' hrm hN0 hr (X r.toNNReal ω)).symm

/-- The centring of `ζ_N^u`: `ζ_N^u(g) = √N (flucPair(X_u) - E flucPair(X_u))`. -/
theorem S7PIF4_zeta_eval (m : ℝ) (hm : (d : ℝ) < 2 * m) {N : ℕ} (hN : 1 ≤ N)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → Config d N) (hX : ∀ s, Measurable (X s)) (u : ℝ) {g : Torus d → ℝ}
    (hg : Torus.IsSmooth g) (ρ : Torus d → ℝ) (ω : Ω) :
    NegSobolev.eval (zetaAt m P X u ω) g = Real.sqrt N *
      (flucPair (X u.toNNReal ω) ρ g - ∫ ω', flucPair (X u.toNNReal ω') ρ g ∂P) := by
  have hN0 : 0 < N := hN
  have hgc : Continuous g := HRS.MC.Sec7.S7PIS1.S7PIS1_cont_of_smooth hg
  set P' : Measure (Config d N) := P.map (X u.toNNReal) with hP'
  have : IsProbabilityMeasure P' :=
    ⟨by rw [hP', Measure.map_apply (hX _) MeasurableSet.univ]; simp⟩
  have : IsProbabilityMeasure (meanEmpirical P') := isProbabilityMeasure_meanEmpirical P' hN
  have : IsProbabilityMeasure (empirical (X u.toNNReal ω)) := empirical_isProbabilityMeasure hN0 _
  have h1 : NegSobolev.eval (zetaAt m P X u ω) g =
      Real.sqrt N * (pair (empirical (X u.toNNReal ω)) g - pair (meanEmpirical P') g) := by
    unfold zetaAt zetaE
    rw [HRS.MC.Sec7.S7PIF1.S7PIF1_eval_smul, NegSobolev.eval_ofMeasureDiff hm _ _ g hg]
  -- the mean of the empirical pairing
  have hmeas : ∀ i : Fin N, Measurable fun ω' => g (X u.toNNReal ω' i) := fun i =>
    hgc.measurable.comp ((measurable_pi_apply i).comp (hX _))
  have hbdd : ∀ i : Fin N, Integrable (fun ω' => g (X u.toNNReal ω' i)) P := fun i => by
    obtain ⟨C, hC⟩ := (isCompact_univ.image hgc).isBounded.exists_norm_le
    exact Integrable.of_bound (hmeas i).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun ω' => hC _ ⟨_, Set.mem_univ _, rfl⟩)
  have hmean : pair (meanEmpirical P') g = ∫ ω', pair (empirical (X u.toNNReal ω')) g ∂P := by
    unfold pair
    rw [integral_meanEmpirical P' hgc]
    have e : ∀ i : Fin N, ∫ x, g (x i) ∂P' = ∫ ω', g (X u.toNNReal ω' i) ∂P := fun i =>
      integral_map (hX _).aemeasurable ((hgc.comp (continuous_apply i)).aestronglyMeasurable)
    simp only [e]
    have e2 : ∀ ω', ∫ x, g x ∂(empirical (X u.toNNReal ω')) =
        (N : ℝ)⁻¹ * ∑ i, g (X u.toNNReal ω' i) := fun ω' => pair_empirical hN0 _ g
    simp only [e2]
    rw [integral_const_mul, integral_finsetSum _ (fun i _ => hbdd i)]
  have hint : Integrable (fun ω' => pair (empirical (X u.toNNReal ω')) g) P := by
    have : (fun ω' => pair (empirical (X u.toNNReal ω')) g) =
        fun ω' => (N : ℝ)⁻¹ * ∑ i, g (X u.toNNReal ω' i) := funext fun ω' => pair_empirical hN0 _ g
    rw [this]
    exact (integrable_finsetSum _ (fun i _ => hbdd i)).const_mul _
  rw [h1, hmean]
  unfold flucPair
  rw [integral_sub hint (integrable_const _)]
  simp

/-- An Itô integral of an integrand vanishing outside `[0,τ]` is constant after `τ`. -/
theorem S7PIF4_mart_const {Ω : Type*} {mΩ : MeasurableSpace Ω} {ι : Type*} [Fintype ι] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → ι → ℝ}
    (hW : IsBrownianFiltration P ℱ W') {Φ : ℝ → Ω → ι → ℝ} (hΦ : IsProgressiveL2 P ℱ Φ) {τ : ℝ}
    (hτ : 0 ≤ τ) (hzero : ∀ s ω k, s ∉ Set.Icc 0 τ → Φ s ω k = 0) :
    ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → itoIntegral P ℱ W' Φ t ω = itoIntegral P ℱ W' Φ (min t τ) ω := by
  classical
  have hU : MeasurableSet[ℱ 0] (Set.univ : Set Ω) := MeasurableSet.univ
  set Φ' : ℝ → Ω → ι → ℝ := fun s ω => Set.indicator (Set.Ioc 0 τ) (fun _ => Φ s ω) s with hΦ'
  have hΦ'eq : Φ' = restrictFun Φ 0 τ Set.univ := by
    funext s ω; simp [hΦ', restrictFun, Set.indicator]
  have hΦ'L2 : IsProgressiveL2 P ℱ Φ' := by
    rw [hΦ'eq]; exact hΦ.restrictFun (b := τ) hU
  have hdiff : ∀ T, sqIntegralOn P (fun s ω => Φ s ω - Φ' s ω) T = 0 := by
    intro T
    unfold sqIntegralOn
    have hz : ∀ s ω, s ≠ 0 → ∀ k, (Φ s ω - Φ' s ω) k = 0 := by
      intro s ω hs k
      by_cases h : s ∈ Set.Ioc 0 τ
      · simp [hΦ', h]
      · have h2 : s ∉ Set.Icc 0 τ := fun hh => h ⟨lt_of_le_of_ne hh.1 (Ne.symm hs), hh.2⟩
        simp [hΦ', h, hzero s ω k h2]
    have hae : ∀ᵐ s ∂(volume : Measure ℝ), s ∉ ({0} : Set ℝ) :=
      (Set.countable_singleton (0 : ℝ)).ae_notMem _
    have : ∀ ω, ∫⁻ s in Set.Icc 0 T, ∑ k, ‖(Φ s ω - Φ' s ω) k‖ₑ ^ 2 = 0 := by
      intro ω
      have : ∀ᵐ s ∂(volume.restrict (Set.Icc 0 T)), ∑ k, ‖(Φ s ω - Φ' s ω) k‖ₑ ^ 2 = 0 := by
        refine ae_restrict_of_ae ?_
        filter_upwards [hae] with s hs
        have hs0 : s ≠ 0 := fun h => hs (by simp [h])
        simp [hz s ω hs0]
      rw [lintegral_congr_ae this]; simp
    simp only [Pi.sub_apply] at this ⊢
    simp [this]
  have h1 := itoIntegral_congr hW hΦ hΦ'L2 hdiff
  have h2 := itoIntegral_indicator_Ioc hW hΦ (a := 0) (b := τ) le_rfl hτ
  filter_upwards [h1, h2] with ω hω1 hω2 t ht
  have := hω2 t
  rw [← hω1 t] at this
  rw [min_eq_right ht, itoIntegral_of_nonpos P ℱ W' Φ le_rfl] at this
  simpa using this

end HRS.MC.Sec7.S7PIF4

end
