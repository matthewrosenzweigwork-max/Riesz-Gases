import HRS.ME.Stat417
import HRS.Stochastic.LyonsZhengSpec

/-!
# Chunk E, row 4.17, packet M4c: Minkowski for countable sums and measurability of path integrals

* `lintegral_sq_tsum_le`: Minkowski's inequality in `L²` for a countable sum of nonnegative functions
  (finite Minkowski by induction, then monotone convergence over the finite partial sums).
* `pathIntegral_aemeasurable`: the path integral `ω ↦ ∫_0^b γ(b-r) R(X^r ω) dr` is a.e. measurable.
  The path is replaced, off a null set, by a jointly measurable modification `Xs` (as in
  `stationary_weighted_integral_proof`), and `γ` by `γ' r := γ (max 0 (min b r))`, which is continuous
  and agrees with `γ` on `[0, b]`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.ME

variable {d : ℕ}

open HRS HRS.LZ

/-- Minkowski's inequality in `L²` for a countable sum of nonnegative (a.e. measurable) functions. -/
theorem lintegral_sq_tsum_le {α : Type*} [MeasurableSpace α] (μ : Measure α) {ι : Type*} [Countable ι]
    (f : ι → α → ℝ≥0∞) (hf : ∀ i, AEMeasurable (f i) μ) :
    (∫⁻ x, (∑' i, f i x) ^ 2 ∂μ) ^ (1 / 2 : ℝ) ≤ ∑' i, (∫⁻ x, (f i x) ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  classical
  -- (1) finite Minkowski inequality, by induction on the finite index set
  have hfin : ∀ s : Finset ι, (∫⁻ x, (∑ i ∈ s, f i x) ^ 2 ∂μ) ^ (1 / 2 : ℝ) ≤
      ∑ i ∈ s, (∫⁻ x, (f i x) ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro j s hj ih
      have hg : AEMeasurable (∑ i ∈ s, f i) μ := Finset.aemeasurable_sum s (fun i _ => hf i)
      have hmink := ENNReal.lintegral_Lp_add_le (μ := μ) (p := 2) (hf j) hg (by norm_num)
      simp only [ENNReal.rpow_two, Pi.add_apply, Finset.sum_apply] at hmink
      simp only [Finset.sum_insert hj]
      exact hmink.trans (add_le_add le_rfl ih)
  -- (2) the common bound `M`
  set M : ℝ≥0∞ := ∑' i, (∫⁻ x, (f i x) ^ 2 ∂μ) ^ (1 / 2 : ℝ) with hM
  have hsq : ∀ A : ℝ≥0∞, (A ^ (1 / 2 : ℝ)) ^ 2 = A := by
    intro A
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hpart : ∀ s : Finset ι, ∫⁻ x, (∑ i ∈ s, f i x) ^ 2 ∂μ ≤ M ^ 2 := by
    intro s
    have h1 : (∫⁻ x, (∑ i ∈ s, f i x) ^ 2 ∂μ) ^ (1 / 2 : ℝ) ≤ M :=
      (hfin s).trans (ENNReal.sum_le_tsum s)
    calc ∫⁻ x, (∑ i ∈ s, f i x) ^ 2 ∂μ
        = ((∫⁻ x, (∑ i ∈ s, f i x) ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := (hsq _).symm
      _ ≤ M ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
  -- (3) monotone convergence over the finite partial sums
  have hpt : ∀ x, (∑' i, f i x) ^ 2 = ⨆ s : Finset ι, (∑ i ∈ s, f i x) ^ 2 := by
    intro x
    rw [ENNReal.tsum_eq_iSup_sum, ENNReal.iSup_pow]
  have hdir : Directed (· ≤ ·) (fun s : Finset ι => fun x => (∑ i ∈ s, f i x) ^ 2) := by
    intro s t
    refine ⟨s ∪ t, ?_, ?_⟩
    · intro x
      exact pow_le_pow_left₀ (by positivity) (Finset.sum_le_sum_of_subset Finset.subset_union_left) 2
    · intro x
      exact pow_le_pow_left₀ (by positivity) (Finset.sum_le_sum_of_subset Finset.subset_union_right) 2
  have hmeas : ∀ s : Finset ι, AEMeasurable (fun x => (∑ i ∈ s, f i x) ^ 2) μ := by
    intro s
    have h : AEMeasurable (∑ i ∈ s, f i) μ := Finset.aemeasurable_sum s (fun i _ => hf i)
    simpa only [Finset.sum_apply] using h.pow_const 2
  have hint : ∫⁻ x, (∑' i, f i x) ^ 2 ∂μ ≤ M ^ 2 := by
    have e : ∫⁻ x, (∑' i, f i x) ^ 2 ∂μ = ∫⁻ x, ⨆ s : Finset ι, (∑ i ∈ s, f i x) ^ 2 ∂μ :=
      lintegral_congr (fun x => hpt x)
    rw [e]
    exact (lintegral_iSup_directed hmeas hdir).trans_le (iSup_le hpart)
  -- (4) conclusion
  have hfinal : (∫⁻ x, (∑' i, f i x) ^ 2 ∂μ) ^ (1 / 2 : ℝ) ≤ (M ^ 2) ^ (1 / 2 : ℝ) :=
    ENNReal.rpow_le_rpow hint (by norm_num)
  have hM2 : (M ^ 2) ^ (1 / 2 : ℝ) = M := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rw [hM2] at hfinal
  exact hfinal

/-- A jointly measurable modification of the path `r ↦ X r.toNNReal ω`: a measurable map
`(r, ω) ↦ Xs r ω` which, off a `P`-null set of `ω`, equals `X r.toNNReal ω` for all `r` simultaneously. -/
theorem mink4_modification {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {N : ℕ}
    (X : ℝ≥0 → Ω → Config d N) (hcont : ∀ᵐ ω ∂P, ∀ i, Continuous fun t : ℝ≥0 => X t ω i)
    (hadapt : ∀ t : ℝ≥0, Measurable (X t)) :
    ∃ Xs : ℝ → Ω → Config d N, (∀ᵐ ω ∂P, ∀ r : ℝ, Xs r ω = X r.toNNReal ω) ∧
      Measurable (fun p : ℝ × Ω => Xs p.1 p.2) := by
  classical
  haveI : BorelSpace (Torus d) := Pi.borelSpace
  haveI : BorelSpace (Config d N) := Pi.borelSpace
  obtain ⟨Nn, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hcont)
  have hcont_bad : ∀ ω, ω ∉ Nn → ∀ i, Continuous fun t : ℝ≥0 => X t ω i := by
    intro ω hω
    by_contra hne
    exact hω (hNsub hne)
  have hNae : ∀ᵐ ω ∂P, ω ∉ Nn := by
    rw [ae_iff]
    exact measure_mono_null (fun ω hω => not_not.mp hω) hN0
  refine ⟨fun r ω => if ω ∈ Nn then X 0 ω else X r.toNNReal ω,
    hNae.mono fun ω hω r => if_neg hω, ?_⟩
  refine measurable_uncurry_of_continuous_of_measurable (u := fun (r : ℝ) (ω : Ω) =>
    if ω ∈ Nn then X 0 ω else X r.toNNReal ω) (fun ω => ?_) (fun r => ?_)
  · by_cases hω : ω ∈ Nn
    · simp only [if_pos hω]
      exact continuous_const
    · simp only [if_neg hω]
      exact continuous_pi fun i => (hcont_bad ω hω i).comp continuous_real_toNNReal
  · exact Measurable.ite hNm (hadapt 0) (hadapt r.toNNReal)

/-- Measurability of the path integral `ω ↦ ∫_0^b γ(b-r) R(X^r ω) dr` for a stationary Gibbs flow. -/
theorem pathIntegral_aemeasurable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N) (H : ℝ)
    (hflow : IsStationaryGibbsFlow P s hs0 hsd V β hβ H X₀ W X)
    (R : Config d N → ℝ) (hR : Measurable R) (γ : ℝ → ℝ) (b : ℝ) (hb : 0 ≤ b) (hbH : b ≤ H)
    (hγ : ContinuousOn γ (Set.Icc 0 b)) :
    AEMeasurable (fun ω => ∫ r in (0 : ℝ)..b, γ (b - r) * R (X r.toNNReal ω)) P := by
  classical
  haveI : BorelSpace (Torus d) := Pi.borelSpace
  haveI : BorelSpace (Config d N) := Pi.borelSpace
  -- path regularity and adaptedness from the strong solution
  have hcont : ∀ᵐ ω ∂P, ∀ i, Continuous fun t : ℝ≥0 => X t ω i := by
    rcases hflow.flow.flow with hh | ⟨hd1, -⟩
    · exact hh.1.cont
    · omega
  have hadapt : ∀ t : ℝ≥0, Measurable (X t) := by
    rcases hflow.flow.flow with hh | ⟨hd1, -⟩
    · exact hh.1.adapted
    · omega
  obtain ⟨Xs, hXs_good, hXs_meas⟩ := mink4_modification P X hcont hadapt
  -- continuous extension of `γ` restricted to `[0, b]`
  obtain ⟨γ', hγ'def⟩ : ∃ g : ℝ → ℝ, g = fun r => γ (max 0 (min b r)) := ⟨_, rfl⟩
  have hγ'c : Continuous γ' := by
    rw [hγ'def]
    have hmaps : ∀ r : ℝ, max 0 (min b r) ∈ Set.Icc (0:ℝ) b := fun r =>
      ⟨le_max_left _ _, max_le hb (min_le_left _ _)⟩
    exact hγ.comp_continuous (continuous_const.max (continuous_const.min continuous_id)) hmaps
  -- joint measurability and measurability of the parametric integral
  have hGm : Measurable (fun ω => ∫ r in Set.Ioc (0:ℝ) b, γ' (b - r) * R (Xs r ω)) := by
    have hmeasG : Measurable (fun p : ℝ × Ω => γ' (b - p.1) * R (Xs p.1 p.2)) :=
      (hγ'c.measurable.comp (measurable_const.sub measurable_fst)).mul (hR.comp hXs_meas)
    exact (hmeasG.stronglyMeasurable.integral_prod_left').measurable
  refine hGm.aemeasurable.congr ?_
  filter_upwards [hXs_good] with ω hω
  show ∫ r in Set.Ioc (0:ℝ) b, γ' (b - r) * R (Xs r ω) =
    ∫ r in (0:ℝ)..b, γ (b - r) * R (X r.toNNReal ω)
  rw [intervalIntegral.integral_of_le hb]
  refine setIntegral_congr_fun measurableSet_Ioc (fun r hr => ?_)
  have h1 : 0 ≤ b - r := by linarith [hr.2]
  have h2 : b - r ≤ b := by linarith [hr.1]
  have hγeq : γ' (b - r) = γ (b - r) := by
    simp only [hγ'def, min_eq_right h2, max_eq_right h1]
  simp only [hγeq, hω r]

end HRS.ME

end
