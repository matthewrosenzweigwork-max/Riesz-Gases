import HRS.MC.CepaDefs
import HRS.Stochastic.Filtration

/-!
# Packet CEPE6A, file 1: a fast-Cauchy sequence of adapted continuous paths has an adapted continuous limit

Generic lemma: if `Y j` are continuous (in `t`) adapted paths in `Ch N` such that off a null measurable set
`Gᶜ`, for every horizon `T` eventually in `l` `‖Y (l+1) t - Y l t‖ ≤ 2⁻ˡ` on `[0,T]`, then there is a
(everywhere) continuous `ℱ`-adapted `Zl` with `Y j → Zl` uniformly on every `[0,T]`, for `ω ∈ G`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MC.CepE6A

open HRS HRS.MC.Cepa

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

/-- Pointwise geometric Cauchy estimate. -/
theorem e6a_geom_limit {y : ℕ → Ch N} {J : ℕ} (h : ∀ l, J ≤ l → ‖y (l + 1) - y l‖ ≤ (1 / 2 : ℝ) ^ l) :
    ∃ a : Ch N, Tendsto y atTop (𝓝 a) ∧ ∀ m, J ≤ m → ‖y m - a‖ ≤ 2 * (1 / 2 : ℝ) ^ m := by
  have key : ∀ m, J ≤ m → ∃ a : Ch N, Tendsto (fun n => y (n + m)) atTop (𝓝 a) ∧
      ∀ n, dist (y (n + m)) a ≤ 2 * (1 / 2 : ℝ) ^ m := by
    intro m hm
    have hu : ∀ n, dist (y (n + m)) (y (n + 1 + m)) ≤ (2 * (1 / 2 : ℝ) ^ m) / 2 / 2 ^ n := by
      intro n
      have h1 := h (n + m) (by omega)
      rw [dist_comm, dist_eq_norm]
      have e : y (n + 1 + m) = y (n + m + 1) := by congr 1; omega
      rw [e]
      refine h1.trans (le_of_eq ?_)
      rw [pow_add]
      field_simp
      rw [← mul_pow]
      norm_num
    obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric_two hu)
    refine ⟨a, ha, fun n => ?_⟩
    have := dist_le_of_le_geometric_two_of_tendsto hu ha n
    refine this.trans ?_
    have h2n : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    have hp : 0 ≤ 2 * (1 / 2 : ℝ) ^ m := by positivity
    exact div_le_self hp h2n
  obtain ⟨a, ha, hb⟩ := key J le_rfl
  refine ⟨a, (tendsto_add_atTop_iff_nat J).1 ha, fun m hm => ?_⟩
  obtain ⟨a', ha', hb'⟩ := key m hm
  have : a' = a := by
    have h2 := (tendsto_add_atTop_iff_nat m).1 ha'
    have h3 := (tendsto_add_atTop_iff_nat J).1 ha
    exact tendsto_nhds_unique h2 h3
  subst this
  have := hb' 0
  simpa [dist_eq_norm] using this

/-- Uniform convergence plus continuity of the pieces gives continuity of the limit. -/
theorem e6a_exists_limit {ℱ : Filtration ℝ mΩ} (hℱ : IsCompleteFiltration P ℱ)
    {Y : ℕ → ℝ → Ω → Ch N} (hYc : ∀ j ω, Continuous fun t => Y j t ω)
    (hYm : ∀ j t, 0 ≤ t → Measurable[ℱ t] (Y j t))
    {G : Set Ω} (hGm : MeasurableSet G) (hG0 : P Gᶜ = 0)
    (hG : ∀ ω ∈ G, ∀ T : ℕ, ∃ J : ℕ, ∀ l, J ≤ l → ∀ t ∈ Icc (0 : ℝ) T,
      ‖Y (l + 1) t ω - Y l t ω‖ ≤ (1 / 2 : ℝ) ^ l) :
    ∃ Zl : ℝ → Ω → Ch N, (∀ ω, Continuous fun t => Zl t ω) ∧ (∀ t, 0 ≤ t → Measurable[ℱ t] (Zl t)) ∧
      ∀ ω ∈ G, ∀ T : ℕ, TendstoUniformlyOn (fun j t => Y j t ω) (fun t => Zl t ω) atTop (Icc (0 : ℝ) T) := by
  classical
  let L : ℝ → Ω → Ch N := fun t ω => limUnder atTop (fun j => Y j t ω)
  let Zl : ℝ → Ω → Ch N := fun t ω => if ω ∈ G then L (max t 0) ω else 0
  -- pointwise facts on `G`
  have hpt : ∀ ω ∈ G, ∀ T : ℕ, ∃ J : ℕ, ∀ t ∈ Icc (0 : ℝ) T, Tendsto (fun j => Y j t ω) atTop (𝓝 (L t ω)) ∧
      ∀ m, J ≤ m → ‖Y m t ω - L t ω‖ ≤ 2 * (1 / 2 : ℝ) ^ m := by
    intro ω hω T
    obtain ⟨J, hJ⟩ := hG ω hω T
    refine ⟨J, fun t ht => ?_⟩
    obtain ⟨a, ha, hb⟩ := e6a_geom_limit (y := fun j => Y j t ω) (J := J) (fun l hl => hJ l hl t ht)
    have : L t ω = a := ha.limUnder_eq
    rw [this]
    exact ⟨ha, hb⟩
  have hunif : ∀ ω ∈ G, ∀ T : ℕ, TendstoUniformlyOn (fun j t => Y j t ω) (fun t => L t ω) atTop (Icc (0 : ℝ) T) := by
    intro ω hω T
    obtain ⟨J, hJ⟩ := hpt ω hω T
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have h0 : Tendsto (fun m : ℕ => 2 * (1 / 2 : ℝ) ^ m) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul 2
    filter_upwards [eventually_ge_atTop J, h0.eventually (gt_mem_nhds hε)] with m hm hm2 t ht
    rw [dist_comm, dist_eq_norm]
    exact lt_of_le_of_lt ((hJ t ht).2 m hm) hm2
  have hLcont : ∀ ω ∈ G, ∀ T : ℕ, ContinuousOn (fun t => L t ω) (Icc (0 : ℝ) T) := by
    intro ω hω T
    exact (hunif ω hω T).continuousOn (Eventually.of_forall fun j => (hYc j ω).continuousOn).frequently
  refine ⟨Zl, ?_, ?_, ?_⟩
  · intro ω
    by_cases hω : ω ∈ G
    · have e : (fun t => Zl t ω) = fun t => L (max t 0) ω := by
        funext t; simp [Zl, hω]
      rw [e, continuous_iff_continuousAt]
      intro t0
      obtain ⟨T, hT⟩ := exists_nat_gt (|t0| + 1)
      have hcont : Continuous fun t : ℝ => L (min (max t 0) T) ω := by
        refine (hLcont ω hω T).comp_continuous ((continuous_id.max continuous_const).min continuous_const) ?_
        intro t
        exact ⟨le_min (le_max_right _ _) (by positivity), min_le_right _ _⟩
      have hev : (fun t : ℝ => L (min (max t 0) T) ω) =ᶠ[𝓝 t0] fun t => L (max t 0) ω := by
        have : Iio (T : ℝ) ∈ 𝓝 t0 := Iio_mem_nhds (by linarith [le_abs_self t0])
        filter_upwards [this] with t ht
        have : max t 0 ≤ T := max_le (le_of_lt ht) (by positivity)
        simp [min_eq_left this]
      exact (hcont.continuousAt).congr hev
    · have e : (fun t => Zl t ω) = fun _ => (0 : Ch N) := by
        funext t; simp [Zl, hω]
      rw [e]; exact continuous_const
  · intro t ht
    -- the `ℱ t`-measurable limit
    have hY' : ∀ j, StronglyMeasurable[ℱ t] (Y j t) := fun j => (hYm j t ht).stronglyMeasurable
    have hlim : StronglyMeasurable[ℱ t] (fun ω => limUnder atTop (fun j => Y j t ω)) := by
      letI : MeasurableSpace Ω := ℱ t
      exact StronglyMeasurable.limUnder hY'
    have hlimM : Measurable (fun ω => limUnder atTop (fun j => Y j t ω)) :=
      hlim.measurable.mono (ℱ.le t) le_rfl
    have hZm : Measurable (Zl t) := by
      have e : Zl t = fun ω => if ω ∈ G then limUnder atTop (fun j => Y j t ω) else 0 := by
        funext ω; simp [Zl, L, max_eq_left ht]
      rw [e]
      exact Measurable.ite hGm hlimM measurable_const
    refine hℱ.measurable_of_ae_eq t hlim.measurable hZm ?_
    have : ∀ᵐ ω ∂P, ω ∈ G := by
      rw [ae_iff]; exact hG0
    filter_upwards [this] with ω hω
    simp [Zl, L, hω, max_eq_left ht]
  · intro ω hω T
    refine (hunif ω hω T).congr_right fun t ht => ?_
    simp [Zl, hω, max_eq_left ht.1]

end HRS.MC.CepE6A
