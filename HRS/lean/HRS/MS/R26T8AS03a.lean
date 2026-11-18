import Mathlib

/-!
# S8.2 T8A.S03a: a jointly measurable representative of an `L²`-valued measurable map (generic)

For `P` finite and `V : α → Lp ℝ 2 P` essentially strongly measurable, there is a jointly measurable
`G : α → Ω → ℝ` with `G t =ᵐ[P] V t` for almost every `t`.  Route: a countable dense family `u n` in the
(separable) range, measurable representatives `g n` of `u n`, and `G_k t := g (n_k t)` where `n_k t` is the
first index with `dist (V t) (u n) < 2⁻ᵏ`; the `G_k t` are Cauchy in `L²(P)` with summable bounds uniformly
in `t`, so `G := lim G_k` (measurable) works for every `t`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace HRS.MS.R26T8A

section
variable {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]

theorem r26t8a_s03a_core (P : Measure Ω) [IsFiniteMeasure P] (V : α → Lp ℝ 2 P)
    (hV : StronglyMeasurable V) :
    ∃ G : α → Ω → ℝ, Measurable (Function.uncurry G) ∧ ∀ t, G t =ᵐ[P] ⇑(V t) := by
  classical
  have hsep : TopologicalSpace.IsSeparable (Set.range V) := hV.isSeparable_range
  obtain ⟨D, -, hDc, hDd⟩ := hsep.exists_countable_dense_subset
  have hDc' : (insert (0 : Lp ℝ 2 P) D).Countable := hDc.insert 0
  obtain ⟨u, hu⟩ := hDc'.exists_eq_range (Set.insert_nonempty _ _)
  have hex : ∀ (k : ℕ) (t : α), ∃ n, dist (V t) (u n) < (1 / 2 : ℝ) ^ k := by
    intro k t
    have h1 : V t ∈ closure (insert (0 : Lp ℝ 2 P) D) :=
      closure_mono (subset_insert _ _) (hDd ⟨t, rfl⟩)
    rw [Metric.mem_closure_iff] at h1
    obtain ⟨b, hb, hd⟩ := h1 ((1 / 2 : ℝ) ^ k) (by positivity)
    rw [hu] at hb
    obtain ⟨n, rfl⟩ := hb
    exact ⟨n, hd⟩
  let g : ℕ → Ω → ℝ := fun n => (Lp.aestronglyMeasurable (u n)).mk _
  have hg : ∀ n, Measurable (g n) := fun n =>
    (Lp.aestronglyMeasurable (u n)).stronglyMeasurable_mk.measurable
  have hgu : ∀ n, g n =ᵐ[P] ⇑(u n) := fun n => ((Lp.aestronglyMeasurable (u n)).ae_eq_mk).symm
  have hN : ∀ k, Measurable (fun t => Nat.find (hex k t)) := fun k =>
    measurable_find (hex k) (fun n =>
      measurableSet_lt (hV.dist stronglyMeasurable_const).measurable measurable_const)
  let Gk : ℕ → α → Ω → ℝ := fun k t ω => g (Nat.find (hex k t)) ω
  have hGk : ∀ k, Measurable (Function.uncurry (Gk k)) := fun k => by
    have h1 : Measurable (fun p : ℕ × Ω => g p.1 p.2) :=
      measurable_from_prod_countable_right (fun n => hg n)
    exact h1.comp (((hN k).comp measurable_fst).prodMk measurable_snd)
  have hGkt : ∀ k t, Measurable (Gk k t) := fun k t => by
    have := (hGk k).comp (measurable_prodMk_left (x := t))
    exact this
  have hbd : ∀ k t, eLpNorm (Gk k t - ⇑(V t)) 2 P ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
    intro k t
    have h := Nat.find_spec (hex k t)
    set n := Nat.find (hex k t) with hn
    calc eLpNorm (Gk k t - ⇑(V t)) 2 P = eLpNorm (⇑(u n) - ⇑(V t)) 2 P :=
          eLpNorm_congr_ae ((hgu n).sub EventuallyEq.rfl)
      _ = ‖u n - V t‖ₑ := by
          rw [Lp.enorm_def]; exact eLpNorm_congr_ae (Lp.coeFn_sub _ _).symm
      _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
          rw [← ofReal_norm, ← dist_eq_norm, dist_comm]
          exact ENNReal.ofReal_le_ofReal h.le
  have hpow : ∀ k N : ℕ, N ≤ k → (1 / 2 : ℝ) ^ k ≤ (1 / 2 : ℝ) ^ N := fun k N h =>
    pow_le_pow_of_le_one (by norm_num) (by norm_num) h
  have hBsum : ∑' N : ℕ, ENNReal.ofReal (3 * (1 / 2 : ℝ) ^ N) ≠ ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun N => by positivity)
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 3)]
    exact ENNReal.ofReal_ne_top
  have hcau : ∀ t, ∀ N n m : ℕ, N ≤ n → N ≤ m →
      eLpNorm (Gk n t - Gk m t) 2 P < ENNReal.ofReal (3 * (1 / 2 : ℝ) ^ N) := by
    intro t N n m hn hm
    have h1 : Gk n t - Gk m t = (Gk n t - ⇑(V t)) - (Gk m t - ⇑(V t)) := by
      ext ω; simp
    rw [h1]
    refine lt_of_le_of_lt (eLpNorm_sub_le (by norm_num)) ?_
    have h2 := hbd n t
    have h3 := hbd m t
    calc eLpNorm (Gk n t - ⇑(V t)) 2 P + eLpNorm (Gk m t - ⇑(V t)) 2 P
        ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ n) + ENNReal.ofReal ((1 / 2 : ℝ) ^ m) := add_le_add h2 h3
      _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ n + (1 / 2 : ℝ) ^ m) :=
          (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ < ENNReal.ofReal (3 * (1 / 2 : ℝ) ^ N) := by
          rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
          have := hpow n N hn
          have := hpow m N hm
          have : (0 : ℝ) < (1 / 2 : ℝ) ^ N := by positivity
          linarith
  refine ⟨fun t ω => limUnder atTop (fun k => Gk k t ω), ?_, ?_⟩
  · have : StronglyMeasurable (fun p : α × Ω => limUnder atTop (fun k => Gk k p.1 p.2)) :=
      StronglyMeasurable.limUnder (fun k => (hGk k).stronglyMeasurable)
    exact this.measurable
  · intro t
    have hae : ∀ᵐ ω ∂P, ∃ l : ℝ, Tendsto (fun k => Gk k t ω) atTop (𝓝 l) :=
      Lp.ae_tendsto_of_cauchy_eLpNorm (fun k => (hGkt k t).aestronglyMeasurable)
        (by norm_num) hBsum (hcau t)
    have hae' : ∀ᵐ ω ∂P, Tendsto (fun k => Gk k t ω) atTop
        (𝓝 (limUnder atTop (fun k => Gk k t ω))) :=
      hae.mono fun ω ⟨l, hl⟩ => by rw [hl.limUnder_eq]; exact hl
    have hG1 : TendstoInMeasure P (fun k => Gk k t) atTop
        (fun ω => limUnder atTop (fun k => Gk k t ω)) :=
      tendstoInMeasure_of_tendsto_ae (fun k => (hGkt k t).aestronglyMeasurable) hae'
    have hG2 : TendstoInMeasure P (fun k => Gk k t) atTop ⇑(V t) := by
      refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) ?_
      have h0 : Tendsto (fun k : ℕ => ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) atTop (𝓝 0) := by
        have := ENNReal.tendsto_ofReal
          (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num))
        simpa using this
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0
        (fun _ => zero_le) (fun k => hbd k t)
    exact tendstoInMeasure_ae_unique hG1 hG2

/-- A jointly measurable representative of an essentially strongly measurable `L²`-valued map:
`G` is jointly measurable and `G t` represents `V t` for almost every `t`. -/
theorem r26t8a_s03a_joint_rep (μ : Measure α) (P : Measure Ω) [IsFiniteMeasure P]
    (V : α → Lp ℝ 2 P) (hV : AEStronglyMeasurable V μ) :
    ∃ G : α → Ω → ℝ, Measurable (Function.uncurry G) ∧ ∀ᵐ t ∂μ, G t =ᵐ[P] ⇑(V t) := by
  obtain ⟨G, hG, hGt⟩ := r26t8a_s03a_core P hV.mk hV.stronglyMeasurable_mk
  refine ⟨G, hG, ?_⟩
  filter_upwards [hV.ae_eq_mk] with t ht
  rw [ht]
  exact hGt t

end

end HRS.MS.R26T8A

end
