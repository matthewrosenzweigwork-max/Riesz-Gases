import HRS.MS.R2ChaosAux25

/-!
# HRS.MS.R2ChaosAux26 -- measurable-in-time selection of a countable dense family of kernels

Packet S94 (R1, part 2), namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.

For a jointly measurable family `h_t` of envelope-bounded kernels (`t ∈ [0,T]`), the set `{[h_t]} ⊂ L²(μ⊗μ)` is separable;
a countable dense subfamily `h_{τ n}` is extracted, and `kk m t ≤ m` (Borel in `t`) selects an `L²`-nearest member among
the first `m + 1`: `‖h_{τ (kk m t)} - h_t‖₂ → 0` for every `t ∈ [0,T]`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Chaos

open HRS.Whole

variable {d : ℕ}

theorem s94_measurable_eLpNorm {α : Type*} [MeasurableSpace α] {ν : Measure α} [SFinite ν]
    {F : ℝ → α → ℝ} (hF : Measurable fun q : ℝ × α => F q.1 q.2) :
    Measurable fun t : ℝ => eLpNorm (fun x => F t x) 2 ν := by
  have h1 : Measurable fun q : ℝ × α => ‖F q.1 q.2‖ₑ ^ (2 : ℝ) := hF.enorm.pow_const _
  have h2 := h1.lintegral_prod_right'  (ν := ν)
  have e : (fun t : ℝ => eLpNorm (fun x => F t x) 2 ν) =
      fun t => (∫⁻ x, ‖F t x‖ₑ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) := by
    funext t
    have hm : AEStronglyMeasurable (fun x => F t x) ν :=
      (hF.comp (measurable_prodMk_left (x := t))).aestronglyMeasurable
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hm]
    simp
  rw [e]
  exact h2.pow_const _

section Select

variable {s T : ℝ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem s94_select (hT : 0 < T) {h : ℝ → Euc d → Euc d → ℝ}
    (hmeas : Measurable fun q : ℝ × Euc d × Euc d => h q.1 q.2.1 q.2.2)
    (hmem : ∀ t ∈ Set.Icc (0 : ℝ) T,
      MemLp (fun q : Euc d × Euc d => h t q.1 q.2) 2 (μ.prod μ)) :
    ∃ (τ : ℕ → ℝ) (kk : ℕ → ℝ → ℕ), (∀ n, τ n ∈ Set.Icc (0 : ℝ) T) ∧ (∀ m, Measurable (kk m)) ∧
      (∀ m t, kk m t ≤ m) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, Tendsto (fun m => eLpNorm
        (fun q : Euc d × Euc d => h (τ (kk m t)) q.1 q.2 - h t q.1 q.2) 2 (μ.prod μ)) atTop (𝓝 0) := by
  classical
  set ν : Measure (Euc d × Euc d) := μ.prod μ with hν
  let φ : Set.Icc (0 : ℝ) T → Lp ℝ 2 ν := fun t => (hmem t.1 t.2).toLp _
  have hsep : TopologicalSpace.IsSeparable (Set.range φ) :=
    TopologicalSpace.IsSeparable.of_separableSpace _
  obtain ⟨S, hSsub, hSc, hSd⟩ := hsep.exists_countable_dense_subset
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_refl _, hT.le⟩
  have hSne : S.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have := hSd ⟨⟨0, h0⟩, rfl⟩
    rw [hne, closure_empty] at this
    exact this
  obtain ⟨f, hf⟩ := hSc.exists_eq_range hSne
  have hfr : ∀ n, ∃ t : Set.Icc (0 : ℝ) T, φ t = f n := fun n =>
    hSsub (hf ▸ Set.mem_range_self n)
  choose τ' hτ' using hfr
  set τ : ℕ → ℝ := fun n => (τ' n).1 with hτ
  let D : ℕ → ℝ → ℝ≥0∞ := fun n t => eLpNorm (fun q : Euc d × Euc d => h t q.1 q.2 - h (τ n) q.1 q.2) 2 ν
  have hDm : ∀ n, Measurable (D n) := fun n =>
    s94_measurable_eLpNorm (ν := ν) (F := fun t q => h t q.1 q.2 - h (τ n) q.1 q.2)
      (hmeas.sub (hmeas.comp (measurable_const.prodMk measurable_snd)))
  have hDfin : ∀ n, ∀ t ∈ Set.Icc (0 : ℝ) T, D n t ≠ ⊤ := fun n t ht =>
    ((hmem t ht).sub (hmem (τ n) (τ' n).2)).eLpNorm_ne_top
  have hdist : ∀ (t : Set.Icc (0 : ℝ) T) n, dist (φ t) (f n) = (D n t.1).toReal := by
    intro t n
    rw [← hτ' n, dist_eq_norm]
    have e : φ t - φ (τ' n) = ((hmem t.1 t.2).sub (hmem (τ' n).1 (τ' n).2)).toLp _ :=
      (MemLp.toLp_sub _ _).symm
    rw [e, Lp.norm_toLp]
    rfl
  have hdense : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ ε : ℝ≥0∞, 0 < ε → ∃ n, D n t < ε := by
    intro t ht ε hε
    obtain ⟨r, hr0, hr1, hr2⟩ := (ENNReal.lt_iff_exists_real_btwn).1 hε
    have hrpos : 0 < r := by
      by_contra hneg
      have : r = 0 := le_antisymm (not_lt.1 hneg) hr0
      rw [this] at hr1
      simp at hr1
    obtain ⟨b, hb, hbd⟩ := Metric.mem_closure_iff.1 (hSd ⟨⟨t, ht⟩, rfl⟩) r hrpos
    rw [hf] at hb
    obtain ⟨n, rfl⟩ := hb
    refine ⟨n, lt_trans ?_ hr2⟩
    rw [hdist ⟨t, ht⟩ n] at hbd
    rw [← ENNReal.ofReal_toReal (hDfin n t ht)]
    exact (ENNReal.ofReal_lt_ofReal_iff hrpos).2 hbd
  have hex : ∀ m t, ∃ n, n ≤ m ∧ ∀ i, i ≤ m → D n t ≤ D i t := by
    intro m t
    obtain ⟨n, hn, hmin⟩ := Finset.exists_min_image (Finset.range (m + 1)) (fun i => D i t)
      ⟨0, by simp⟩
    exact ⟨n, by simpa [Nat.lt_succ_iff] using hn, fun i hi => hmin i (by simp [hi])⟩
  let kk : ℕ → ℝ → ℕ := fun m t => Nat.find (hex m t)
  have hkk_spec : ∀ m t, kk m t ≤ m ∧ ∀ i, i ≤ m → D (kk m t) t ≤ D i t :=
    fun m t => Nat.find_spec (hex m t)
  have hkk_meas : ∀ m, Measurable (kk m) := by
    intro m
    refine measurable_find (hex m) fun k => ?_
    simp only [Set.setOf_and, Set.setOf_forall]
    exact (MeasurableSet.const _).inter (MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
      measurableSet_le (hDm k) (hDm i))
  refine ⟨τ, kk, fun n => (τ' n).2, hkk_meas, fun m t => (hkk_spec m t).1, fun t ht => ?_⟩
  have e : ∀ m, eLpNorm (fun q : Euc d × Euc d => h (τ (kk m t)) q.1 q.2 - h t q.1 q.2) 2 ν =
      D (kk m t) t := by
    intro m
    have : (fun q : Euc d × Euc d => h (τ (kk m t)) q.1 q.2 - h t q.1 q.2) =
        -(fun q : Euc d × Euc d => h t q.1 q.2 - h (τ (kk m t)) q.1 q.2) := by
      funext q; simp
    rw [this, eLpNorm_neg]
  simp_rw [e]
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  obtain ⟨n0, hn0⟩ := hdense t ht ε hε
  exact Filter.eventually_atTop.2 ⟨n0, fun m hm => ((hkk_spec m t).2 n0 hm).trans hn0.le⟩

end Select

end HRS.MS.R2Chaos
