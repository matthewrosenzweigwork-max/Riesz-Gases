import HRS.PDE.TorusFPEntropyClassical
import HRS.Appendix.B15BAux1

/-!
# D3-b, Aux1: narrow stability of weak solutions, parametric narrow continuity, Fisher lower semicontinuity

Helpers of packet D3B (names `d3b_*`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS

variable {n : ℕ}

/-- Duality: `∫ ψ dν_τ = ∫ g dν_0` for every weak solution `ν`, with one continuous `g` (the value at time `0`
of the classical backward solution with terminal datum `ψ`). -/
theorem d3b_dual (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
    {T : ℝ} {τ : ℝ} (hτ : τ ∈ Set.Icc 0 T) (hτpos : 0 < τ) {ψ : Torus n → ℝ} (hψ : Torus.IsSmooth ψ) :
    ∃ g : Torus n → ℝ, Continuous g ∧ ∀ ν : ℝ → Measure (Torus n),
      D1WeakSolution κ (d1_gradDrift U) T ν → ∫ x, ψ x ∂(ν τ) = ∫ x, g x ∂(ν 0) := by
  obtain ⟨f, hf⟩ := d1_backward_classical hn hκ hU hτpos hψ
  refine ⟨f 0, d3a_continuous_of_ck1 (d3a_ck2_ck1 (hf.c2 0 ⟨le_rfl, hτpos.le⟩)), fun ν hν => ?_⟩
  have e1 := hν.eqT τ hτ f _ hf.isC12Test
  have hz : ∀ s : ℝ, ∫ x, (-(d1_gen κ (d1_gradDrift U) (f s) x) +
      d1_gen κ (d1_gradDrift U) (f s) x) ∂(ν s) = 0 := by
    intro s; simp
  simp only [hz, integral_zero, add_zero] at e1
  rw [hf.terminal] at e1
  exact e1

theorem d3b_int_close {ν : Measure (Torus n)} [IsProbabilityMeasure ν] {f g : Torus n → ℝ}
    (hf : Continuous f) (hg : Continuous g) {ε : ℝ} (h : ∀ x, |f x - g x| ≤ ε) :
    |∫ x, f x ∂ν - ∫ x, g x ∂ν| ≤ ε := by
  rw [← integral_sub (d3a_hint ν hf) (d3a_hint ν hg)]
  have := norm_integral_le_of_norm_le_const (μ := ν) (f := fun x => f x - g x) (C := ε)
    (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using h x)
  simpa [Real.norm_eq_abs] using this

/-- Narrow stability: if the initial data of weak solutions `μk k` converge narrowly to that of `μ`, so do
the solutions at every time. -/
theorem d3b_stability (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
    {T : ℝ} {μ : ℝ → Measure (Torus n)} {μk : ℕ → ℝ → Measure (Torus n)}
    (hμ : D1WeakSolution κ (d1_gradDrift U) T μ)
    (hμk : ∀ k, D1WeakSolution κ (d1_gradDrift U) T (μk k))
    [IsProbabilityMeasure (μ 0)] [∀ k, IsProbabilityMeasure (μk k 0)]
    (h0 : ∀ φ : Torus n → ℝ, Continuous φ →
      Tendsto (fun k => ∫ x, φ x ∂(μk k 0)) atTop (𝓝 (∫ x, φ x ∂(μ 0)))) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ φ : Torus n → ℝ, Continuous φ →
      Tendsto (fun k => ∫ x, φ x ∂(μk k t)) atTop (𝓝 (∫ x, φ x ∂(μ t))) := by
  intro t ht φ hφ
  rcases ht.1.eq_or_lt with rfl | htpos
  · exact h0 φ hφ
  have hpt : IsProbabilityMeasure (μ t) := d1_isProbabilityMeasure hμ ht
  have hpk : ∀ k, IsProbabilityMeasure (μk k t) := fun k => d1_isProbabilityMeasure (hμk k) ht
  have key : ∀ ψ : Torus n → ℝ, Torus.IsSmooth ψ →
      Tendsto (fun k => ∫ x, ψ x ∂(μk k t)) atTop (𝓝 (∫ x, ψ x ∂(μ t))) := by
    intro ψ hψ
    obtain ⟨g, hgc, hg⟩ := d3b_dual hn hκ hU ht htpos hψ
    rw [hg μ hμ]
    simp_rw [hg _ (hμk _)]
    exact h0 g hgc
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨ψ, hψ, hψφ⟩ := d1_exists_smooth_approx hφ (show 0 < ε / 4 by positivity)
  have hψc : Continuous ψ := d1c_continuous_of_isSmooth hψ
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (key ψ hψ) (ε / 2) (by positivity)
  refine ⟨N, fun k hk => ?_⟩
  have h1 := hN k hk
  rw [Real.dist_eq] at h1 ⊢
  have e1 := d3b_int_close (ν := μk k t) hφ hψc hψφ
  have e2' := d3b_int_close (ν := μ t) hψc hφ (fun x => by rw [abs_sub_comm]; exact hψφ x)
  obtain ⟨a1, a2⟩ := abs_le.1 e1
  obtain ⟨b1, b2⟩ := abs_lt.1 h1
  obtain ⟨c1, c2⟩ := abs_le.1 e2'
  rw [abs_lt]
  constructor <;> linarith

/-- Parametric narrow continuity: if `r ↦ μ r` is narrowly continuous on `[0,T]` (probability measures) and `G`
is jointly continuous on `[0,T] × 𝕋ⁿ`, then `r ↦ ∫ G r dμ_r` is continuous on `[0,T]`. -/
theorem d3b_contOn_param {T : ℝ} {μ : ℝ → Measure (Torus n)}
    (hprob : ∀ t ∈ Set.Icc (0 : ℝ) T, IsProbabilityMeasure (μ t))
    (hnarrow : ∀ φ : Torus n → ℝ, Continuous φ →
      ContinuousOn (fun t => ∫ x, φ x ∂(μ t)) (Set.Icc 0 T))
    {G : ℝ → Torus n → ℝ} (hG : Continuous fun p : Set.Icc (0 : ℝ) T × Torus n => G p.1 p.2) :
    ContinuousOn (fun r => ∫ x, G r x ∂(μ r)) (Set.Icc 0 T) := by
  intro r0 hr0
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have huc := CompactSpace.uniformContinuous_of_continuous hG
  obtain ⟨δ1, hδ1, hu⟩ := Metric.uniformContinuous_iff.1 huc (ε / 2) (by positivity)
  have hn0 := hnarrow (G r0) (d3a_contOn_space hG hr0) r0 hr0
  rw [Metric.continuousWithinAt_iff] at hn0
  obtain ⟨δ2, hδ2, hn2⟩ := hn0 (ε / 2) (by positivity)
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun r hr hd => ?_⟩
  haveI := hprob r hr
  haveI := hprob r0 hr0
  have hd1 : dist r r0 < δ1 := lt_of_lt_of_le hd (min_le_left _ _)
  have hd2 : dist r r0 < δ2 := lt_of_lt_of_le hd (min_le_right _ _)
  have hclose : ∀ x, |G r x - G r0 x| ≤ ε / 2 := by
    intro x
    have := hu (a := (⟨r, hr⟩, x)) (b := (⟨r0, hr0⟩, x)) (by
      rw [Prod.dist_eq, Subtype.dist_eq, dist_self]
      simpa using hd1)
    simpa [Real.dist_eq] using this.le
  have e1 := d3b_int_close (ν := μ r) (d3a_contOn_space hG hr) (d3a_contOn_space hG hr0) hclose
  have e2 := hn2 hr hd2
  rw [Real.dist_eq] at e2 ⊢
  have : ∫ x, G r x ∂(μ r) - ∫ x, G r0 x ∂(μ r0) =
      (∫ x, G r x ∂(μ r) - ∫ x, G r0 x ∂(μ r)) + (∫ x, G r0 x ∂(μ r) - ∫ x, G r0 x ∂(μ r0)) := by ring
  rw [this]
  exact lt_of_le_of_lt (abs_add_le _ _) (by linarith)

theorem d3b_tilt_ck1 {κ : ℝ} {U ψ : Torus n → ℝ} (hU : Torus.IsCk 1 U) (hψ : Torus.IsCk 1 ψ) :
    Torus.IsCk 1 (d3_tiltPot κ U ψ) := by
  unfold Torus.IsCk Torus.lift d3_tiltPot at *
  exact hU.sub (contDiff_const.mul hψ)

theorem d3b_continuous_div {ζ : Torus n → Euc n} (hζ : Torus.IsCk 1 ζ) : Continuous (Torus.div ζ) := by
  have : Torus.div ζ = fun x => ∑ j, (Torus.grad (fun y => (ζ y).ofLp j) x).ofLp j := by
    funext x; rw [d3a_div_eq hζ]
    exact Finset.sum_congr rfl fun j _ => (d1c_grad_component x j).symm
  rw [this]
  exact continuous_finset_sum _ fun j _ =>
    (EuclideanSpace.proj j : Euc n →L[ℝ] ℝ).continuous.comp
      (d3a_continuous_grad_ck1 (d3a_comp_ck hζ j))

/-- Lower semicontinuity of the Fisher information along narrowly convergent probability measures. -/
theorem d3b_fisher_lsc {κ : ℝ} {V : Torus n → ℝ} (hV : Torus.IsCk 1 V) {P : Measure (Torus n)}
    {Pn : ℕ → Measure (Torus n)} [IsProbabilityMeasure P] [∀ k, IsProbabilityMeasure (Pn k)]
    (h : ∀ φ : Torus n → ℝ, Continuous φ →
      Tendsto (fun k => ∫ x, φ x ∂(Pn k)) atTop (𝓝 (∫ x, φ x ∂P))) :
    d1_fisherInfo κ V P ≤ liminf (fun k => d1_fisherInfo κ V (Pn k)) atTop := by
  unfold d1_fisherInfo
  refine iSup₂_le fun ζ hζ => ?_
  set g : Torus n → ℝ := fun x => -2 * Torus.div ζ x + 2 * κ⁻¹ * inner ℝ (ζ x) (Torus.grad V x)
    - ‖ζ x‖ ^ 2 with hg
  have hgc : Continuous g := by
    have hζ1 := d3a_smoothE_ck1 hζ
    exact ((continuous_const.mul (d3b_continuous_div hζ1)).add
      (continuous_const.mul ((d3a_smoothE_cont hζ).inner (d3a_continuous_grad_ck1 hV)))).sub
      ((d3a_smoothE_cont hζ).norm.pow 2)
  have ht : Tendsto (fun k => ENNReal.ofReal (∫ x, g x ∂(Pn k))) atTop
      (𝓝 (ENNReal.ofReal (∫ x, g x ∂P))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp (h g hgc)
  calc ENNReal.ofReal (∫ x, g x ∂P)
      = liminf (fun k => ENNReal.ofReal (∫ x, g x ∂(Pn k))) atTop := ht.liminf_eq.symm
    _ ≤ _ := liminf_le_liminf (Eventually.of_forall fun k =>
        le_iSup₂_of_le ζ hζ le_rfl)

end HRS
