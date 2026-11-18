import HRS.MC.CepH2Core1
import HRS.MC.CepH2Fish3

/-!
# CEPH2, C6 (b): extended-real bookkeeping for the passage to the limit
-/

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

theorem h2_cylEntropy_ne_bot {U : Ch N → ℝ} {θ : ℝ} (μ : Measure (Ch N)) : cep_cylEntropy θ U μ ≠ ⊥ := by
  unfold cep_cylEntropy
  intro h
  rw [sub_eq_add_neg] at h
  have h1 : ((relEntropy μ (cep_cylRef θ U) : ℝ≥0∞) : EReal) = ⊥ ∨
      -((Real.log (cep_cylPartition θ U).toReal : ℝ) : EReal) = ⊥ := by
    by_contra hh
    push_neg at hh
    exact (EReal.add_ne_bot_iff.2 ⟨hh.1, hh.2⟩) h
  rcases h1 with h1 | h1
  · exact absurd h1 (EReal.coe_ennreal_ne_bot _)
  · rw [← EReal.coe_neg] at h1
    exact absurd h1 (EReal.coe_ne_bot _)

theorem h2_cylEntropy_real {U : Ch N → ℝ} {θ : ℝ} {μ : Measure (Ch N)} (h : cep_cylEntropy θ U μ < ⊤) :
    ∃ H : ℝ, cep_cylEntropy θ U μ = (H : EReal) := by
  have hrel := h2_relEntropy_ne_top h
  unfold cep_cylEntropy
  refine ⟨(relEntropy μ (cep_cylRef θ U)).toReal - Real.log (cep_cylPartition θ U).toReal, ?_⟩
  rw [EReal.coe_sub, EReal.coe_ennreal_toReal hrel]

theorem h2_liminf_add_le {a Y E : ℕ → ℝ} {H0 : ℝ} (hE : Tendsto E atTop (𝓝 0))
    (h : ∀ k, a k + Y k ≤ H0 + E k) :
    liminf (fun k => (a k : EReal)) atTop + liminf (fun k => (Y k : EReal)) atTop ≤ (H0 : EReal) := by
  calc liminf (fun k => (a k : EReal)) atTop + liminf (fun k => (Y k : EReal)) atTop
      ≤ liminf (fun k => (a k : EReal) + (Y k : EReal)) atTop := EReal.le_liminf_add
    _ ≤ liminf (fun k => ((H0 + E k : ℝ) : EReal)) atTop := by
        refine liminf_le_liminf (Eventually.of_forall fun k => ?_)
        rw [← EReal.coe_add]
        exact EReal.coe_le_coe_iff.2 (h k)
    _ = (H0 : EReal) := by
        refine Tendsto.liminf_eq ?_
        have h1 : Tendsto (fun k => H0 + E k) atTop (𝓝 H0) := by simpa using hE.const_add H0
        exact (continuous_coe_real_ereal.tendsto _).comp h1

/-- From `H + θ(1-δ) J ≤ H₀` for all `δ ∈ (0,1)` to `H + θ J ≤ H₀`. -/
theorem h2_delta_limit {θ : ℝ} (hθ : 0 < θ) {Hm : EReal} (hbot : Hm ≠ ⊥) {H0 : ℝ} {Jd : ℝ≥0∞}
    (h : ∀ δ : ℝ, 0 < δ → δ < 1 → Hm + ((ENNReal.ofReal (θ * (1 - δ)) * Jd : ℝ≥0∞) : EReal) ≤ (H0 : EReal)) :
    Hm + ((ENNReal.ofReal θ * Jd : ℝ≥0∞) : EReal) ≤ (H0 : EReal) := by
  have h12 := h (1 / 2) (by norm_num) (by norm_num)
  have hJ : Jd ≠ ⊤ := by
    intro hJ
    rw [hJ, ENNReal.mul_top (by simpa using (by positivity : 0 < θ * (1 - 1 / 2)))] at h12
    simp only [EReal.coe_ennreal_top] at h12
    rw [EReal.add_top_of_ne_bot hbot] at h12
    exact absurd (top_le_iff.1 h12) (EReal.coe_ne_top _)
  have hHtop : Hm ≠ ⊤ := by
    intro hH
    rw [hH, EReal.top_add_of_ne_bot (EReal.coe_ennreal_ne_bot _)] at h12
    exact absurd (top_le_iff.1 h12) (EReal.coe_ne_top _)
  lift Hm to ℝ using ⟨hHtop, hbot⟩
  set Jr : ℝ := Jd.toReal with hJr
  have e : ∀ c : ℝ, 0 ≤ c → ((ENNReal.ofReal c * Jd : ℝ≥0∞) : EReal) = ((c * Jr : ℝ) : EReal) := by
    intro c hc
    rw [show ENNReal.ofReal c * Jd = ENNReal.ofReal (c * Jr) by
      rw [ENNReal.ofReal_mul hc, hJr, ENNReal.ofReal_toReal hJ]]
    rw [EReal.coe_ennreal_ofReal, max_eq_left (mul_nonneg hc ENNReal.toReal_nonneg)]
  have hJr0 : 0 ≤ Jr := ENNReal.toReal_nonneg
  rw [e θ hθ.le]
  rw [← EReal.coe_add, EReal.coe_le_coe_iff]
  have hlim : Tendsto (fun δ : ℝ => Hm + θ * (1 - δ) * Jr) (𝓝[>] 0) (𝓝 (Hm + θ * (1 - 0) * Jr)) := by
    have : Continuous fun δ : ℝ => Hm + θ * (1 - δ) * Jr := by fun_prop
    exact tendsto_nhdsWithin_of_tendsto_nhds (this.tendsto 0)
  have hle : ∀ᶠ δ in 𝓝[>] (0 : ℝ), Hm + θ * (1 - δ) * Jr ≤ H0 := by
    have : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT (by norm_num)
    filter_upwards [this] with δ hδ
    have := h δ hδ.1 hδ.2
    rw [e _ (mul_nonneg hθ.le (by linarith [hδ.2])), ← EReal.coe_add, EReal.coe_le_coe_iff] at this
    exact this
  have := le_of_tendsto hlim hle
  simpa using this

end HRS.MC.CepH2
