import HRS.MC.S7UCDefs
import HRS.MC.S7FCH4F

/-!
# Packet ucH, H4c: the limit lemma uniformly in a parameter (sorry-free; imports no sorried module)

`s7_UC_H4_limit_unif_proof`: `S7FCH4_limit` (`S7FCH4F.lean:100`) for families `μ N a`, `ν a`, `m N a` indexed by `a ∈ A`, with
suprema over `a`.  The bound `w + k (1 + 2c + w)(w + e)` of the proof of `S7FCH4_limit` is taken with
`w N := ⨆_a W_{2q}(μ_{N,a}, ν_a) + 1/(N+1)` and `e N := ⨆_a ‖m_{N,a}‖ + N^{-1/2}`, which do not depend on `a`.
Namespace `HRS.MC.Sec7.S7UCH`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7UCH

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.S7FCH4

variable {d : ℕ}

/-- **UC-H4c**, proof. -/
theorem s7_UC_H4_limit_unif_proof {r T : ℝ} (hT : 0 ≤ T) {q : ℝ} (hq : 1 ≤ q) (S : Finset (NonzeroLattice d))
    (K : NonzeroLattice d → FRKernel d) {A : Type*}
    (μ : ℕ → A → Measure (PathSpace d r T)) [∀ N a, IsProbabilityMeasure (μ N a)]
    (ν : A → Measure (PathSpace d r T)) [∀ a, IsProbabilityMeasure (ν a)] (m : ℕ → A → PathSpace d r T)
    {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hμ : ∀ᶠ N : ℕ in atTop, ∀ a, S7FCH4_Lp (2 * q) (μ N a) (fun u => ENNReal.ofReal ‖u‖) ≤ c)
    (hw : Tendsto (fun N : ℕ => ⨆ a, wassersteinE (2 * q) (μ N a) (ν a)) atTop (𝓝 0))
    (hm : Tendsto (fun N : ℕ => ⨆ a, ENNReal.ofReal ‖m N a‖) atTop (𝓝 0))
    (hYi : ∀ᶠ N : ℕ in atTop, ∀ a, Integrable (S7FCH4_Y S K (Real.sqrt N)⁻¹ (m N a)) (μ N a))
    (hY0i : ∀ a, Integrable (S7FCH4_Y S K 0 (0 : PathSpace d r T)) (ν a)) :
    Tendsto (fun N : ℕ => ⨆ a, wassersteinE q
      ((μ N a).map (fun u => (u, S7FCH4_iota hT (S7FCH4_Y S K (Real.sqrt N)⁻¹ (m N a) u -
        ∫ x, S7FCH4_Y S K (Real.sqrt N)⁻¹ (m N a) x ∂(μ N a)))))
      ((ν a).map (fun v => (v, S7FCH4_iota hT (S7FCH4_Y S K 0 (0 : PathSpace d r T) v -
        ∫ x, S7FCH4_Y S K 0 (0 : PathSpace d r T) x ∂(ν a)))))) atTop (𝓝 0) := by
  classical
  have hq0 : 0 < q := by linarith
  have hq2 : 1 ≤ 2 * q := by linarith
  have hq20 : 0 < 2 * q := by linarith
  set Λ := S7FCH4_Lg r S K + S7FCH4_Lh r S K with hΛdef
  have hΛ : 0 ≤ Λ := add_nonneg (S7FCH4_Lg_nonneg r S K) (S7FCH4_Lh_nonneg r S K)
  set k : ℝ≥0∞ := ENNReal.ofReal (2 * Real.sqrt T * Λ) with hk
  have hktop : k ≠ ⊤ := ENNReal.ofReal_ne_top
  set δ : ℕ → ℝ≥0∞ := fun N => ENNReal.ofReal (1 / ((N : ℝ) + 1)) with hδdef
  have hδ0 : ∀ N, δ N ≠ 0 := fun N => by
    simp only [hδdef, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hδt : Tendsto δ atTop (𝓝 0) := by
    show Tendsto (fun N : ℕ => ENNReal.ofReal (1 / ((N : ℝ) + 1))) atTop (𝓝 0)
    have := ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using this
  set Ws : ℕ → ℝ≥0∞ := fun N => ⨆ a, wassersteinE (2 * q) (μ N a) (ν a) with hWs
  set Ms : ℕ → ℝ≥0∞ := fun N => ⨆ a, ENNReal.ofReal ‖m N a‖ with hMs
  set w : ℕ → ℝ≥0∞ := fun N => Ws N + δ N with hwdef
  have hwt : Tendsto w atTop (𝓝 0) := by simpa using hw.add hδt
  have hsq : Tendsto (fun N : ℕ => ENNReal.ofReal (Real.sqrt N)⁻¹) atTop (𝓝 0) := by
    have h0 : Tendsto (fun N : ℕ => (Real.sqrt N)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    simpa using ENNReal.tendsto_ofReal h0
  set e : ℕ → ℝ≥0∞ := fun N => Ms N + ENNReal.ofReal (Real.sqrt N)⁻¹ with hedef
  have het : Tendsto e atTop (𝓝 0) := by simpa using hm.add hsq
  set Bd : ℕ → ℝ≥0∞ := fun N => w N + k * (1 + 2 * c + w N) * (w N + e N) with hBd
  have hBt : Tendsto Bd atTop (𝓝 0) := by
    have h1 : Tendsto (fun N => k * (1 + 2 * c + w N)) atTop (𝓝 (k * (1 + 2 * c + 0))) :=
      ENNReal.Tendsto.const_mul (tendsto_const_nhds.add hwt) (Or.inr hktop)
    have h2 : Tendsto (fun N => w N + e N) atTop (𝓝 (0 + 0)) := hwt.add het
    have hne : k * (1 + 2 * c + 0) ≠ ⊤ := by
      refine ENNReal.mul_ne_top hktop ?_
      simp [ENNReal.add_eq_top, ENNReal.mul_eq_top, hc]
    have h3 := ENNReal.Tendsto.mul h1 (Or.inr (by simp)) h2 (Or.inr hne)
    have h4 := hwt.add h3
    simpa [hBd, mul_assoc] using h4
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hBt
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hμ, hYi, hm.eventually (gt_mem_nhds zero_lt_one),
    hw.eventually (gt_mem_nhds zero_lt_one)] with N hN1 hN2 hN3 hN4
  refine iSup_le fun a => ?_
  have hWa : wassersteinE (2 * q) (μ N a) (ν a) ≤ Ws N := le_iSup (fun a => wassersteinE (2 * q) (μ N a) (ν a)) a
  have hMa : ENNReal.ofReal ‖m N a‖ ≤ Ms N := le_iSup (fun a => ENNReal.ofReal ‖m N a‖) a
  have hWne : wassersteinE (2 * q) (μ N a) (ν a) ≠ ⊤ := ne_top_of_lt (lt_of_le_of_lt hWa hN4)
  have hm1 : ‖m N a‖ ≤ 1 := by
    have : ENNReal.ofReal ‖m N a‖ < 1 := lt_of_le_of_lt hMa hN3
    rw [← ENNReal.ofReal_one] at this
    exact ((ENNReal.ofReal_lt_ofReal_iff zero_lt_one).1 this).le
  obtain ⟨π, hπ, hlt⟩ := S7FCH4_exists_coupling hq20 (μ N a) (ν a) (hδ0 N) hWne
  have : IsProbabilityMeasure π := hπ.isProbabilityMeasure
  have hs : (0 : ℝ) ≤ (Real.sqrt N)⁻¹ := by positivity
  have hε : 0 ≤ ‖m N a‖ + (Real.sqrt N)⁻¹ := by positivity
  have htr := S7FCH4_transport hT hq (μ N a) (ν a) (S7FCH4_Y S K (Real.sqrt N)⁻¹ (m N a))
    (S7FCH4_Y S K 0 (0 : PathSpace d r T)) (S7FCH4_Y_continuous S K _ _) (S7FCH4_Y_continuous S K _ _)
    (hN2 a) (hY0i a) π hπ Λ _ hΛ hε (fun u v => S7FCH4_Y_sub_le S K hs hm1 u v)
  refine htr.trans ?_
  have hx : S7FCH4_Lp (2 * q) π (fun z => ENNReal.ofReal ‖z.1 - z.2‖) ≤ w N :=
    hlt.le.trans (add_le_add hWa le_rfl)
  have hA : S7FCH4_Lp (2 * q) π (fun z => ENNReal.ofReal (1 + ‖z.1‖ + ‖z.2‖)) ≤ 1 + 2 * c + w N := by
    refine (S7FCH4_A_le hq2 π).trans ?_
    rw [S7FCH4_Lp_marg1 hπ (2 * q) (f := fun u => ENNReal.ofReal ‖u‖)
      (ENNReal.measurable_ofReal.comp measurable_norm)]
    gcongr
    exact hN1 a
  have he : ENNReal.ofReal (‖m N a‖ + (Real.sqrt N)⁻¹) ≤ e N := by
    rw [ENNReal.ofReal_add (norm_nonneg _) hs]
    exact add_le_add hMa le_rfl
  show _ ≤ w N + k * (1 + 2 * c + w N) * (w N + e N)
  gcongr

end HRS.MC.Sec7.S7UCH

end
