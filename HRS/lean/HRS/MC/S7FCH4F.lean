import HRS.MC.S7FCH4E

/-!
# S7FCH4F: the limit lemma (H4, part F)

`S7FCH4_limit`: abstract limit argument.  If `W_{2q}(μ_N, ν) → 0`, `‖m_N‖ → 0`, `‖·‖_{L^{2q}(μ_N)} ≤ c < ∞`, and `Y_N`, `Y_0`
integrable, then the pushed-forward pair laws `(u, ι(Y_N u - ∫Y_N dμ_N))`, `(v, ι(Y_0 v - ∫Y_0 dν))` converge in `W_q`.
-/
open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace HRS.MC.Sec7.S7FCH4
open Classical
variable {d : ℕ} {r T : ℝ}

theorem S7FCH4_meas_diff :
    Measurable (fun z : PathSpace d r T × PathSpace d r T => ENNReal.ofReal ‖z.1 - z.2‖) :=
  ENNReal.measurable_ofReal.comp (continuous_fst.sub continuous_snd).norm.measurable

theorem S7FCH4_meas_n1 :
    Measurable (fun z : PathSpace d r T × PathSpace d r T => ENNReal.ofReal ‖z.1‖) :=
  ENNReal.measurable_ofReal.comp continuous_fst.norm.measurable

theorem S7FCH4_meas_n2 :
    Measurable (fun z : PathSpace d r T × PathSpace d r T => ENNReal.ofReal ‖z.2‖) :=
  ENNReal.measurable_ofReal.comp continuous_snd.norm.measurable

theorem S7FCH4_Lp_marg1 {π : Measure (PathSpace d r T × PathSpace d r T)} {μ ν : Measure (PathSpace d r T)}
    (hπ : IsCoupling π μ ν) (p : ℝ) {f : PathSpace d r T → ℝ≥0∞} (hf : Measurable f) :
    S7FCH4_Lp p π (fun z => f z.1) = S7FCH4_Lp p μ f := by
  unfold S7FCH4_Lp
  rw [← hπ.1, lintegral_map (hf.pow_const p) measurable_fst]

theorem S7FCH4_Lp_marg2 {π : Measure (PathSpace d r T × PathSpace d r T)} {μ ν : Measure (PathSpace d r T)}
    (hπ : IsCoupling π μ ν) (p : ℝ) {f : PathSpace d r T → ℝ≥0∞} (hf : Measurable f) :
    S7FCH4_Lp p π (fun z => f z.2) = S7FCH4_Lp p ν f := by
  unfold S7FCH4_Lp
  rw [← hπ.2, lintegral_map (hf.pow_const p) measurable_snd]

theorem S7FCH4_exists_coupling {p : ℝ} (hp : 0 < p) (μ ν : Measure (PathSpace d r T)) {δ : ℝ≥0∞}
    (hδ : δ ≠ 0) (hW : wassersteinE p μ ν ≠ ⊤) :
    ∃ π, IsCoupling π μ ν ∧
      S7FCH4_Lp p π (fun z => ENNReal.ofReal ‖z.1 - z.2‖) < wassersteinE p μ ν + δ := by
  have h : wassersteinE p μ ν < wassersteinE p μ ν + δ := ENNReal.lt_add_right hW hδ
  have h' : (⨅ π : couplings μ ν, (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ p) ∂π.1) ^ (1 / p)) <
      wassersteinE p μ ν + δ := h
  obtain ⟨⟨π, hπ⟩, hlt⟩ := iInf_lt_iff.1 h'
  refine ⟨π, hπ, ?_⟩
  have : S7FCH4_Lp p π (fun z => ENNReal.ofReal ‖z.1 - z.2‖) =
      (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ p) ∂π) ^ (1 / p) := by
    unfold S7FCH4_Lp
    congr 1
    exact lintegral_congr fun z => (ofReal_norm_rpow hp.le).symm
  rw [this]
  exact hlt

theorem S7FCH4_snd_le {p : ℝ} (hp : 1 ≤ p) (π : Measure (PathSpace d r T × PathSpace d r T)) :
    S7FCH4_Lp p π (fun z => ENNReal.ofReal ‖z.2‖) ≤
      S7FCH4_Lp p π (fun z => ENNReal.ofReal ‖z.1‖) + S7FCH4_Lp p π (fun z => ENNReal.ofReal ‖z.1 - z.2‖) := by
  refine (S7FCH4_Lp_mono (by linarith) fun z => ?_).trans
    (S7FCH4_Lp_add hp S7FCH4_meas_n1.aemeasurable S7FCH4_meas_diff.aemeasurable)
  show ENNReal.ofReal ‖z.2‖ ≤ ENNReal.ofReal ‖z.1‖ + ENNReal.ofReal ‖z.1 - z.2‖
  rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  simpa using norm_sub_le z.1 (z.1 - z.2)

theorem S7FCH4_A_le {p : ℝ} (hp : 1 ≤ p) (π : Measure (PathSpace d r T × PathSpace d r T))
    [IsProbabilityMeasure π] :
    S7FCH4_Lp p π (fun z => ENNReal.ofReal (1 + ‖z.1‖ + ‖z.2‖)) ≤
      1 + 2 * S7FCH4_Lp p π (fun z => ENNReal.ofReal ‖z.1‖) +
        S7FCH4_Lp p π (fun z => ENNReal.ofReal ‖z.1 - z.2‖) := by
  have hp0 : 0 < p := by linarith
  have hpw : ∀ z : PathSpace d r T × PathSpace d r T, ENNReal.ofReal (1 + ‖z.1‖ + ‖z.2‖) ≤
      (1 + ENNReal.ofReal ‖z.1‖) + (ENNReal.ofReal ‖z.1‖ + ENNReal.ofReal ‖z.1 - z.2‖) := by
    intro z
    have h1 : ‖z.2‖ ≤ ‖z.1‖ + ‖z.1 - z.2‖ := by simpa using norm_sub_le z.1 (z.1 - z.2)
    calc ENNReal.ofReal (1 + ‖z.1‖ + ‖z.2‖) ≤ ENNReal.ofReal (1 + ‖z.1‖ + (‖z.1‖ + ‖z.1 - z.2‖)) :=
          ENNReal.ofReal_le_ofReal (by linarith)
      _ = _ := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add (by positivity)
            (norm_nonneg _), ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _), ENNReal.ofReal_one]
  have hm1 := S7FCH4_meas_n1 (d := d) (r := r) (T := T)
  have hm2 := S7FCH4_meas_diff (d := d) (r := r) (T := T)
  calc S7FCH4_Lp p π (fun z => ENNReal.ofReal (1 + ‖z.1‖ + ‖z.2‖))
      ≤ S7FCH4_Lp p π (fun z => (1 + ENNReal.ofReal ‖z.1‖) + (ENNReal.ofReal ‖z.1‖ + ENNReal.ofReal ‖z.1 - z.2‖)) :=
        S7FCH4_Lp_mono hp0 hpw
    _ ≤ S7FCH4_Lp p π (fun z => 1 + ENNReal.ofReal ‖z.1‖) +
          S7FCH4_Lp p π (fun z => ENNReal.ofReal ‖z.1‖ + ENNReal.ofReal ‖z.1 - z.2‖) :=
        S7FCH4_Lp_add hp (hm1.const_add 1).aemeasurable (hm1.add hm2).aemeasurable
    _ ≤ (S7FCH4_Lp p π (fun _ => 1) + S7FCH4_Lp p π (fun z => ENNReal.ofReal ‖z.1‖)) +
          (S7FCH4_Lp p π (fun z => ENNReal.ofReal ‖z.1‖) + S7FCH4_Lp p π (fun z => ENNReal.ofReal ‖z.1 - z.2‖)) := by
        gcongr
        · exact S7FCH4_Lp_add hp aemeasurable_const hm1.aemeasurable
        · exact S7FCH4_Lp_add hp hm1.aemeasurable hm2.aemeasurable
    _ = _ := by
        rw [S7FCH4_Lp_const hp0]
        ring

theorem S7FCH4_limit (hT : 0 ≤ T) {q : ℝ} (hq : 1 ≤ q) (S : Finset (NonzeroLattice d))
    (K : NonzeroLattice d → FRKernel d)
    (μ : ℕ → Measure (PathSpace d r T)) [∀ N, IsProbabilityMeasure (μ N)]
    (ν : Measure (PathSpace d r T)) [IsProbabilityMeasure ν] (m : ℕ → PathSpace d r T)
    {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hμ : ∀ᶠ N : ℕ in atTop, S7FCH4_Lp (2 * q) (μ N) (fun u => ENNReal.ofReal ‖u‖) ≤ c)
    (hw : Tendsto (fun N : ℕ => wassersteinE (2 * q) (μ N) ν) atTop (𝓝 0))
    (hm : Tendsto (fun N : ℕ => ‖m N‖) atTop (𝓝 0))
    (hYi : ∀ᶠ N : ℕ in atTop, Integrable (S7FCH4_Y S K (Real.sqrt N)⁻¹ (m N)) (μ N))
    (hY0i : Integrable (S7FCH4_Y S K 0 (0 : PathSpace d r T)) ν) :
    Tendsto (fun N : ℕ => wassersteinE q
      ((μ N).map (fun u => (u, S7FCH4_iota hT (S7FCH4_Y S K (Real.sqrt N)⁻¹ (m N) u -
        ∫ x, S7FCH4_Y S K (Real.sqrt N)⁻¹ (m N) x ∂(μ N)))))
      (ν.map (fun v => (v, S7FCH4_iota hT (S7FCH4_Y S K 0 (0 : PathSpace d r T) v -
        ∫ x, S7FCH4_Y S K 0 (0 : PathSpace d r T) x ∂ν))))) atTop (𝓝 0) := by
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
  set w : ℕ → ℝ≥0∞ := fun N => wassersteinE (2 * q) (μ N) ν + δ N with hwdef
  have hwt : Tendsto w atTop (𝓝 0) := by simpa using hw.add hδt
  have hsq : Tendsto (fun N : ℕ => (Real.sqrt N)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  set e : ℕ → ℝ≥0∞ := fun N => ENNReal.ofReal (‖m N‖ + (Real.sqrt N)⁻¹) with hedef
  have het : Tendsto e atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (hm.add hsq)
    simpa using this
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
  filter_upwards [hμ, hYi, hm.eventually (ge_mem_nhds zero_lt_one),
    hw.eventually (gt_mem_nhds zero_lt_one)] with N hN1 hN2 hN3 hN4
  have hWne : wassersteinE (2 * q) (μ N) ν ≠ ⊤ := ne_top_of_lt hN4
  obtain ⟨π, hπ, hlt⟩ := S7FCH4_exists_coupling hq20 (μ N) ν (hδ0 N) hWne
  have : IsProbabilityMeasure π := hπ.isProbabilityMeasure
  have hs : (0 : ℝ) ≤ (Real.sqrt N)⁻¹ := by positivity
  have hε : 0 ≤ ‖m N‖ + (Real.sqrt N)⁻¹ := by positivity
  have htr := S7FCH4_transport hT hq (μ N) ν (S7FCH4_Y S K (Real.sqrt N)⁻¹ (m N))
    (S7FCH4_Y S K 0 (0 : PathSpace d r T)) (S7FCH4_Y_continuous S K _ _) (S7FCH4_Y_continuous S K _ _)
    hN2 hY0i π hπ Λ _ hΛ hε (fun u v => S7FCH4_Y_sub_le S K hs hN3 u v)
  refine htr.trans ?_
  have hx : S7FCH4_Lp (2 * q) π (fun z => ENNReal.ofReal ‖z.1 - z.2‖) ≤ w N := hlt.le
  have hA : S7FCH4_Lp (2 * q) π (fun z => ENNReal.ofReal (1 + ‖z.1‖ + ‖z.2‖)) ≤ 1 + 2 * c + w N := by
    refine (S7FCH4_A_le hq2 π).trans ?_
    rw [S7FCH4_Lp_marg1 hπ (2 * q) (f := fun u => ENNReal.ofReal ‖u‖)
      (ENNReal.measurable_ofReal.comp measurable_norm)]
    gcongr
  have he : ENNReal.ofReal (‖m N‖ + (Real.sqrt N)⁻¹) = e N := rfl
  rw [he]
  show _ ≤ w N + k * (1 + 2 * c + w N) * (w N + e N)
  gcongr

end HRS.MC.Sec7.S7FCH4
