import HRS.MS.ZeroTempAux9

/-!
# SA11, packet C2a: continuous representatives of weak jets; norm bounds from jet-wise bounds

* `sa11_approx_cont`: if `G ∈ W^{m,p}` has a continuous zeroth component `u`, there are `φ_k ∈ C_c^∞` with `J φ_k → G`
  and `φ_k → u` uniformly (the sup norm is controlled by the jet norm, `sa11_embed`).
* `sa11_ev_weak`, `sa11_evMeas_weak`: `ev_x G = u(x)`, `evMeas μ G = ∫ u dμ`.
* `sa11_enorm_le_of_repr`: an `ℝ≥0∞`-valued version of `sa11_norm_le_of_repr`.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.Whole.AppendixA
open scoped ENNReal ContDiff

namespace HRS.MS.ZeroTemp

variable {d : ℕ} {m : ℕ} {p : ℝ} [Fact (2 ≤ p)]

section Approx

variable (hd : 1 ≤ d) (hm : mStar d + ⌊(d : ℝ) / p⌋₊ + 1 ≤ m)

include hd hm

theorem sa11_approx_cont (G : WmpSpace d m p) {u : Euc d → ℝ} (hu : Continuous u)
    (hG : ∀ᵐ x ∂(volume : Measure (Euc d)),
      ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) = u x) :
    ∃ φ : ℕ → sa11_V d, Tendsto (fun k => sa11_J (m := m) (p := p) (φ k)) atTop (𝓝 G) ∧
      ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k ≥ K, ∀ x, |(φ k).1 x - u x| ≤ ε := by
  have hF := sa11_denseRange_J (d := d) (m := m) (p := p) G
  rw [mem_closure_iff_seq_limit] at hF
  obtain ⟨x, hxr, hxt⟩ := hF
  choose φ hφ using hxr
  have hxt' : Tendsto (fun k => sa11_J (m := m) (p := p) (φ k)) atTop (𝓝 G) := by
    have : (fun k => sa11_J (m := m) (p := p) (φ k)) = x := funext hφ
    rw [this]; exact hxt
  refine ⟨φ, hxt', ?_⟩
  set Cm := sa11_Cemb (m := m) (p := p) hd hm with hCm
  have hC0 : 0 ≤ Cm := sa11_Cemb_nonneg hd hm
  -- uniform Cauchy property
  have hcauchy : CauchySeq (fun k => sa11_J (m := m) (p := p) (φ k)) := hxt'.cauchySeq
  have hunif : ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k ≥ K, ∀ l ≥ K, ∀ y : Euc d, |(φ k).1 y - (φ l).1 y| ≤ ε := by
    intro ε hε
    obtain ⟨K, hK⟩ := Metric.cauchySeq_iff.1 hcauchy (ε / (Cm + 1)) (by positivity)
    refine ⟨K, fun k hk l hl y => ?_⟩
    have h1 := hK k hk l hl
    rw [dist_eq_norm] at h1
    have h2 := sa11_Cemb_spec (m := m) (p := p) hd hm (φ k - φ l) 0 (Nat.zero_le _) y
    rw [norm_iteratedFDeriv_zero, map_sub] at h2
    have h3 : ‖(φ k - φ l).1 y‖ = |(φ k).1 y - (φ l).1 y| := by
      rw [Real.norm_eq_abs]; rfl
    rw [h3] at h2
    calc |(φ k).1 y - (φ l).1 y| ≤ Cm * ‖sa11_J (m := m) (p := p) (φ k) - sa11_J (m := m) (p := p) (φ l)‖ := h2
      _ ≤ Cm * (ε / (Cm + 1)) := mul_le_mul_of_nonneg_left h1.le hC0
      _ ≤ ε := by
          rw [mul_div_assoc']
          rw [div_le_iff₀ (by positivity)]
          nlinarith
  -- pointwise limit
  have hpt : ∀ y : Euc d, ∃ g : ℝ, Tendsto (fun k => (φ k).1 y) atTop (𝓝 g) := by
    intro y
    refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff.2 fun ε hε => ?_)
    obtain ⟨K, hK⟩ := hunif (ε / 2) (by positivity)
    exact ⟨K, fun k hk l hl => by
      rw [Real.dist_eq]; exact lt_of_le_of_lt (hK k hk l hl y) (by linarith)⟩
  choose g hg using hpt
  have hgu : ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k ≥ K, ∀ y, |(φ k).1 y - g y| ≤ ε := by
    intro ε hε
    obtain ⟨K, hK⟩ := hunif ε hε
    refine ⟨K, fun k hk y => ?_⟩
    have : Tendsto (fun l => |(φ k).1 y - (φ l).1 y|) atTop (𝓝 |(φ k).1 y - g y|) :=
      (continuous_abs.tendsto _).comp (tendsto_const_nhds.sub (hg y))
    exact le_of_tendsto this (eventually_atTop.2 ⟨K, fun l hl => hK k hk l hl y⟩)
  have hgc : Continuous g := by
    have hT : TendstoUniformly (fun k y => (φ k).1 y) g atTop := by
      rw [Metric.tendstoUniformly_iff]
      intro ε hε
      obtain ⟨K, hK⟩ := hgu (ε / 2) (by positivity)
      filter_upwards [eventually_ge_atTop K] with k hk y
      rw [Real.dist_eq, abs_sub_comm]
      exact lt_of_le_of_lt (hK k hk y) (by linarith)
    exact hT.continuous (Eventually.of_forall fun k => (φ k).2.1.continuous).frequently
  -- `g = u`
  have hgeq : g = u := by
    have hdiff : ∀ᵐ y ∂(volume : Measure (Euc d)), (g y - u y) = 0 := by
      refine ae_eq_zero_of_integral_contDiff_smul_eq_zero ((hgc.sub hu).locallyIntegrable) fun ψ hψ hψc => ?_
      have hLψ := sa11_pairL (m := m) (p := p) (wZero d m) hψ.continuous hψc
      have hlim : Tendsto (fun k => sa11_pairL (m := m) (p := p) (wZero d m) hψ.continuous hψc
          ((sa11_J (m := m) (p := p) (φ k) : WmpSpace d m p) : WLp d m p)) atTop
          (𝓝 (sa11_pairL (m := m) (p := p) (wZero d m) hψ.continuous hψc (G : WLp d m p))) :=
        ((sa11_pairL (m := m) (p := p) (wZero d m) hψ.continuous hψc).continuous.tendsto _).comp
          ((continuous_subtype_val.tendsto G).comp hxt')
      have hval : ∀ k, sa11_pairL (m := m) (p := p) (wZero d m) hψ.continuous hψc
          ((sa11_J (m := m) (p := p) (φ k) : WmpSpace d m p) : WLp d m p) = ∫ y, (φ k).1 y * ψ y := by
        intro k
        rw [sa11_pairL_apply]
        refine integral_congr_ae ?_
        filter_upwards [sa11_J_coe (m := m) (p := p) (φ k)] with y hy
        rw [hy]
        show partialDeriv (wZero d m).2 (φ k).1 y * ψ y = _
        rw [show partialDeriv (wZero d m).2 (φ k).1 = (φ k).1 from sa11_partialDeriv_zero (wZero d m).2 (φ k).1]
      have hlimG : sa11_pairL (m := m) (p := p) (wZero d m) hψ.continuous hψc (G : WLp d m p) = ∫ y, u y * ψ y := by
        rw [sa11_pairL_apply]
        exact integral_congr_ae (hG.mono fun y hy => by simp only [hy])
      -- `∫ φ_k ψ → ∫ g ψ`
      have hlim2 : Tendsto (fun k => ∫ y, (φ k).1 y * ψ y) atTop (𝓝 (∫ y, g y * ψ y)) := by
        have hψi : Integrable ψ := hψ.continuous.integrable_of_hasCompactSupport hψc
        have hI : 0 ≤ ∫ y, |ψ y| := integral_nonneg fun y => abs_nonneg _
        rw [Metric.tendsto_atTop]
        intro ε hε
        obtain ⟨K, hK⟩ := hgu (ε / ((∫ y, |ψ y|) + 1)) (div_pos hε (by linarith))
        refine ⟨K, fun k hk => ?_⟩
        have hint1 : Integrable (fun y => (φ k).1 y * ψ y) :=
          ((φ k).2.1.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hψc.mul_left
        have hint2 : Integrable (fun y => g y * ψ y) :=
          (hgc.mul hψ.continuous).integrable_of_hasCompactSupport hψc.mul_left
        rw [Real.dist_eq, ← integral_sub hint1 hint2]
        have hb : ∀ y, ‖(φ k).1 y * ψ y - g y * ψ y‖ ≤ (ε / ((∫ y, |ψ y|) + 1)) * |ψ y| := by
          intro y
          rw [← sub_mul, norm_mul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (hK k hk y) (abs_nonneg _)
        calc |∫ y, ((φ k).1 y * ψ y - g y * ψ y)| ≤ ∫ y, (ε / ((∫ y, |ψ y|) + 1)) * |ψ y| := by
              have := norm_integral_le_of_norm_le (hψi.abs.const_mul (ε / ((∫ y, |ψ y|) + 1)))
                (Eventually.of_forall hb)
              simpa [Real.norm_eq_abs] using this
          _ = (ε / ((∫ y, |ψ y|) + 1)) * ∫ y, |ψ y| := by rw [integral_const_mul]
          _ < ε := by
              rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
              nlinarith
      have e1 : ∫ y, g y * ψ y = ∫ y, u y * ψ y :=
        tendsto_nhds_unique hlim2 ((hlim.congr hval).congr' (Eventually.of_forall fun _ => rfl) |>.trans (by rw [hlimG]))
      have hI1 : Integrable (fun y => g y * ψ y) :=
        (hgc.mul hψ.continuous).integrable_of_hasCompactSupport hψc.mul_left
      have hI2 : Integrable (fun y => u y * ψ y) :=
        (hu.mul hψ.continuous).integrable_of_hasCompactSupport hψc.mul_left
      simp only [smul_eq_mul]
      have : ∫ y, ψ y * (g y - u y) = (∫ y, g y * ψ y) - ∫ y, u y * ψ y := by
        rw [← integral_sub hI1 hI2]
        congr 1; funext y; ring
      rw [this, e1]; ring
    have : ∀ y, g y = u y := by
      have hc : Continuous fun y => g y - u y := hgc.sub hu
      have h0 : (fun y => g y - u y) = fun _ => 0 :=
        (Continuous.ae_eq_iff_eq volume hc continuous_const).1 (hdiff.mono fun y hy => hy)
      intro y
      have := congrFun h0 y
      simpa [sub_eq_zero] using this
    funext y; exact this y
  intro ε hε
  obtain ⟨K, hK⟩ := hgu ε hε
  exact ⟨K, fun k hk y => by rw [← hgeq]; exact hK k hk y⟩

theorem sa11_ev_weak (G : WmpSpace d m p) {u : Euc d → ℝ} (hu : Continuous u)
    (hG : ∀ᵐ x ∂(volume : Measure (Euc d)),
      ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) = u x) (x : Euc d) :
    sa11_ev (m := m) (p := p) x G = u x := by
  obtain ⟨φ, hφt, hφu⟩ := sa11_approx_cont hd hm G hu hG
  have h1 : Tendsto (fun k => sa11_ev (m := m) (p := p) x (sa11_J (m := m) (p := p) (φ k))) atTop
      (𝓝 (sa11_ev (m := m) (p := p) x G)) :=
    ((sa11_ev (m := m) (p := p) x).continuous.tendsto G).comp hφt
  have h2 : Tendsto (fun k => (φ k).1 x) atTop (𝓝 (u x)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨K, hK⟩ := hφu (ε / 2) (half_pos hε)
    exact ⟨K, fun k hk => by rw [Real.dist_eq]; exact lt_of_le_of_lt (hK k hk x) (half_lt_self hε)⟩
  exact tendsto_nhds_unique h1 (h2.congr fun k => (sa11_ev_apply hd hm x (φ k)).symm)

theorem sa11_evMeas_weak (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (G : WmpSpace d m p) {u : Euc d → ℝ}
    (hu : Continuous u)
    (hG : ∀ᵐ x ∂(volume : Measure (Euc d)),
      ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) = u x) :
    sa11_evMeas (m := m) (p := p) μ G = ∫ x, u x ∂μ := by
  obtain ⟨φ, hφt, hφu⟩ := sa11_approx_cont hd hm G hu hG
  have h1 : Tendsto (fun k => sa11_evMeas (m := m) (p := p) μ (sa11_J (m := m) (p := p) (φ k))) atTop
      (𝓝 (sa11_evMeas (m := m) (p := p) μ G)) :=
    ((sa11_evMeas (m := m) (p := p) μ).continuous.tendsto G).comp hφt
  -- `u` is bounded, hence integrable
  obtain ⟨K1, hK1⟩ := hφu 1 one_pos
  obtain ⟨B, hB⟩ := (φ K1).2.1.continuous.bounded_above_of_compact_support (φ K1).2.2
  have hub : ∀ x, ‖u x‖ ≤ B + 1 := fun x => by
    have h1 := hK1 K1 le_rfl x
    have h2 := hB x
    rw [Real.norm_eq_abs] at h2 ⊢
    calc |u x| ≤ |(φ K1).1 x| + |(φ K1).1 x - u x| := by
          have := abs_sub_abs_le_abs_sub (u x) ((φ K1).1 x)
          rw [abs_sub_comm] at this
          linarith [abs_sub_comm ((φ K1).1 x) (u x), abs_nonneg (u x)]
      _ ≤ B + 1 := by linarith
  have huint : Integrable u μ := Integrable.of_bound hu.aestronglyMeasurable (B + 1) (Eventually.of_forall hub)
  have h2 : Tendsto (fun k => ∫ x, (φ k).1 x ∂μ) atTop (𝓝 (∫ x, u x ∂μ)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨K, hK⟩ := hφu (ε / 2) (half_pos hε)
    refine ⟨K, fun k hk => ?_⟩
    have hint : Integrable (fun x => (φ k).1 x) μ :=
      (φ k).2.1.continuous.integrable_of_hasCompactSupport (φ k).2.2
    rw [Real.dist_eq, ← integral_sub hint huint]
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => (φ k).1 x - u x) (C := ε / 2)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hK k hk x)
    have hμ : μ.real Set.univ = 1 := by simp [Measure.real]
    rw [hμ, mul_one, Real.norm_eq_abs] at this
    exact lt_of_le_of_lt (by simpa [Real.norm_eq_abs] using this) (half_lt_self hε)
  exact tendsto_nhds_unique h1 (h2.congr fun k => (sa11_evMeas_apply hd hm μ (φ k)).symm)

end Approx

/-! ### Norm bounds from jet-wise bounds, `ℝ≥0∞` version -/

section EnormRepr

variable {Ω : Type*} [MeasurableSpace Ω]

theorem sa11_enorm_le_of_repr (P : Measure Ω) (L : Ω → WmpSpace d m p →L[ℝ] ℝ) (B : Ω → ℝ≥0∞)
    (h : ∀ φ : sa11_V d, ∀ᵐ ζ ∂P, ENNReal.ofReal |L ζ (sa11_J (m := m) (p := p) φ)| ≤
      B ζ * ENNReal.ofReal ‖sa11_J (m := m) (p := p) φ‖) :
    ∀ᵐ ζ ∂P, ‖L ζ‖ₑ ≤ B ζ := by
  obtain ⟨D, hDc, hDd⟩ := sa11_exists_countable_dense (d := d) (m := m) (p := p)
  have hall : ∀ᵐ ζ ∂P, ∀ φ ∈ D, ENNReal.ofReal |L ζ (sa11_J (m := m) (p := p) φ)| ≤
      B ζ * ENNReal.ofReal ‖sa11_J (m := m) (p := p) φ‖ :=
    (MeasureTheory.ae_ball_iff hDc).2 fun φ _ => h φ
  filter_upwards [hall] with ζ hζ
  rcases eq_or_ne (B ζ) ⊤ with hB | hB
  · rw [hB]; exact le_top
  · have hb0 : 0 ≤ (B ζ).toReal := ENNReal.toReal_nonneg
    have hreal : ∀ F : WmpSpace d m p, |L ζ F| ≤ (B ζ).toReal * ‖F‖ := by
      have hcl : IsClosed {F : WmpSpace d m p | |L ζ F| ≤ (B ζ).toReal * ‖F‖} :=
        isClosed_le (continuous_abs.comp (L ζ).continuous) (continuous_const.mul continuous_norm)
      have hsub : sa11_J (d := d) (m := m) (p := p) '' D ⊆ {F : WmpSpace d m p | |L ζ F| ≤ (B ζ).toReal * ‖F‖} := by
        rintro _ ⟨φ, hφ, rfl⟩
        have := hζ φ hφ
        rw [← ENNReal.ofReal_toReal hB, ← ENNReal.ofReal_mul hb0] at this
        exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hb0 (norm_nonneg _))).1 this
      intro F
      exact closure_minimal hsub hcl (hDd F)
    have hn : ‖L ζ‖ ≤ (B ζ).toReal := (L ζ).opNorm_le_bound hb0 fun F => by
      have := hreal F
      simpa [Real.norm_eq_abs] using this
    rw [← ofReal_norm_eq_enorm]
    calc ENNReal.ofReal ‖L ζ‖ ≤ ENNReal.ofReal (B ζ).toReal := ENNReal.ofReal_le_ofReal hn
      _ = B ζ := ENNReal.ofReal_toReal hB

end EnormRepr

end HRS.MS.ZeroTemp
