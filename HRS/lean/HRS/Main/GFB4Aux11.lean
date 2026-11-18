import HRS.Main.GFB4Aux10

/-!
# GFB4, part 11: the single-window Wasserstein comparison, with the missing measurability of `M`, `G`

`gf_wasserstein_comparison` as stated in `GFSpec3` is false (the Riemann-sum limits `IsStochConv` are lower integrals, and `M`, `G`
are not assumed measurable): see ISSUES "GFB4".  Here it is proved with two extra hypotheses `hMm : ∀ t, Measurable (M t)`,
`hGm : ∀ t, Measurable (G t)`, which hold in the use in `gf_stage2` (`M ∘ π` with `M` an adapted martingale, `G` a martingale).

Counterexample sketch to the unrepaired statement: `A` with inner measure `0` and `Aᶜ` of inner measure `0` (Bernstein set), `Y` a
nice martingale of norm `~1` with `Z_Y = ∫V dY`, `B` a tiny martingale with `Z_B = ∫V dB`.  `M = 1_A Y + B`, `G = 1_A Y`, so `M - G = B`;
`Z = Z_Y + Z_B` and `Zb = 0` satisfy `IsStochConv` for `M`, `G` (the lower integral of `g = 1_A g_A + 1_{Aᶜ} g_{Aᶜ}` is `∫ min (g_A, g_{Aᶜ})`),
with `X₀ = X₀' = 0, R = 0`: `W_p(Law Z, δ_0) ~ 1` while the right side is `~ C ‖cost‖^{1/2} → 0` with `B → 0`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.GF

open HRS HRS.Uniform HRS.Uniform.Q45 HRS.Uniform.Q54c

section StochConv

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology E] [SecondCountableTopology H]

theorem gfb4_rs_measurable (VE : ℝ → ℝ → E →L[ℝ] E) (j : H →L[ℝ] E) {M : ℝ → Ω → H}
    (hM : ∀ t, Measurable (M t)) (t : ℝ) {n : ℕ} (r : Fin (n + 1) → ℝ) :
    Measurable (riemannSum VE j M t r) := by
  unfold riemannSum
  refine Finset.measurable_sum _ fun i _ => ?_
  exact ((VE t (r i.castSucc)).continuous.comp j.continuous).measurable.comp ((hM _).sub (hM _))

theorem gfb4_riemannSum_sub (VE : ℝ → ℝ → E →L[ℝ] E) (j : H →L[ℝ] E) (M G : ℝ → Ω → H) (T t : ℝ)
    {n : ℕ} (r : Fin (n + 1) → ℝ) (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) T) (ω : Ω) :
    riemannSum VE j (fun τ ω => M (min τ T) ω - G (min τ T) ω) t r ω =
      riemannSum VE j M t r ω - riemannSum VE j G t r ω := by
  unfold riemannSum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [min_eq_left (hr i.castSucc).2, min_eq_left (hr i.succ).2]
  rw [show M (r i.succ) ω - G (r i.succ) ω - (M (r i.castSucc) ω - G (r i.castSucc) ω) =
    (M (r i.succ) ω - M (r i.castSucc) ω) - (G (r i.succ) ω - G (r i.castSucc) ω) by abel]
  simp [map_sub]

theorem gfb4_sq_add_le (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  have := ENNReal.rpow_add_le_mul_rpow_add_rpow a b (p := 2) (by norm_num)
  have h2 : (2 : ℝ≥0∞) ^ ((2 : ℝ) - 1) = 2 := by norm_num
  rw [h2] at this
  simpa [ENNReal.rpow_two] using this

theorem gfb4_eps_calc (ε : ℝ) (hε : 0 < ε) :
    (2 : ℝ≥0∞) * (ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4)) = ENNReal.ofReal ε := by
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

/-- Linearity of stochastic convolutions (for measurable integrators). -/
theorem gfb4_isStochConv_sub (P : Measure Ω) (VE : ℝ → ℝ → E →L[ℝ] E) (j : H →L[ℝ] E)
    {M G : ℝ → Ω → H} (hMm : ∀ t, Measurable (M t)) (hGm : ∀ t, Measurable (G t)) {T t : ℝ}
    (ht0 : 0 ≤ t) (htT : t ≤ T) {Z Zb : Ω → E} (hZm : Measurable Z) (hZbm : Measurable Zb)
    (hZ : IsStochConv P VE j M 0 t Z) (hZb : IsStochConv P VE j G 0 t Zb) :
    IsStochConv P VE j (fun τ ω => M (min τ T) ω - G (min τ T) ω) 0 t (fun ω => Z ω - Zb ω) := by
  intro ε hε
  obtain ⟨δ1, hδ1, h1⟩ := hZ (ε / 4) (by positivity)
  obtain ⟨δ2, hδ2, h2⟩ := hZb (ε / 4) (by positivity)
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun n r h0 hn hmono hmesh => ?_⟩
  have hmem : ∀ i, r i ∈ Set.Icc (0 : ℝ) T := fun i =>
    ⟨(h0 ▸ hmono (Fin.zero_le i)), (hn ▸ hmono (Fin.le_last i)).trans htT⟩
  have a1 := h1 n r h0 hn hmono (fun i => (hmesh i).trans_le (min_le_left _ _))
  have a2 := h2 n r h0 hn hmono (fun i => (hmesh i).trans_le (min_le_right _ _))
  have hf1m : Measurable fun ω => ‖Z ω - riemannSum VE j M t r ω‖ₑ ^ 2 :=
    ((hZm.sub (gfb4_rs_measurable VE j hMm t r)).enorm).pow_const 2
  calc ∫⁻ ω, ‖(Z ω - Zb ω) - riemannSum VE j (fun τ ω => M (min τ T) ω - G (min τ T) ω) t r ω‖ₑ ^ 2 ∂P
      ≤ ∫⁻ ω, 2 * (‖Z ω - riemannSum VE j M t r ω‖ₑ ^ 2 +
          ‖Zb ω - riemannSum VE j G t r ω‖ₑ ^ 2) ∂P := by
        refine lintegral_mono fun ω => ?_
        rw [gfb4_riemannSum_sub VE j M G T t r hmem ω]
        refine le_trans ?_ (gfb4_sq_add_le _ _)
        gcongr
        refine le_trans (le_of_eq ?_) (enorm_sub_le (a := Z ω - riemannSum VE j M t r ω)
          (b := Zb ω - riemannSum VE j G t r ω))
        congr 1
        abel
    _ = 2 * (∫⁻ ω, ‖Z ω - riemannSum VE j M t r ω‖ₑ ^ 2 ∂P +
          ∫⁻ ω, ‖Zb ω - riemannSum VE j G t r ω‖ₑ ^ 2 ∂P) := by
        rw [lintegral_const_mul' _ _ (by simp), lintegral_add_left hf1m]
    _ < 2 * (ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4)) := by
        refine (ENNReal.mul_lt_mul_iff_right (by simp) (by simp)).2 ?_  
        exact ENNReal.add_lt_add a1 a2
    _ = ENNReal.ofReal ε := gfb4_eps_calc ε hε

/-- `L²`-uniqueness of stochastic convolutions. -/
theorem gfb4_isStochConv_unique (P : Measure Ω) (VE : ℝ → ℝ → E →L[ℝ] E) (j : H →L[ℝ] E)
    {M : ℝ → Ω → H} (hMm : ∀ t, Measurable (M t)) {T t : ℝ} (hT : 0 ≤ T) (ht0 : 0 ≤ t) (htT : t ≤ T)
    {Z₁ Z₂ : Ω → E} (hZ₁m : AEMeasurable Z₁ P) (hZ₂m : AEMeasurable Z₂ P)
    (hZ₁ : IsStochConv P VE j M 0 t Z₁) (hZ₂ : IsStochConv P VE j M 0 t Z₂) : Z₁ =ᵐ[P] Z₂ := by
  have key : ∀ ε : ℝ, 0 < ε → ∫⁻ ω, ‖Z₁ ω - Z₂ ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨δ1, hδ1, h1⟩ := hZ₁ (ε / 4) (by positivity)
    obtain ⟨δ2, hδ2, h2⟩ := hZ₂ (ε / 4) (by positivity)
    obtain ⟨N, hN⟩ := exists_nat_gt (T / min δ1 δ2)
    obtain ⟨p0, p1, p2, p3⟩ := gfb4_grid_partition hT ht0 htT N
    have hstep : T / ((N : ℝ) + 1) < min δ1 δ2 := by
      rw [div_lt_iff₀ (by positivity)]
      have : T / min δ1 δ2 < N + 1 := by linarith
      rw [div_lt_iff₀ (lt_min hδ1 hδ2)] at this
      linarith
    set r : Fin (N + 2) → ℝ := fun i => min (gridPt T N (i : ℕ)) t with hr
    have a1 := h1 (N + 1) r p0 p1 p2 (fun i => (lt_of_le_of_lt (p3 i) hstep).trans_le (min_le_left _ _))
    have a2 := h2 (N + 1) r p0 p1 p2 (fun i => (lt_of_le_of_lt (p3 i) hstep).trans_le (min_le_right _ _))
    have hf1m : AEMeasurable (fun ω => ‖Z₁ ω - riemannSum VE j M t r ω‖ₑ ^ 2) P :=
      ((hZ₁m.sub (gfb4_rs_measurable VE j hMm t r).aemeasurable).enorm).pow_const 2
    calc ∫⁻ ω, ‖Z₁ ω - Z₂ ω‖ₑ ^ 2 ∂P
        ≤ ∫⁻ ω, 2 * (‖Z₁ ω - riemannSum VE j M t r ω‖ₑ ^ 2 +
            ‖Z₂ ω - riemannSum VE j M t r ω‖ₑ ^ 2) ∂P := by
          refine lintegral_mono fun ω => ?_
          refine le_trans ?_ (gfb4_sq_add_le _ _)
          gcongr
          refine le_trans (le_of_eq ?_) (enorm_sub_le (a := Z₁ ω - riemannSum VE j M t r ω)
            (b := Z₂ ω - riemannSum VE j M t r ω))
          congr 1
          abel
      _ = 2 * (∫⁻ ω, ‖Z₁ ω - riemannSum VE j M t r ω‖ₑ ^ 2 ∂P +
            ∫⁻ ω, ‖Z₂ ω - riemannSum VE j M t r ω‖ₑ ^ 2 ∂P) := by
          rw [lintegral_const_mul' _ _ (by simp), lintegral_add_left' hf1m]
      _ ≤ 2 * (ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4)) := by
          gcongr
      _ = ENNReal.ofReal ε := gfb4_eps_calc ε hε
  have h0 : ∫⁻ ω, ‖Z₁ ω - Z₂ ω‖ₑ ^ 2 ∂P = 0 := by
    refine le_antisymm ?_ bot_le
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have := key (ε : ℝ) (by exact_mod_cast hε)
    simpa using this
  have hm : AEMeasurable (fun ω => ‖Z₁ ω - Z₂ ω‖ₑ ^ 2) P := ((hZ₁m.sub hZ₂m).enorm).pow_const 2
  rw [lintegral_eq_zero_iff' hm] at h0
  filter_upwards [h0] with ω hω
  have : ‖Z₁ ω - Z₂ ω‖ₑ = 0 := by simpa using hω
  have := enorm_eq_zero.1 this
  exact sub_eq_zero.1 this

end StochConv

/-- Two a.s.-continuous processes that agree a.s. at each fixed time of `[0,T]` agree a.s. at all times of `[0,T]`. -/
theorem gfb4_ae_forall_Icc {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) {E : Type*}
    [TopologicalSpace E] [T2Space E] {T : ℝ} (hT : 0 ≤ T) (X Y : ℝ → Ω → E)
    (hX : ∀ᵐ ω ∂P, ContinuousOn (fun t => X t ω) (Set.Icc 0 T))
    (hY : ∀ᵐ ω ∂P, ContinuousOn (fun t => Y t ω) (Set.Icc 0 T))
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, X t =ᵐ[P] Y t) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X t ω = Y t ω := by
  have hq : ∀ᵐ ω ∂P, ∀ q : ℚ, (q : ℝ) ∈ Set.Icc (0 : ℝ) T → X (q : ℝ) ω = Y (q : ℝ) ω := by
    refine ae_all_iff.2 fun q => ?_
    by_cases hqm : (q : ℝ) ∈ Set.Icc (0 : ℝ) T
    · filter_upwards [h _ hqm] with ω hω _ using hω
    · exact Filter.Eventually.of_forall fun ω hh => absurd hh hqm
  filter_upwards [hX, hY, hq] with ω hx hy hq t ht
  set s : Set ℝ := {x | x ∈ Set.Icc (0 : ℝ) T ∧ ∃ q : ℚ, (q : ℝ) = x} with hs
  have hsub : s ⊆ Set.Icc (0 : ℝ) T := fun x hx => hx.1
  have hcl : Set.Icc (0 : ℝ) T ⊆ closure s := by
    rcases hT.eq_or_lt with h0 | hpos
    · intro x hx
      have : x = 0 := by rw [← h0] at hx; exact le_antisymm hx.2 hx.1
      subst this
      exact subset_closure ⟨⟨le_rfl, hT⟩, ⟨0, by simp⟩⟩
    · rw [← closure_Ioo hpos.ne]
      refine closure_minimal ?_ isClosed_closure
      intro x hx
      have h1 := (Rat.denseRange_cast (𝕜 := ℝ)).open_subset_closure_inter isOpen_Ioo hx
      refine closure_mono ?_ h1
      rintro y ⟨hy1, ⟨q, hq'⟩⟩
      exact ⟨⟨hy1.1.le, hy1.2.le⟩, ⟨q, hq'⟩⟩
  have heq : Set.EqOn (fun t => X t ω) (fun t => Y t ω) s := by
    rintro x ⟨hx1, ⟨q, rfl⟩⟩
    exact hq q hx1
  exact heq.of_subset_closure hx hy hsub hcl ht

end HRS.GF
