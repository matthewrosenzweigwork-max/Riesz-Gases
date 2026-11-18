import HRS.Stochastic.Ito

/-!
# Packet Q09-B, part 1: an Itô second-moment bound with exponential weight

Abstract moment bound for an Itô process with additive noise (used for `B:lem:moments`, S.A.18):
if `g ≥ 0` is `C²` with `‖Dg‖ ≤ K(1+g)`, and the Itô drift of `g(X)` is bounded by `c g(X) + c₀ + u`
with `E u_s ≤ A`, then `E g(X_t) ≤ e^{cT}(E g(X_0) + (c₀+A)T)`.  Proof: Itô's formula for
`e^{-ct} g(x)`, localisation by the stopping times `{g(X) ≥ n}`, zero mean of the stopped Itô
integral, Fatou.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Whole.Q09B

open HRS

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ι : Type*} [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem q09b_drift_value {T : ℝ} (hT : 0 < T) {g : E → ℝ} (hg : ContDiff ℝ 2 g) (c : ℝ)
    {s : ℝ} (hs : s ∈ Set.Icc 0 T) (x v : E) (σ : ι → E) :
    derivWithin (fun r => (fun t x => Real.exp (-(c * t)) * g x) r x) (Set.Icc 0 T) s +
      fderiv ℝ ((fun t x => Real.exp (-(c * t)) * g x) s) x v +
      (1 / 2) * ∑ k, fderiv ℝ (fderiv ℝ ((fun t x => Real.exp (-(c * t)) * g x) s)) x (σ k) (σ k)
    = Real.exp (-(c * s)) * (-c * g x + fderiv ℝ g x v +
        (1 / 2) * ∑ k, fderiv ℝ (fderiv ℝ g) x (σ k) (σ k)) := by
  have hd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hd1 : Differentiable ℝ (fderiv ℝ g) := (hg.fderiv_right (m := 1) (by norm_num)).differentiable
    (by norm_num)
  have h1 : derivWithin (fun r => Real.exp (-(c * r)) * g x) (Set.Icc 0 T) s
      = -c * Real.exp (-(c * s)) * g x := by
    have h : HasDerivAt (fun r : ℝ => Real.exp (-(c * r)) * g x)
        (Real.exp (-(c * s)) * (-c) * g x) s := by
      have h0 : HasDerivAt (fun r : ℝ => -(c * r)) (-c) s := by
        have := ((hasDerivAt_id s).const_mul c).neg
        convert this using 1
        · funext y; simp
        · simp
      exact (h0.exp).mul_const (g x)
    rw [h.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hT s hs)]
    ring
  have h2 : fderiv ℝ (fun x => Real.exp (-(c * s)) * g x)
      = fun x => Real.exp (-(c * s)) • fderiv ℝ g x := by
    funext y
    rw [fderiv_const_mul (hd y)]
  have h3 : fderiv ℝ (fderiv ℝ (fun x => Real.exp (-(c * s)) * g x)) x
      = Real.exp (-(c * s)) • fderiv ℝ (fderiv ℝ g) x := by
    rw [h2]
    exact ((hd1 x).hasFDerivAt.const_smul (Real.exp (-(c * s)))).fderiv
  simp only [h3]
  simp only [h1, h2, smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum]
  ring


/-- A monotone localising sequence of stopping times for a continuous adapted process `Y`:
`Y_t ≤ n` for `0 ≤ t ≤ τ_n`, and eventually `T ≤ τ_n`. -/
theorem q09b_stopping_seq {ℱ : Filtration ℝ mΩ} {Y : ℝ → Ω → ℝ} (hY : Adapted ℱ Y)
    (hc : ∀ ω, Continuous fun t => Y t ω) (hY0 : ∀ t, Measurable[ℱ t] (Y 0)) :
    ∃ τ : ℕ → Ω → WithTop ℝ, (∀ n, IsStoppingTime ℱ (τ n)) ∧
      (∀ (n : ℕ) (ω : Ω) (t : ℝ), 0 ≤ t → (t : WithTop ℝ) ≤ τ n ω → Y t ω ≤ n) ∧
      (∀ (ω : Ω) (T : ℝ), ∃ n0 : ℕ, ∀ n ≥ n0, (T : WithTop ℝ) ≤ τ n ω) := by
  classical
  obtain ⟨τ0, h1, h2, h3⟩ := exists_radius_times hY hc hY0
  have hne : ∀ n : ℕ, (Finset.range (n + 1)).Nonempty := fun n => ⟨0, by simp⟩
  refine ⟨fun n ω => (Finset.range (n + 1)).sup' (hne n) (fun k => τ0 k ω), ?_, ?_, ?_⟩
  · intro n i
    have : {ω | (Finset.range (n + 1)).sup' (hne n) (fun k => τ0 k ω) ≤ (i : WithTop ℝ)} =
        ⋂ k ∈ Finset.range (n + 1), {ω | τ0 k ω ≤ (i : WithTop ℝ)} := by
      ext ω
      simp [Finset.sup'_le_iff]
    rw [this]
    exact Finset.measurableSet_biInter _ fun k _ => h1 k i
  · intro n ω t ht hle
    obtain ⟨k, hk, hkle⟩ := (Finset.le_sup'_iff (hne n)).1 hle
    have := h2 k ω t ht hkle
    have hkn : (k : ℝ) ≤ n := by
      have : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      exact_mod_cast this
    linarith
  · intro ω T
    obtain ⟨n0, hn0⟩ := h3 ω T
    refine ⟨n0, fun n hn => hn0.trans ?_⟩
    exact Finset.le_sup' (fun k => τ0 k ω) (Finset.mem_range.2 (Nat.lt_succ_of_le hn))


/-- Joint-measurable functions of progressive processes are progressive. -/
theorem q09b_progressive_comp {ℱ : Filtration ℝ mΩ} {β E' : Type*} [MeasurableSpace β]
    [MeasurableSpace E'] (X : ℝ → Ω → E') (hX : IsProgressive ℱ X) (g : ℝ → E' → β)
    (hg : Measurable (Function.uncurry g)) : IsProgressive ℱ (fun s ω => g s (X s ω)) := by
  intro i
  have h2 : Measurable[Subtype.instMeasurableSpace.prod (ℱ i)]
      (fun p : Set.Iic i × Ω => ((p.1 : ℝ), X p.1 p.2)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk (hX i)
  exact hg.comp h2

/-- The stopped process at time `t` is the process at a time `r ≤ min t τ`. -/
theorem q09b_stopped_eq (τ : Ω → WithTop ℝ) (t : ℝ) (ω : Ω) :
    ∃ r : ℝ, r ≤ t ∧ (r : WithTop ℝ) ≤ τ ω ∧
      ∀ H : ℝ → Ω → ℝ, stoppedProcess H τ t ω = H r ω := by
  cases hτ : τ ω with
  | top => exact ⟨t, le_rfl, le_top, fun H => stoppedProcess_top_gen hτ t⟩
  | coe c =>
    refine ⟨min t c, min_le_left _ _, ?_, fun H => stoppedProcess_coe_gen hτ t⟩
    exact_mod_cast min_le_right t c

/-- Zero mean of the stopped local Itô integral. -/
theorem q09b_stopped_mean {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → ι → ℝ} (hW : IsBrownianFiltration P ℱ W') {Ψ : ℝ → Ω → ι → ℝ}
    (hΨ : IsProgressiveLocL2 P ℱ Ψ) {τ : Ω → WithTop ℝ} (hτ : IsStoppingTime ℱ τ)
    (hL2 : IsProgressiveL2 P ℱ (HRS.stopIntegrand Ψ τ)) (t : ℝ) :
    Integrable (stoppedProcess (localItoIntegral P ℱ W' Ψ) τ t) P ∧
      ∫ ω, stoppedProcess (localItoIntegral P ℱ W' Ψ) τ t ω ∂P = 0 := by
  have hM := isLocalItoIntegral_localItoIntegral hW hΨ
  have hst := hM.stopped τ hτ hL2
  have hae : stoppedProcess (localItoIntegral P ℱ W' Ψ) τ t =ᵐ[P]
      itoIntegral P ℱ W' (HRS.stopIntegrand Ψ τ) t := by
    filter_upwards [hst] with ω hω using hω t
  refine ⟨?_, ?_⟩
  · exact ((memLp_two_itoIntegral hW hL2 t).integrable one_le_two).congr hae.symm
  · rw [integral_congr_ae hae]
    exact integral_itoIntegral hW hL2 t

/-- The `L¹` bound for the time integral of the dominating process. -/
theorem q09b_J_bound {P : Measure Ω} [IsProbabilityMeasure P] (c c0 A : ℝ) (hc : 0 ≤ c)
    (hc0 : 0 ≤ c0) (hA : 0 ≤ A) {T : ℝ} (u : ℝ≥0 → Ω → ℝ)
    (hu : Measurable fun p : ℝ × Ω => u (Real.toNNReal p.1) p.2) (hu0 : ∀ s ω, 0 ≤ u s ω)
    (huE : ∀ s : ℝ≥0, (s : ℝ) ≤ T → ∫⁻ ω, ENNReal.ofReal (u s ω) ∂P ≤ ENNReal.ofReal A)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    Measurable (fun ω => ∫⁻ s in Set.Icc (0 : ℝ) t,
        ENNReal.ofReal (Real.exp (-(c * s)) * (c0 + u (Real.toNNReal s) ω))) ∧
    ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) t,
        ENNReal.ofReal (Real.exp (-(c * s)) * (c0 + u (Real.toNNReal s) ω))) ∂P
      ≤ ENNReal.ofReal ((c0 + A) * t) := by
  set F : Ω × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (Real.exp (-(c * p.2)) * (c0 + u (Real.toNNReal p.2) p.1)) with hF
  have hFm : Measurable F := by
    refine ENNReal.measurable_ofReal.comp ?_
    have h1 : Measurable fun p : Ω × ℝ => Real.exp (-(c * p.2)) :=
      (Real.measurable_exp.comp (measurable_snd.const_mul c).neg)
    have h2 : Measurable fun p : Ω × ℝ => u (Real.toNNReal p.2) p.1 :=
      hu.comp measurable_swap
    exact h1.mul (h2.const_add c0)
  refine ⟨hFm.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) t)), ?_⟩
  have hswap := lintegral_lintegral_swap (μ := P) (ν := volume.restrict (Set.Icc (0 : ℝ) t))
    (f := fun ω s => F (ω, s)) hFm.aemeasurable
  simp only [hF] at hswap
  rw [hswap]
  have hin : ∀ s ∈ Set.Icc (0 : ℝ) t,
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-(c * s)) * (c0 + u (Real.toNNReal s) ω)) ∂P
        ≤ ENNReal.ofReal (c0 + A) := by
    intro s hs
    have hsT : ((Real.toNNReal s : ℝ≥0) : ℝ) ≤ T := by
      rw [Real.coe_toNNReal _ hs.1]; exact hs.2.trans htT
    have hexp : Real.exp (-(c * s)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [hs.1]
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp (-(c * s)) * (c0 + u (Real.toNNReal s) ω)) ∂P
        ≤ ∫⁻ ω, (ENNReal.ofReal c0 + ENNReal.ofReal (u (Real.toNNReal s) ω)) ∂P := by
          refine lintegral_mono fun ω => ?_
          rw [← ENNReal.ofReal_add hc0 (hu0 _ _)]
          refine ENNReal.ofReal_le_ofReal ?_
          have := hu0 (Real.toNNReal s) ω
          nlinarith [Real.exp_pos (-(c * s))]
      _ = ENNReal.ofReal c0 + ∫⁻ ω, ENNReal.ofReal (u (Real.toNNReal s) ω) ∂P := by
          rw [lintegral_add_left measurable_const]
          simp
      _ ≤ ENNReal.ofReal c0 + ENNReal.ofReal A := by gcongr; exact huE _ hsT
      _ = ENNReal.ofReal (c0 + A) := (ENNReal.ofReal_add hc0 hA).symm
  calc ∫⁻ s in Set.Icc (0 : ℝ) t, (∫⁻ ω, ENNReal.ofReal (Real.exp (-(c * s)) *
          (c0 + u (Real.toNNReal s) ω)) ∂P)
      ≤ ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (c0 + A) :=
        setLIntegral_mono' measurableSet_Icc hin
    _ = ENNReal.ofReal ((c0 + A) * t) := by
        rw [setLIntegral_const, Real.volume_Icc, sub_zero,
          ENNReal.ofReal_mul (by linarith)]

/-- Itô moment bound (everywhere continuous version). -/
theorem q09b_moment_core {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → ι → ℝ} (hW : IsBrownianFiltration P ℱ W') {T : ℝ} (hT : 0 < T)
    (g : E → ℝ) (hg : ContDiff ℝ 2 g) (hg0 : ∀ x, 0 ≤ g x)
    (K : ℝ) (hK : ∀ x, ‖fderiv ℝ g x‖ ≤ K * (1 + g x))
    (σ : ι → E) (X : ℝ≥0 → Ω → E) (hXmeas : ∀ t, Measurable (X t))
    (hX0 : ∀ t : ℝ, Measurable[ℱ t] (X 0)) (hXprog : IsProgressive ℱ (ofNNRealTime X))
    (hXcont : ∀ ω, Continuous fun t => X t ω)
    (b : ℝ≥0 → Ω → E) (hb : IsProgressive ℱ (ofNNRealTime b))
    (hbint : ∀ᵐ ω ∂P, IntegrableOn (fun s : ℝ => b (Real.toNNReal s) ω) (Set.Icc 0 T))
    (hX : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      X t ω = X 0 ω + (∫ s in Set.Icc (0 : ℝ) t, b (Real.toNNReal s) ω) +
        ∑ k, (W' t ω k - W' 0 ω k) • σ k)
    (c c0 A m0 : ℝ) (hc : 0 ≤ c) (hc0 : 0 ≤ c0) (hA : 0 ≤ A) (hm0 : 0 ≤ m0)
    (u : ℝ≥0 → Ω → ℝ) (hu : IsProgressive ℱ (ofNNRealTime u)) (hu0 : ∀ s ω, 0 ≤ u s ω)
    (hdrift : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ) ≤ T →
      fderiv ℝ g (X s ω) (b s ω) + (1 / 2) * ∑ k, fderiv ℝ (fderiv ℝ g) (X s ω) (σ k) (σ k)
        ≤ c * g (X s ω) + c0 + u s ω)
    (huE : ∀ s : ℝ≥0, (s : ℝ) ≤ T → ∫⁻ ω, ENNReal.ofReal (u s ω) ∂P ≤ ENNReal.ofReal A)
    (hm : ∫⁻ ω, ENNReal.ofReal (g (X 0 ω)) ∂P ≤ ENNReal.ofReal m0) :
    ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      ∫⁻ ω, ENNReal.ofReal (g (X t ω)) ∂P ≤
        ENNReal.ofReal (Real.exp (c * T) * (m0 + (c0 + A) * T)) := by
  classical
  intro t0 ht0
  have hK0 : 0 ≤ K := by
    have h := hK 0
    have h1 : 0 ≤ ‖fderiv ℝ g 0‖ := norm_nonneg _
    have h2 : 0 < 1 + g 0 := by linarith [hg0 0]
    by_contra hneg
    push_neg at hneg
    nlinarith
  set f : ℝ → E → ℝ := fun t x => Real.exp (-(c * t)) * g x with hfdef
  have hfC : ContDiff ℝ 2 (Function.uncurry f) := by
    have h1 : ContDiff ℝ 2 (fun p : ℝ × E => Real.exp (-(c * p.1))) :=
      Real.contDiff_exp.comp (contDiff_const.mul contDiff_fst).neg
    exact h1.mul (hg.comp contDiff_snd)
  have hf : IsC12On T Set.univ f := IsC12On.of_contDiff T _ f hfC
  have hIto := ito_formula_additive hW hT.le f hf σ X hXmeas hX0 b hb hbint hX
  have hΦ : IsProgressiveLocL2E P ℱ (fun (_ : ℝ) (_ : Ω) => σ) := by
    refine ⟨isProgressive_const ℱ σ, fun T => ae_of_all _ fun ω => ?_⟩
    rw [lintegral_const]
    exact ENNReal.mul_lt_top (by simp) (by simp)
  set Ψ := itoIntegrand T Set.univ f (ofNNRealTime X) (fun _ _ => σ) with hΨdef
  have hΨ : IsProgressiveLocL2 P ℱ Ψ :=
    isProgressiveLocL2_itoIntegrand Set.univ isClosed_univ Set.univ (Set.Subset.refl _) f hf
      (ofNNRealTime X) hXprog
      (Filter.Eventually.of_forall fun ω => continuous_ofNNRealTime X ω (hXcont ω))
      (fun _ _ => σ) hΦ
  set M := localItoIntegral P ℱ W' Ψ with hMdef
  have hM : IsLocalItoIntegral P ℱ W' Ψ M := isLocalItoIntegral_localItoIntegral hW hΨ
  set drift : ℝ → Ω → ℝ :=
    itoDrift T f (ofNNRealTime X) (ofNNRealTime b) (fun _ _ => σ) with hdriftdef
  set Gp : ℝ → Ω → ℝ := fun r ω =>
    Real.exp (-(c * ((Real.toNNReal r : ℝ≥0) : ℝ))) * g (X (Real.toNNReal r) ω) with hGp
  have hGp0 : ∀ ω, Gp 0 ω = g (X 0 ω) := by
    intro ω; simp [Gp]
  have hreal : ∀ᵐ ω ∂P, IntegrableOn (fun s => drift s ω) (Set.Icc 0 T) ∧
      ∀ r : ℝ, r ≤ T → Gp r ω = Gp 0 ω + (∫ s in Set.Icc 0 r, drift s ω) + M r ω := by
    filter_upwards [hIto] with ω hω
    refine ⟨hω.1, fun r hr => ?_⟩
    rcases le_or_gt 0 r with h0 | h0
    · have := hω.2 (Real.toNNReal r) (by rw [Real.coe_toNNReal _ h0]; exact hr)
      rw [Real.coe_toNNReal _ h0] at this
      have e1 : Gp r ω = f r (X (Real.toNNReal r) ω) := by
        simp only [Gp, f, Real.coe_toNNReal _ h0]
      rw [e1, this, hGp0]
      simp [f]
    · have hr0 : Real.toNNReal r = 0 := Real.toNNReal_of_nonpos h0.le
      have e1 : Gp r ω = Gp 0 ω := by simp only [Gp, hr0, Real.toNNReal_zero]
      rw [e1, hM.zero r h0.le ω, Set.Icc_eq_empty (not_le.2 h0)]
      simp
  have hdr : ∀ᵐ ω ∂P, ∀ s ∈ Set.Icc (0 : ℝ) T,
      drift s ω ≤ Real.exp (-(c * s)) * (c0 + u (Real.toNNReal s) ω) := by
    filter_upwards [hdrift] with ω hω s hs
    have hsT : ((Real.toNNReal s : ℝ≥0) : ℝ) ≤ T := by
      rw [Real.coe_toNNReal _ hs.1]; exact hs.2
    have h1 := hω (Real.toNNReal s) hsT
    have hv := q09b_drift_value hT hg c hs (X (Real.toNNReal s) ω) (b (Real.toNNReal s) ω) σ
    have e : drift s ω = Real.exp (-(c * s)) * (-c * g (X (Real.toNNReal s) ω) +
        fderiv ℝ g (X (Real.toNNReal s) ω) (b (Real.toNNReal s) ω) +
        (1 / 2) * ∑ k, fderiv ℝ (fderiv ℝ g) (X (Real.toNNReal s) ω) (σ k) (σ k)) := hv
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    linarith
  -- localising times
  set Y : ℝ → Ω → ℝ := fun t ω => g (X (Real.toNNReal t) ω) with hYdef
  have hYad : Adapted ℱ Y := fun t => hg.continuous.measurable.comp (hXprog.adapted t)
  have hYc : ∀ ω, Continuous fun t => Y t ω := fun ω =>
    hg.continuous.comp ((hXcont ω).comp continuous_real_toNNReal)
  have hY0 : ∀ t, Measurable[ℱ t] (Y 0) := fun t => by
    have : Y 0 = fun ω => g (X 0 ω) := by funext ω; simp [Y]
    rw [this]; exact hg.continuous.measurable.comp (hX0 t)
  obtain ⟨τ, hτ, hτle, hτex⟩ := q09b_stopping_seq hYad hYc hY0
  have hfd : ∀ s x, fderiv ℝ (f s) x = Real.exp (-(c * s)) • fderiv ℝ g x := by
    intro s x
    show fderiv ℝ (fun x => Real.exp (-(c * s)) * g x) x = _
    exact fderiv_const_mul ((hg.differentiable (by norm_num)) x) _
  have hL2 : ∀ n : ℕ, IsProgressiveL2 P ℱ (HRS.stopIntegrand Ψ (τ n)) := by
    intro n
    refine IsProgressiveL2.of_bounded P (isProgressive_stopIntegrand hΨ.prog (hτ n))
      (K * (1 + n) * ∑ j, ‖σ j‖) ?_
    intro s ω k
    have hB : 0 ≤ K * (1 + n) * ∑ j, ‖σ j‖ := by positivity
    by_cases h : (s : WithTop ℝ) ≤ τ n ω
    · by_cases hs : s ∈ Set.Icc (0 : ℝ) T
      · have e : HRS.stopIntegrand Ψ (τ n) s ω k =
            Real.exp (-(c * s)) * fderiv ℝ g (X (Real.toNNReal s) ω) (σ k) := by
          simp [HRS.stopIntegrand, Ψ, itoIntegrand, Set.indicator, h, hs, hfd]
        rw [e]
        have hgx : g (X (Real.toNNReal s) ω) ≤ n := hτle n ω s hs.1 h
        have hexp : Real.exp (-(c * s)) ≤ 1 := by
          rw [Real.exp_le_one_iff]; nlinarith [hs.1]
        have h1 : |fderiv ℝ g (X (Real.toNNReal s) ω) (σ k)| ≤
            K * (1 + g (X (Real.toNNReal s) ω)) * ‖σ k‖ :=
          (le_of_eq (Real.norm_eq_abs _).symm).trans
            (((fderiv ℝ g (X (Real.toNNReal s) ω)).le_opNorm (σ k)).trans
              (mul_le_mul_of_nonneg_right (hK _) (norm_nonneg _)))
        have h2 : ‖σ k‖ ≤ ∑ j, ‖σ j‖ :=
          Finset.single_le_sum (f := fun j => ‖σ j‖) (fun _ _ => norm_nonneg _)
            (Finset.mem_univ k)
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        calc Real.exp (-(c * s)) * |fderiv ℝ g (X (Real.toNNReal s) ω) (σ k)|
            ≤ 1 * (K * (1 + g (X (Real.toNNReal s) ω)) * ‖σ k‖) :=
              mul_le_mul hexp h1 (abs_nonneg _) zero_le_one
          _ ≤ K * (1 + n) * ∑ j, ‖σ j‖ := by
              rw [one_mul]
              have hg1 : 0 ≤ g (X (Real.toNNReal s) ω) := hg0 _
              have : K * (1 + g (X (Real.toNNReal s) ω)) ≤ K * (1 + n) := by nlinarith
              calc K * (1 + g (X (Real.toNNReal s) ω)) * ‖σ k‖
                  ≤ K * (1 + n) * ‖σ k‖ := mul_le_mul_of_nonneg_right this (norm_nonneg _)
                _ ≤ K * (1 + n) * ∑ j, ‖σ j‖ :=
                    mul_le_mul_of_nonneg_left h2 (by positivity)
      · have e : HRS.stopIntegrand Ψ (τ n) s ω k = 0 := by
          simp [HRS.stopIntegrand, Ψ, itoIntegrand, Set.indicator, h, hs]
        rw [e]; simpa using hB
    · have e : HRS.stopIntegrand Ψ (τ n) s ω k = 0 := by
        simp [HRS.stopIntegrand, Set.indicator, h]
      rw [e]; simpa using hB
  have hGprog : IsProgressive ℱ Gp := by
    have hm : Measurable (Function.uncurry fun (r : ℝ) (x : E) =>
        Real.exp (-(c * ((Real.toNNReal r : ℝ≥0) : ℝ))) * g x) := by
      have h1 : Measurable fun p : ℝ × E =>
          Real.exp (-(c * ((Real.toNNReal p.1 : ℝ≥0) : ℝ))) :=
        Real.measurable_exp.comp ((measurable_coe_nnreal_real.comp
          (measurable_real_toNNReal.comp measurable_fst)).const_mul c).neg
      exact h1.mul (hg.continuous.measurable.comp measurable_snd)
    exact q09b_progressive_comp (ℱ := ℱ) (ofNNRealTime X) hXprog _ hm
  have key : ∀ t : ℝ, 0 ≤ t → t ≤ T → ∀ n : ℕ,
      Measurable (stoppedProcess Gp (τ n) t) ∧
      ∫⁻ ω, ENNReal.ofReal (stoppedProcess Gp (τ n) t ω) ∂P ≤
        ENNReal.ofReal (m0 + (c0 + A) * t) := by
    intro t ht0 htT n
    have hZm : Measurable (stoppedProcess Gp (τ n) t) :=
      ((isProgressive_stoppedProcess_E hGprog (hτ n)).adapted t).mono (ℱ.le t) le_rfl
    have hG0m : Measurable fun ω => g (X 0 ω) := hg.continuous.measurable.comp (hXmeas 0)
    have hG0nn : ∀ ω, 0 ≤ g (X 0 ω) := fun ω => hg0 _
    have hG0lint : ∫⁻ ω, ENNReal.ofReal (g (X 0 ω)) ∂P ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hm
    have hG0int : Integrable (fun ω => g (X 0 ω)) P := by
      refine ⟨hG0m.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hG0nn)]
      exact lt_top_iff_ne_top.2 hG0lint
    have hG0le : ∫ ω, g (X 0 ω) ∂P ≤ m0 := by
      rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hG0nn)
        hG0m.aestronglyMeasurable]
      exact ENNReal.toReal_le_of_le_ofReal hm0 hm
    have hZb : ∀ ω, 0 ≤ stoppedProcess Gp (τ n) t ω ∧
        stoppedProcess Gp (τ n) t ω ≤ n + g (X 0 ω) := by
      intro ω
      obtain ⟨r, hrt, hrτ, hH⟩ := q09b_stopped_eq (τ n) t ω
      rw [hH Gp]
      have hnn : 0 ≤ Gp r ω := mul_nonneg (Real.exp_pos _).le (hg0 _)
      refine ⟨hnn, ?_⟩
      rcases le_or_gt 0 r with h0 | h0
      · have h1 : g (X (Real.toNNReal r) ω) ≤ n := hτle n ω r h0 hrτ
        have h2 : Real.exp (-(c * ((Real.toNNReal r : ℝ≥0) : ℝ))) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          have := (Real.toNNReal r).2
          nlinarith
        have h3 : Gp r ω ≤ g (X (Real.toNNReal r) ω) := by
          calc Gp r ω = Real.exp (-(c * ((Real.toNNReal r : ℝ≥0) : ℝ))) *
                g (X (Real.toNNReal r) ω) := rfl
            _ ≤ 1 * g (X (Real.toNNReal r) ω) :=
                mul_le_mul_of_nonneg_right h2 (hg0 _)
            _ = _ := one_mul _
        linarith [hg0 (X 0 ω)]
      · have hr0 : Real.toNNReal r = 0 := Real.toNNReal_of_nonpos h0.le
        have h3 : Gp r ω = g (X 0 ω) := by
          show Real.exp (-(c * ((Real.toNNReal r : ℝ≥0) : ℝ))) * g (X (Real.toNNReal r) ω) = _
          rw [hr0]; simp
        rw [h3]
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hZint : Integrable (stoppedProcess Gp (τ n) t) P := by
      refine Integrable.mono' ((integrable_const (n : ℝ)).add hG0int) hZm.aestronglyMeasurable
        (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hZb ω).1]
      exact (hZb ω).2
    obtain ⟨hMint, hM0⟩ := q09b_stopped_mean hW hΨ (hτ n) (hL2 n) t
    obtain ⟨hBlm, hBlint⟩ := q09b_J_bound c c0 A hc hc0 hA u (measurable_of_progressive hu) hu0
      huE ht0 htT
    set Bl : Ω → ℝ≥0∞ := fun ω => ∫⁻ s in Set.Icc (0 : ℝ) t,
      ENNReal.ofReal (Real.exp (-(c * s)) * (c0 + u (Real.toNNReal s) ω)) with hBl
    have hBlfin : ∫⁻ ω, Bl ω ∂P ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hBlint
    set J : Ω → ℝ := fun ω => (Bl ω).toReal with hJ
    have hJint : Integrable J P := integrable_toReal_of_lintegral_ne_top hBlm.aemeasurable hBlfin
    have hJle : ∫ ω, J ω ∂P ≤ (c0 + A) * t := by
      rw [hJ, integral_toReal hBlm.aemeasurable (ae_lt_top hBlm hBlfin)]
      exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg (add_nonneg hc0 hA) ht0) hBlint
    have hJnn : ∀ ω, 0 ≤ J ω := fun ω => ENNReal.toReal_nonneg
    have hbm : Measurable fun p : ℝ × Ω =>
        Real.exp (-(c * p.1)) * (c0 + u (Real.toNNReal p.1) p.2) :=
      (Real.measurable_exp.comp (measurable_fst.const_mul c).neg).mul
        ((measurable_of_progressive hu).const_add c0)
    have hpath : ∀ᵐ ω ∂P, stoppedProcess Gp (τ n) t ω ≤
        g (X 0 ω) + J ω + stoppedProcess M (τ n) t ω := by
      filter_upwards [hreal, hdr, ae_lt_top hBlm hBlfin] with ω hω hd hBω
      obtain ⟨r, hrt, hrτ, hH⟩ := q09b_stopped_eq (τ n) t ω
      rw [hH Gp, hH M]
      have hrT : r ≤ T := hrt.trans htT
      rw [hω.2 r hrT, hGp0]
      have hI : ∫ s in Set.Icc 0 r, drift s ω ≤ J ω := by
        rcases le_or_gt 0 r with h0 | h0
        · set bnd : ℝ → ℝ := fun s => Real.exp (-(c * s)) * (c0 + u (Real.toNNReal s) ω) with hbnd
          have hbnn : ∀ s, 0 ≤ bnd s := fun s =>
            mul_nonneg (Real.exp_pos _).le (add_nonneg hc0 (hu0 _ _))
          have hbmeas : Measurable bnd := hbm.comp (measurable_id.prodMk measurable_const)
          have hbint : IntegrableOn bnd (Set.Icc 0 t) := by
            refine ⟨hbmeas.aestronglyMeasurable, ?_⟩
            rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hbnn)]
            exact hBω
          have hJeq : J ω = ∫ s in Set.Icc 0 t, bnd s := by
            rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hbnn)
              hbmeas.aestronglyMeasurable]
          rw [hJeq]
          have hdint : IntegrableOn (fun s => drift s ω) (Set.Icc 0 r) :=
            hω.1.mono_set (Set.Icc_subset_Icc le_rfl hrT)
          calc ∫ s in Set.Icc 0 r, drift s ω ≤ ∫ s in Set.Icc 0 r, bnd s :=
                setIntegral_mono_on hdint (hbint.mono_set (Set.Icc_subset_Icc le_rfl hrt))
                  measurableSet_Icc (fun s hs => hd s ⟨hs.1, hs.2.trans hrT⟩)
            _ ≤ ∫ s in Set.Icc 0 t, bnd s :=
                setIntegral_mono_set hbint (Filter.Eventually.of_forall hbnn)
                  (Set.Icc_subset_Icc le_rfl hrt).eventuallyLE
        · rw [Set.Icc_eq_empty (not_le.2 h0)]
          simpa using hJnn ω
      linarith
    have hGJ : Integrable (fun ω => g (X 0 ω) + J ω) P := hG0int.add hJint
    have hRHSint : Integrable (fun ω => g (X 0 ω) + J ω + stoppedProcess M (τ n) t ω) P :=
      hGJ.add hMint
    have hmono := integral_mono_ae hZint hRHSint hpath
    rw [integral_add hGJ hMint, integral_add hG0int hJint, hM0] at hmono
    refine ⟨hZm, ?_⟩
    rw [← ofReal_integral_eq_lintegral_ofReal hZint
      (Filter.Eventually.of_forall fun ω => (hZb ω).1)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have ht0' : (0 : ℝ) ≤ t0 := t0.2
  have hfat : ∫⁻ ω, ENNReal.ofReal (Gp (t0 : ℝ) ω) ∂P ≤
      ENNReal.ofReal (m0 + (c0 + A) * t0) := by
    have hev : ∀ ω, ∀ᶠ n in atTop, stoppedProcess Gp (τ n) (t0 : ℝ) ω = Gp (t0 : ℝ) ω := by
      intro ω
      obtain ⟨n0, hn0⟩ := hτex ω T
      filter_upwards [eventually_ge_atTop n0] with n hn
      refine MeasureTheory.stoppedProcess_eq_of_le ?_
      exact (by exact_mod_cast ht0 : ((t0 : ℝ) : WithTop ℝ) ≤ (T : WithTop ℝ)).trans (hn0 n hn)
    calc ∫⁻ ω, ENNReal.ofReal (Gp (t0 : ℝ) ω) ∂P
        = ∫⁻ ω, Filter.liminf (fun n => ENNReal.ofReal (stoppedProcess Gp (τ n) (t0 : ℝ) ω))
            atTop ∂P := by
          refine lintegral_congr fun ω => ?_
          have : ∀ᶠ n in atTop, ENNReal.ofReal (stoppedProcess Gp (τ n) (t0 : ℝ) ω) =
              ENNReal.ofReal (Gp (t0 : ℝ) ω) := (hev ω).mono fun n h => by rw [h]
          rw [Filter.liminf_congr this, Filter.liminf_const]
      _ ≤ Filter.liminf (fun n => ∫⁻ ω, ENNReal.ofReal (stoppedProcess Gp (τ n) (t0 : ℝ) ω) ∂P)
            atTop :=
          lintegral_liminf_le (fun n => ENNReal.measurable_ofReal.comp ((key t0 ht0' ht0 n).1))
      _ ≤ ENNReal.ofReal (m0 + (c0 + A) * t0) :=
          Filter.liminf_le_of_frequently_le'
            (Filter.Eventually.frequently
              (Filter.Eventually.of_forall fun n => (key t0 ht0' ht0 n).2))
  have hgt : ∀ ω, ENNReal.ofReal (g (X t0 ω)) =
      ENNReal.ofReal (Real.exp (c * t0)) * ENNReal.ofReal (Gp (t0 : ℝ) ω) := by
    intro ω
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    simp only [Gp, Real.toNNReal_coe]
    rw [← mul_assoc, ← Real.exp_add]
    simp
  have hm1 : 0 ≤ m0 + (c0 + A) * t0 := by positivity
  calc ∫⁻ ω, ENNReal.ofReal (g (X t0 ω)) ∂P
      = ENNReal.ofReal (Real.exp (c * t0)) * ∫⁻ ω, ENNReal.ofReal (Gp (t0 : ℝ) ω) ∂P := by
        simp_rw [hgt]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (Real.exp (c * t0)) * ENNReal.ofReal (m0 + (c0 + A) * t0) := by
        gcongr
    _ = ENNReal.ofReal (Real.exp (c * t0) * (m0 + (c0 + A) * t0)) :=
        (ENNReal.ofReal_mul (Real.exp_pos _).le).symm
    _ ≤ ENNReal.ofReal (Real.exp (c * T) * (m0 + (c0 + A) * T)) := by
        refine ENNReal.ofReal_le_ofReal (mul_le_mul (Real.exp_le_exp.2 (by nlinarith))
          (by nlinarith [add_nonneg hc0 hA]) hm1 (Real.exp_pos _).le)

/-- Itô moment bound: `E g(X_t) ≤ e^{cT}(E g(X_0) + (c₀+A)T)` (a.s. continuous paths). -/
theorem q09b_moment_bound {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → ι → ℝ} (hW : IsBrownianFiltration P ℱ W') {T : ℝ} (hT : 0 < T)
    (g : E → ℝ) (hg : ContDiff ℝ 2 g) (hg0 : ∀ x, 0 ≤ g x)
    (K : ℝ) (hK : ∀ x, ‖fderiv ℝ g x‖ ≤ K * (1 + g x))
    (σ : ι → E) (X : ℝ≥0 → Ω → E) (hXmeas : ∀ t, Measurable (X t))
    (hX0 : ∀ t : ℝ, Measurable[ℱ t] (X 0)) (hXprog : IsProgressive ℱ (ofNNRealTime X))
    (hXcont : ∀ᵐ ω ∂P, Continuous fun t => X t ω)
    (b : ℝ≥0 → Ω → E) (hb : IsProgressive ℱ (ofNNRealTime b))
    (hbint : ∀ᵐ ω ∂P, IntegrableOn (fun s : ℝ => b (Real.toNNReal s) ω) (Set.Icc 0 T))
    (hX : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      X t ω = X 0 ω + (∫ s in Set.Icc (0 : ℝ) t, b (Real.toNNReal s) ω) +
        ∑ k, (W' t ω k - W' 0 ω k) • σ k)
    (c c0 A m0 : ℝ) (hc : 0 ≤ c) (hc0 : 0 ≤ c0) (hA : 0 ≤ A) (hm0 : 0 ≤ m0)
    (u : ℝ≥0 → Ω → ℝ) (hu : IsProgressive ℱ (ofNNRealTime u)) (hu0 : ∀ s ω, 0 ≤ u s ω)
    (hdrift : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ) ≤ T →
      fderiv ℝ g (X s ω) (b s ω) + (1 / 2) * ∑ k, fderiv ℝ (fderiv ℝ g) (X s ω) (σ k) (σ k)
        ≤ c * g (X s ω) + c0 + u s ω)
    (huE : ∀ s : ℝ≥0, (s : ℝ) ≤ T → ∫⁻ ω, ENNReal.ofReal (u s ω) ∂P ≤ ENNReal.ofReal A)
    (hm : ∫⁻ ω, ENNReal.ofReal (g (X 0 ω)) ∂P ≤ ENNReal.ofReal m0) :
    ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      ∫⁻ ω, ENNReal.ofReal (g (X t ω)) ∂P ≤
        ENNReal.ofReal (Real.exp (c * T) * (m0 + (c0 + A) * T)) := by
  classical
  obtain ⟨N0, hN0m, hN00, hN0⟩ : ∃ N0 : Set Ω, MeasurableSet N0 ∧ P N0 = 0 ∧
      ∀ ω ∉ N0, Continuous fun t => X t ω := by
    refine ⟨toMeasurable P {ω | ¬ Continuous fun t => X t ω}, measurableSet_toMeasurable _ _,
      ?_, ?_⟩
    · rw [measure_toMeasurable]; exact ae_iff.1 hXcont
    · intro ω hω; by_contra hc; exact hω (subset_toMeasurable _ _ hc)
  have hNt : ∀ t, MeasurableSet[ℱ t] N0 := fun t => hW.complete t N0 hN0m hN00
  have hae : ∀ᵐ ω ∂P, ω ∉ N0 := by rw [ae_iff]; simpa using hN00
  let X' : ℝ≥0 → Ω → E := fun t ω => if ω ∈ N0 then 0 else X t ω
  have hX'eq : ∀ᵐ ω ∂P, ∀ t, X' t ω = X t ω := by
    filter_upwards [hae] with ω hω t
    simp [X', hω]
  have hXmeas' : ∀ t, Measurable (X' t) := fun t =>
    Measurable.ite hN0m measurable_const (hXmeas t)
  have hX0' : ∀ t : ℝ, Measurable[ℱ t] (X' 0) := fun t =>
    Measurable.ite (m := ℱ t) (hNt t) measurable_const (hX0 t)
  have hXprog' : IsProgressive ℱ (ofNNRealTime X') := by
    intro i
    letI : MeasurableSpace (Set.Iic i × Ω) := Subtype.instMeasurableSpace.prod (ℱ i)
    have hs : MeasurableSet {p : Set.Iic i × Ω | p.2 ∈ N0} :=
      (measurable_snd (α := Set.Iic i) (β := Ω)) (hNt i)
    exact Measurable.ite hs measurable_const (hXprog i)
  have hXcont' : ∀ ω, Continuous fun t => X' t ω := by
    intro ω
    by_cases hω : ω ∈ N0
    · simp only [X', hω, if_true]; exact continuous_const
    · simp only [X', hω, if_false]; exact hN0 ω hω
  have hX' : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      X' t ω = X' 0 ω + (∫ s in Set.Icc (0 : ℝ) t, b (Real.toNNReal s) ω) +
        ∑ k, (W' t ω k - W' 0 ω k) • σ k := by
    filter_upwards [hX, hae] with ω h1 hω t ht
    simp only [X', hω, if_false]
    exact h1 t ht
  have hdrift' : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ) ≤ T →
      fderiv ℝ g (X' s ω) (b s ω) + (1 / 2) * ∑ k, fderiv ℝ (fderiv ℝ g) (X' s ω) (σ k) (σ k)
        ≤ c * g (X' s ω) + c0 + u s ω := by
    filter_upwards [hdrift, hae] with ω h1 hω s hs
    simp only [X', hω, if_false]
    exact h1 s hs
  have hm' : ∫⁻ ω, ENNReal.ofReal (g (X' 0 ω)) ∂P ≤ ENNReal.ofReal m0 := by
    refine le_trans (le_of_eq (lintegral_congr_ae ?_)) hm
    filter_upwards [hX'eq] with ω h
    rw [h 0]
  have key := q09b_moment_core hW hT g hg hg0 K hK σ X' hXmeas' hX0' hXprog' hXcont' b hb hbint
    hX' c c0 A m0 hc hc0 hA hm0 u hu hu0 hdrift' huE hm'
  intro t ht
  refine le_trans (le_of_eq (lintegral_congr_ae ?_)) (key t ht)
  filter_upwards [hX'eq] with ω h
  rw [h t]

end HRS.Whole.Q09B
