import HRS.MC.E213U10R
import HRS.MC.E213U5a

/-!
# Packet e213u10, part S: `near_estimate`

Statement copied verbatim from `HRS.MC.E213Plan.near_estimate`; checked equal in `HRS/MC/E213U10Tie.lean`.

With `L = Rw + T`, `b = max (a - Rw) 0`: part R gives, for each `N ≥ 2`, `a`, `Φ`, the bound of the error by
`K₁ W₁ + K₂ W₂` (for the sups `W₁, W₂` of `chaos_conv` at window length `L`) once `W₁ < ∞`; the finitely many `N` with
`W₁ + W₂ ≥ 1` are handled by the absolute bounds, the Gaussian side being bounded by comparison with a large `N`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E213U10

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ} {S : PreparedData d} {β₀ m : ℝ}

theorem u10_abs_sub_le (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  rcases abs_cases x with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rcases abs_cases y with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
    rcases abs_cases (x - y) with ⟨h3, _⟩ | ⟨h3, _⟩ <;> linarith

theorem near_estimate_proof (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (gd : GaussData S β₀ hE)
    (fam : PrepFamily S β₀ hE) (Rw : ℝ) (hRw : 0 < Rw) :
    ∃ (C : ℝ) (e : ℕ → ℝ), Tendsto e atTop (𝓝 0) ∧
      ∀ (N : ℕ), 2 ≤ N → ∀ (a : ℝ) (ha : 0 ≤ a), ∀ Φ ∈ CbUnitBall (PathSpace d m T) 5,
        |∫ ω, rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 (fam.P N) (fam.X N) ω)
            (nearCoef (max (a - Rw) 0) (fun v => quadFieldAt m (regime S β₀ hE).D.s
              (fun t => withDensityReal ((regime S β₀ hE).ρ t)) (fam.P N) (fam.X N) v ω)) ∂(fam.P N) -
          ∫ ω, rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
            (nearCoef (max (a - Rw) 0) (fun v => NegSobolev.embed m (gd.B v ω))) ∂gd.P₀| +
        (1 / 2) * |∫ ω, rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 (fam.P N) (fam.X N) ω)
            (nearCoef (max (a - Rw) 0) (fun v => etaE m ((fam.X N) v.toNNReal ω)
              (withDensityReal ((regime S β₀ hE).ρ v)))) ∂(fam.P N) -
          ∫ ω, rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
            (nearCoef (max (a - Rw) 0) (fun v => NegSobolev.embed m (gd.η v ω))) ∂gd.P₀| ≤ C * e N := by
  classical
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Rw + T := ⟨_, rfl⟩
  have hL : 0 < L := by rw [hLdef]; linarith
  obtain ⟨CD, hCDpos, hCD⟩ := HRS.MC.E213U1.winDrift_near_proof hE T hT
  obtain ⟨CJ, hCJpos, hCJ⟩ := HRS.MC.E213U2.winJ_near_proof hE T hT Rw hRw
  obtain ⟨CY, hCY1, hCY⟩ := u10_winPred_norm_le hE T hT
  obtain ⟨Cq, hCq⟩ := HRS.MC.Sec7.S7FCF5N.fcf5_F6c_B_moments_proof (regime S β₀ hE) (rLvl d) rfl L hL 2
    (by norm_num)
  obtain ⟨Cf, hCf⟩ := HRS.MC.Sec7.S7FCF5R.fcf5_E3b_F5_zeta_moments_proof (regime S β₀ hE) (rLvl d) rfl L hL 2
    (by norm_num)
  obtain ⟨Mq, hMq0, hMq⟩ : ∃ M : ℝ, 0 ≤ M ∧ Cq ≤ M ^ 2 :=
    ⟨Real.sqrt (max Cq 0), Real.sqrt_nonneg _, by rw [Real.sq_sqrt (le_max_right _ _)]; exact le_max_left _ _⟩
  obtain ⟨Mf, hMf0, hMf⟩ : ∃ M : ℝ, 0 ≤ M ∧ Cf ≤ M ^ 2 :=
    ⟨Real.sqrt (max Cf 0), Real.sqrt_nonneg _, by rw [Real.sq_sqrt (le_max_right _ _)]; exact le_max_left _ _⟩
  obtain ⟨hc1, hc2⟩ := HRS.MC.E213U5.chaos_conv_proof gd fam
  have hc1L := hc1 L hL 2 (by norm_num)
  have hc2L := hc2 L hL
  -- handles
  obtain ⟨W1f, hW1f⟩ : ∃ f : ℕ → ℝ → ℝ≥0∞, ∀ N b, f N b = wassersteinE 2
      (law (fam.P N) (pairN (rLvl d) L b (regime S β₀ hE).D.s (regime S β₀ hE).ρ (fam.P N) (fam.X N)))
      (law gd.P₀ (pairLim (rLvl d) L b gd.η gd.B)) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨W2f, hW2f⟩ : ∃ f : ℕ → ℝ → ℝ≥0∞, ∀ N b, f N b = wassersteinE 2
      (law (fam.P N) (HRS.Main.windowFluc (rLvl d) L b (Real.sqrt N) (fam.X N) (regime S β₀ hE).ρ))
      (law gd.P₀ (procWin (rLvl d) L b gd.η)) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨W1, hW1⟩ : ∃ W : ℕ → ℝ≥0∞, ∀ N, W N = ⨆ a : {a : ℝ // 0 ≤ a}, W1f N a.1 := ⟨_, fun _ => rfl⟩
  obtain ⟨W2, hW2⟩ : ∃ W : ℕ → ℝ≥0∞, ∀ N, W N = ⨆ a : {a : ℝ // 0 ≤ a}, W2f N a.1 := ⟨_, fun _ => rfl⟩
  have hc1' : Tendsto W1 atTop (𝓝 0) := by
    have : W1 = fun N : ℕ => ⨆ a : {a : ℝ // 0 ≤ a}, wassersteinE 2
        (law (fam.P N) (pairN (rLvl d) L a.1 (regime S β₀ hE).D.s (regime S β₀ hE).ρ (fam.P N) (fam.X N)))
        (law gd.P₀ (pairLim (rLvl d) L a.1 gd.η gd.B)) := by
      funext N
      rw [hW1]
      exact iSup_congr fun a => hW1f N a.1
    rw [this]
    exact hc1L
  have hc2' : Tendsto W2 atTop (𝓝 0) := by
    have : W2 = fun N : ℕ => ⨆ a : {a : ℝ // 0 ≤ a}, wassersteinE 2
        (law (fam.P N) (HRS.Main.windowFluc (rLvl d) L a.1 (Real.sqrt N) (fam.X N) (regime S β₀ hE).ρ))
        (law gd.P₀ (procWin (rLvl d) L a.1 gd.η)) := by
      funext N
      rw [hW2]
      exact iSup_congr fun a => hW2f N a.1
    rw [this]
    exact hc2L
  have hle1 : ∀ N b, 0 ≤ b → W1f N b ≤ W1 N := fun N b hb => by
    rw [hW1]; exact le_iSup (fun a : {a : ℝ // 0 ≤ a} => W1f N a.1) ⟨b, hb⟩
  have hle2 : ∀ N b, 0 ≤ b → W2f N b ≤ W2 N := fun N b hb => by
    rw [hW2]; exact le_iSup (fun a : {a : ℝ // 0 ≤ a} => W2f N a.1) ⟨b, hb⟩
  obtain ⟨PAf, hPAf⟩ : ∃ f : ℕ → (a : ℝ) → 0 ≤ a → (PathSpace d m T → ℝ) → ℝ, ∀ N a ha Φ, f N a ha Φ =
      ∫ ω, rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 (fam.P N) (fam.X N) ω)
        (nearCoef (max (a - Rw) 0) (fun v => quadFieldAt m (regime S β₀ hE).D.s
          (fun t => withDensityReal ((regime S β₀ hE).ρ t)) (fam.P N) (fam.X N) v ω)) ∂(fam.P N) :=
    ⟨_, fun _ _ _ _ => rfl⟩
  obtain ⟨GAf, hGAf⟩ : ∃ f : (a : ℝ) → 0 ≤ a → (PathSpace d m T → ℝ) → ℝ, ∀ a ha Φ, f a ha Φ =
      ∫ ω, rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
        (nearCoef (max (a - Rw) 0) (fun v => NegSobolev.embed m (gd.B v ω))) ∂gd.P₀ :=
    ⟨_, fun _ _ _ => rfl⟩
  obtain ⟨PJf, hPJf⟩ : ∃ f : ℕ → (a : ℝ) → 0 ≤ a → (PathSpace d m T → ℝ) → ℝ, ∀ N a ha Φ, f N a ha Φ =
      ∫ ω, rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 (fam.P N) (fam.X N) ω)
        (nearCoef (max (a - Rw) 0) (fun v => etaE m ((fam.X N) v.toNNReal ω)
          (withDensityReal ((regime S β₀ hE).ρ v)))) ∂(fam.P N) :=
    ⟨_, fun _ _ _ _ => rfl⟩
  obtain ⟨GJf, hGJf⟩ : ∃ f : (a : ℝ) → 0 ≤ a → (PathSpace d m T → ℝ) → ℝ, ∀ a ha Φ, f a ha Φ =
      ∫ ω, rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
        (nearCoef (max (a - Rw) 0) (fun v => NegSobolev.embed m (gd.η v ω))) ∂gd.P₀ :=
    ⟨_, fun _ _ _ => rfl⟩
  -- the pointwise estimate
  have key : ∀ N : ℕ, 2 ≤ N → ∀ (a : ℝ) (ha : 0 ≤ a), ∀ Φ ∈ CbUnitBall (PathSpace d m T) 5,
      ∃ mm : PathSpace d (rLvl d) L, ENNReal.ofReal ‖mm‖ ≤ W2f N (max (a - Rw) 0) ∧
        |PAf N a ha Φ| ≤ CD * Real.sqrt L * Mq ∧ |PJf N a ha Φ| ≤ CJ * L * Mf ∧
        (W1f N (max (a - Rw) 0) ≠ ⊤ →
          |PAf N a ha Φ - GAf a ha Φ| ≤
            CD * Real.sqrt L * ((CY * Mq + 1) * (W1f N (max (a - Rw) 0)).toReal) ∧
          |PJf N a ha Φ - GJf a ha Φ| ≤
            CJ * L * ((CY * Mf + 1) * (W1f N (max (a - Rw) 0)).toReal + ‖mm‖)) := by
    intro N hN a ha Φ hΦ
    have hb : 0 ≤ max (a - Rw) 0 := le_max_right _ _
    have hba : max (a - Rw) 0 ≤ a := max_le (by linarith) ha
    have hab : a - max (a - Rw) 0 ≤ Rw := by
      rcases le_total (a - Rw) 0 with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    have hH : a + T ≤ max (a - Rw) 0 + L := by
      rw [hLdef]; have := le_max_left (a - Rw) 0; linarith
    have hΦ1 : MemCb 5 Φ := ⟨hΦ.1, hΦ.2.1⟩
    have hΦ2 : cbNorm 5 Φ ≤ 1 := hΦ.2.2
    have hN1 : 1 ≤ N := by omega
    have hCDa : U10_DriftNear hE T a ha (max (a - Rw) 0) CD := hCD a ha _ hb
    have hJa : U10_JNear hE T a ha (max (a - Rw) 0) CJ := fun zr hzm M hM u u' hu huu hu' =>
      (hCJ a ha _ hb hba hab zr hzm M hM u u' hu huu hu').2
    have hCYa : U10_PredBound hE T a ha CY := hCY a ha
    have hq := hCq (max (a - Rw) 0) hb N hN (fam.P N) (fam.X₀ N) (fam.W N) (fam.X N) (fam.hreal N hN1)
    have hf := hCf (max (a - Rw) 0) hb N hN (fam.P N) (fam.X₀ N) (fam.W N) (fam.X N) (fam.hreal N hN1)
    obtain ⟨mm, h1, h2, h3, h4⟩ := u10_near_pointwise hE gd fam T hT a ha Φ hΦ1 hΦ2 _ L hb hba hL hH CD CJ CY
      hCDpos.le hCJpos.le (by linarith) hCDa hJa hCYa N hN Mq Mf hMq0 hMf0 ⟨hq.1, hq.2.trans hMq⟩
      ⟨hf.2.1, hf.2.2.trans hMf⟩
    refine ⟨mm, ?_, ?_, ?_, ?_⟩
    · rw [hW2f]; exact h1
    · rw [hPAf]; exact h2
    · rw [hPJf]; exact h3
    · intro hW
      rw [hW1f] at hW
      have h5 := h4 hW
      rw [hPAf, hPJf, hGAf, hGJf, hW1f]
      exact h5
  have hev : ∀ᶠ N in atTop, W1 N + W2 N < 1 := by
    have h := hc1'.add hc2'
    exact h.eventually (gt_mem_nhds (by simp))
  obtain ⟨n1, hn1⟩ := eventually_atTop.1 hev
  obtain ⟨n0, hn0def⟩ : ∃ n0 : ℕ, n0 = max n1 2 := ⟨_, rfl⟩
  have hn02 : 2 ≤ n0 := by rw [hn0def]; exact le_max_right _ _
  have hsmall : ∀ N, n0 ≤ N → W1 N + W2 N < 1 := fun N hN => by
    rw [hn0def] at hN
    exact hn1 N ((le_max_left _ _).trans hN)
  obtain ⟨KA, hKA⟩ : ∃ K : ℝ, K = CD * Real.sqrt L * (CY * Mq + 1) := ⟨_, rfl⟩
  obtain ⟨KJ, hKJ⟩ : ∃ K : ℝ, K = CJ * L * (CY * Mf + 1) := ⟨_, rfl⟩
  have hCY0 : 0 < CY := by linarith
  have hKA0 : 0 ≤ KA := by rw [hKA]; positivity
  have hKJ0 : 0 ≤ KJ := by rw [hKJ]; positivity
  have hA0 : 0 ≤ CD * Real.sqrt L * Mq := by positivity
  have hJ0 : 0 ≤ CJ * L * Mf := by positivity
  have hE0 : 0 ≤ CJ * L := by positivity
  -- the Gaussian side is bounded by comparison with the particle system `n0`
  have hG : ∀ (a : ℝ) (ha : 0 ≤ a), ∀ Φ ∈ CbUnitBall (PathSpace d m T) 5,
      |GAf a ha Φ| ≤ CD * Real.sqrt L * Mq + KA ∧ |GJf a ha Φ| ≤ CJ * L * Mf + KJ + CJ * L := by
    intro a ha Φ hΦ
    obtain ⟨mm, h1, h2, h3, h4⟩ := key n0 hn02 a ha Φ hΦ
    have hb : 0 ≤ max (a - Rw) 0 := le_max_right _ _
    have hs := hsmall n0 le_rfl
    have hW1lt : W1 n0 < 1 := lt_of_le_of_lt le_self_add hs
    have hW2lt : W2 n0 < 1 := lt_of_le_of_lt le_add_self hs
    have hw1 : W1f n0 (max (a - Rw) 0) < 1 := lt_of_le_of_lt (hle1 _ _ hb) hW1lt
    have hne : W1f n0 (max (a - Rw) 0) ≠ ⊤ := (hw1.trans ENNReal.one_lt_top).ne
    have hw1r : (W1f n0 (max (a - Rw) 0)).toReal ≤ 1 := by
      have := ENNReal.toReal_mono ENNReal.one_ne_top hw1.le
      simpa using this
    have hmm1 : ‖mm‖ ≤ 1 := by
      have : ENNReal.ofReal ‖mm‖ < 1 := lt_of_le_of_lt (h1.trans (hle2 _ _ hb)) hW2lt
      exact (ENNReal.ofReal_lt_one.1 this).le
    obtain ⟨h5, h6⟩ := h4 hne
    have hw0 : 0 ≤ (W1f n0 (max (a - Rw) 0)).toReal := ENNReal.toReal_nonneg
    constructor
    · have e1 : CD * Real.sqrt L * ((CY * Mq + 1) * (W1f n0 (max (a - Rw) 0)).toReal) ≤ KA := by
        have : CD * Real.sqrt L * ((CY * Mq + 1) * (W1f n0 (max (a - Rw) 0)).toReal) =
            KA * (W1f n0 (max (a - Rw) 0)).toReal := by rw [hKA]; ring
        rw [this]
        exact mul_le_of_le_one_right hKA0 hw1r
      have t := u10_abs_sub_le (PAf n0 a ha Φ) (PAf n0 a ha Φ - GAf a ha Φ)
      rw [sub_sub_cancel] at t
      linarith
    · have e1 : CJ * L * ((CY * Mf + 1) * (W1f n0 (max (a - Rw) 0)).toReal + ‖mm‖) ≤ KJ + CJ * L := by
        have : CJ * L * ((CY * Mf + 1) * (W1f n0 (max (a - Rw) 0)).toReal + ‖mm‖) =
            KJ * (W1f n0 (max (a - Rw) 0)).toReal + CJ * L * ‖mm‖ := by rw [hKJ]; ring
        rw [this]
        exact add_le_add (mul_le_of_le_one_right hKJ0 hw1r) (mul_le_of_le_one_right hE0 hmm1)
      have t := u10_abs_sub_le (PJf n0 a ha Φ) (PJf n0 a ha Φ - GJf a ha Φ)
      rw [sub_sub_cancel] at t
      linarith
  obtain ⟨C₁, hC₁⟩ : ∃ C : ℝ, C = KA + KJ + CJ * L := ⟨_, rfl⟩
  obtain ⟨C₂, hC₂⟩ : ∃ C : ℝ, C = (CD * Real.sqrt L * Mq + (CD * Real.sqrt L * Mq + KA)) +
      1 / 2 * (CJ * L * Mf + (CJ * L * Mf + KJ + CJ * L)) := ⟨_, rfl⟩
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁]; positivity
  have hC₂0 : 0 ≤ C₂ := by rw [hC₂]; positivity
  refine ⟨max C₁ C₂, fun N => if n0 ≤ N then (W1 N).toReal + (W2 N).toReal else 1, ?_, ?_⟩
  · have ht1 : Tendsto (fun N => (W1 N).toReal) atTop (𝓝 0) := by
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hc1'
      rw [ENNReal.toReal_zero] at this
      exact this
    have ht2 : Tendsto (fun N => (W2 N).toReal) atTop (𝓝 0) := by
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hc2'
      rw [ENNReal.toReal_zero] at this
      exact this
    have h12 : Tendsto (fun N => (W1 N).toReal + (W2 N).toReal) atTop (𝓝 0) := by
      simpa using ht1.add ht2
    refine h12.congr' ?_
    filter_upwards [eventually_ge_atTop n0] with N hN
    simp [if_pos hN]
  · intro N hN a ha Φ hΦ
    have main : |PAf N a ha Φ - GAf a ha Φ| + 1 / 2 * |PJf N a ha Φ - GJf a ha Φ| ≤
        max C₁ C₂ * (if n0 ≤ N then (W1 N).toReal + (W2 N).toReal else 1) := by
      obtain ⟨mm, h1, h2, h3, h4⟩ := key N hN a ha Φ hΦ
      obtain ⟨hGa, hGj⟩ := hG a ha Φ hΦ
      have hb : 0 ≤ max (a - Rw) 0 := le_max_right _ _
      by_cases hNN : n0 ≤ N
      · rw [if_pos hNN]
        have hs := hsmall N hNN
        have hW1lt : W1 N < 1 := lt_of_le_of_lt le_self_add hs
        have hW2lt : W2 N < 1 := lt_of_le_of_lt le_add_self hs
        have hne1 : W1 N ≠ ⊤ := (hW1lt.trans ENNReal.one_lt_top).ne
        have hne2 : W2 N ≠ ⊤ := (hW2lt.trans ENNReal.one_lt_top).ne
        have hne : W1f N (max (a - Rw) 0) ≠ ⊤ := ne_top_of_le_ne_top hne1 (hle1 _ _ hb)
        obtain ⟨h5, h6⟩ := h4 hne
        have hw : (W1f N (max (a - Rw) 0)).toReal ≤ (W1 N).toReal :=
          ENNReal.toReal_mono hne1 (hle1 _ _ hb)
        have hmm : ‖mm‖ ≤ (W2 N).toReal :=
          (ENNReal.ofReal_le_iff_le_toReal hne2).1 (h1.trans (hle2 _ _ hb))
        have hw0 : 0 ≤ (W1 N).toReal := ENNReal.toReal_nonneg
        have hw20 : 0 ≤ (W2 N).toReal := ENNReal.toReal_nonneg
        have eA : CD * Real.sqrt L * ((CY * Mq + 1) * (W1f N (max (a - Rw) 0)).toReal) ≤
            KA * (W1 N).toReal := by
          have : CD * Real.sqrt L * ((CY * Mq + 1) * (W1f N (max (a - Rw) 0)).toReal) =
              KA * (W1f N (max (a - Rw) 0)).toReal := by rw [hKA]; ring
          rw [this]
          exact mul_le_mul_of_nonneg_left hw hKA0
        have eJ : CJ * L * ((CY * Mf + 1) * (W1f N (max (a - Rw) 0)).toReal + ‖mm‖) ≤
            KJ * (W1 N).toReal + CJ * L * (W2 N).toReal := by
          have : CJ * L * ((CY * Mf + 1) * (W1f N (max (a - Rw) 0)).toReal + ‖mm‖) =
              KJ * (W1f N (max (a - Rw) 0)).toReal + CJ * L * ‖mm‖ := by rw [hKJ]; ring
          rw [this]
          exact add_le_add (mul_le_mul_of_nonneg_left hw hKJ0) (mul_le_mul_of_nonneg_left hmm hE0)
        have hmax1 : KA + KJ + CJ * L ≤ max C₁ C₂ := by rw [← hC₁]; exact le_max_left _ _
        have hmax := mul_le_mul_of_nonneg_right hmax1 (add_nonneg hw0 hw20)
        nlinarith [mul_nonneg hKJ0 hw0, mul_nonneg hE0 hw0, mul_nonneg hKA0 hw20, mul_nonneg hKJ0 hw20,
          mul_nonneg hE0 hw20]
      · rw [if_neg hNN, mul_one]
        have tA := u10_abs_sub_le (PAf N a ha Φ) (GAf a ha Φ)
        have tJ := u10_abs_sub_le (PJf N a ha Φ) (GJf a ha Φ)
        have hmax : C₂ ≤ max C₁ C₂ := le_max_right _ _
        linarith
    simpa only [hPAf, hGAf, hPJf, hGJf] using main

end HRS.MC.E213U10

end
