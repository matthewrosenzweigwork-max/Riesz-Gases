import HRS.MS.MovAdjAux17

/-!
# S6.7 (packet P4, part 4): the Duhamel formula for classical solutions with linearly growing time derivative

Namespace `HRS.MS.MovAdj`, helpers `s67_`.  Infrastructure for the supplement row `S:W:lem:r2mov-global-adjoint`; not a manuscript row.

`s67_duhamel_abs`: for `S67DuhData q B T u a S` and `τ ∈ [0,T]`:
`u τ x = P_τ (u 0)(x) + ∫_0^τ P_{τ-s} (S s)(x) ds`, `P_τ = sg P W q B τ` (the POIS semigroup of `Δ + (-qx + B)·∇`).
Proof: the truncated formula `s67_duhamel_n` and `n → ∞` by dominated convergence.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovAdj

open HRS HRS.Whole HRS.MS.PoisKolm HRS.MS.PoisHigh HRS.MS.Mov63 HRS.MS.FlowB HRS.MS.PoisSg HRS.MS.PoisFlow

universe w

variable {d : ℕ} {q : ℝ} {B : Euc d → Euc d} {T : ℝ} {u a S : ℝ → Euc d → ℝ}

/-- Continuity of `s ↦ P_{τ-s}(g_s)(x)` on `[0,τ]` for bounded jointly continuous `g`. -/
theorem s67_cont_sg_comp {Ω : Type w} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → Fin d → ℝ} (hW : IsBrownianFiltration P ℱ W)
    {Mb : ℝ} (hq : 0 < q) {m : ℕ} (hm : 2 ≤ m) (hBm : HasCbBound m Mb B) (hT0 : 0 ≤ T)
    {g : ℝ → Euc d → ℝ} (hg : Continuous fun p : ℝ × Euc d => g p.1 p.2) {K : ℝ}
    (hK : ∀ r y, |g r y| ≤ K) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) (x : Euc d) :
    ContinuousOn (fun s : ℝ => sg P W q B (τ - s) (g s) x) (Icc 0 τ) := by
  have hc := hs_cont_sg hW hq hm hBm hT0 hg hK
  have h2 : ContinuousOn (fun s : ℝ => ((s, τ - s, x) : ℝ × ℝ × Euc d)) (Icc 0 τ) := by fun_prop
  exact hc.comp h2 (fun s hs => by
    show τ - s ∈ Icc (0 : ℝ) T
    exact ⟨by linarith [hs.2], by linarith [hs.1, hτ.2]⟩)

/-- Convergence of `P_{τ'} (g_n)(x)` when the bounded continuous `g_n` are eventually equal to `g_0` pointwise. -/
theorem s67_sg_tendsto {Ω : Type w} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → Fin d → ℝ} (hW : IsBrownianFiltration P ℱ W)
    {Mb : ℝ} (hq : 0 < q) {m : ℕ} (hm : 2 ≤ m) (hBm : HasCbBound m Mb B) {τ' : ℝ} (hτ' : 0 ≤ τ')
    (x : Euc d) {gn : ℕ → Euc d → ℝ} {g0 : Euc d → ℝ} {K : ℝ} (hc : ∀ n, Continuous (gn n))
    (hb : ∀ n y, |gn n y| ≤ K) (hlim : ∀ y, ∃ N : ℕ, ∀ n ≥ N, gn n y = g0 y) :
    Tendsto (fun n : ℕ => sg P W q B τ' (gn n) x) atTop (𝓝 (sg P W q B τ' g0 x)) := by
  have hn := sgNoise_of_brownian hW
  have hfl : Measurable (fun o => flowMap q B (fun r => W r o) τ' x) :=
    hs_meas_flow (W := W) hq (by omega) hBm hn hτ' x
  unfold sg
  refine tendsto_integral_of_dominated_convergence (fun _ => K) (fun n => ?_) (integrable_const _)
    (fun n => Eventually.of_forall fun o => ?_) (Eventually.of_forall fun o => ?_)
  · exact ((hc n).measurable.comp hfl).aestronglyMeasurable
  · rw [Real.norm_eq_abs]; exact hb n _
  · obtain ⟨N, hN⟩ := hlim (flowMap q B (fun r => W r o) τ' x)
    exact tendsto_atTop_of_eventually_const (i₀ := N) (fun n hn' => hN n hn')

theorem s67_exists_cut (y : Euc d) : ∃ N : ℕ, ∀ n ≥ N, ‖y‖ < (n : ℝ) + 1 := by
  refine ⟨⌈‖y‖⌉₊, fun n hn => ?_⟩
  have h1 : ‖y‖ ≤ ⌈‖y‖⌉₊ := Nat.le_ceil _
  have h3 : (⌈‖y‖⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
  linarith

set_option maxHeartbeats 3200000 in
theorem s67_duhamel_abs {Ω : Type w} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → Fin d → ℝ} (hW : IsBrownianFiltration P ℱ W)
    {Mb : ℝ} (hq : 0 < q) {m : ℕ} (hm : 2 ≤ m) (hBm : HasCbBound m Mb B)
    (h : S67DuhData q B T u a S) (hT : 0 < T) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) (x : Euc d) :
    u τ x = sg P W q B τ (u 0) x + ∫ s in (0 : ℝ)..τ, sg P W q B (τ - s) (S s) x := by
  have hT0 : 0 ≤ T := hT.le
  have hBb : ∀ y, ‖B y‖ ≤ Mb := fun y => by simpa using hBm.2 0 (Nat.zero_le _) y
  obtain ⟨K0, hK0⟩ := h.v_bound hT0
  obtain ⟨KF, hKF⟩ := h.F_bound hT0 hBb
  obtain ⟨KS, hKS⟩ := h.Sbd
  have hT00 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT0⟩
  have hclτ : clampT T τ = τ := clampT_of_mem hτ
  have hcl0 : clampT T 0 = 0 := clampT_of_mem hT00
  -- (a) the left side
  have hLHS : Tendsto (fun n : ℕ => s67v T u n τ x) atTop (𝓝 (u τ x)) := by
    obtain ⟨N, hN⟩ := s67_exists_cut x
    refine tendsto_atTop_of_eventually_const (i₀ := N) (fun n hn' => ?_)
    rw [S67DuhData.v_eventually (q := q) τ x u T (hN n hn'), hclτ]
  -- (b) the semigroup term
  have hB' : Tendsto (fun n : ℕ => sg P W q B τ (s67v T u n 0) x) atTop (𝓝 (sg P W q B τ (u 0) x)) := by
    refine s67_sg_tendsto hW hq hm hBm hτ.1 x (gn := fun n => s67v T u n 0) (g0 := u 0) (K := K0)
      (fun n => ?_) (fun n y => hK0 n 0 y) (fun y => ?_)
    · exact (h.v_cont hT0 n).comp (continuous_const.prodMk continuous_id)
    · obtain ⟨N, hN⟩ := s67_exists_cut y
      exact ⟨N, fun n hn' => by rw [S67DuhData.v_eventually (q := q) 0 y u T (hN n hn'), hcl0]⟩
  -- (c) the integral term
  have hSc : Continuous fun p : ℝ × Euc d => S (clampT T p.1) p.2 := s67_comp_clamp hT0 h.Scont
  have hinner : ∀ s ∈ Icc (0 : ℝ) τ, Tendsto (fun n : ℕ => sg P W q B (τ - s) (s67F q B T u S n s) x)
      atTop (𝓝 (sg P W q B (τ - s) (S (clampT T s)) x)) := by
    intro s hs
    refine s67_sg_tendsto hW hq hm hBm (by linarith [hs.2]) x (gn := fun n => s67F q B T u S n s)
      (g0 := S (clampT T s)) (K := KF) (fun n => ?_) (fun n y => hKF n s y) (fun y => ?_)
    · exact (h.F_cont hT0 hBm.1.continuous n).comp (continuous_const.prodMk continuous_id)
    · obtain ⟨N, hN⟩ := s67_exists_cut y
      exact ⟨N, fun n hn' => s67F_eventually s y (hN n hn')⟩
  have hint : Tendsto (fun n : ℕ => ∫ s in (0 : ℝ)..τ, sg P W q B (τ - s) (s67F q B T u S n s) x) atTop
      (𝓝 (∫ s in (0 : ℝ)..τ, sg P W q B (τ - s) (S (clampT T s)) x)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => KF) ?_ ?_
      intervalIntegrable_const ?_
    · refine Eventually.of_forall fun n => ?_
      have hcn := s67_cont_sg_comp hW hq hm hBm hT0 (h.F_cont hT0 hBm.1.continuous n)
        (fun r y => hKF n r y) hτ x
      rw [uIoc_of_le hτ.1]
      exact (hcn.aestronglyMeasurable (μ := volume) measurableSet_Icc).mono_set Ioc_subset_Icc_self
    · refine Eventually.of_forall fun n => Eventually.of_forall fun s hs => ?_
      rw [uIoc_of_le hτ.1] at hs
      have : |sg P W q B (τ - s) (s67F q B T u S n s) x| ≤ KF := by
        unfold sg
        have := norm_integral_le_of_norm_le_const (μ := P)
          (f := fun o => s67F q B T u S n s (flowMap q B (fun r => W r o) (τ - s) x)) (C := KF)
          (Eventually.of_forall fun o => by rw [Real.norm_eq_abs]; exact hKF n s _)
        simpa [Real.norm_eq_abs, Measure.real] using this
      rwa [Real.norm_eq_abs]
    · refine Eventually.of_forall fun s hs => ?_
      rw [uIoc_of_le hτ.1] at hs
      exact hinner s ⟨hs.1.le, hs.2⟩
  have hIeq : ∫ s in (0 : ℝ)..τ, sg P W q B (τ - s) (S (clampT T s)) x =
      ∫ s in (0 : ℝ)..τ, sg P W q B (τ - s) (S s) x := by
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    rw [uIcc_of_le hτ.1] at hs
    simp only [clampT_of_mem (⟨hs.1, hs.2.trans hτ.2⟩ : s ∈ Icc (0 : ℝ) T)]
  rw [← hIeq]
  have hfin : Tendsto (fun n : ℕ => s67v T u n τ x) atTop
      (𝓝 (sg P W q B τ (u 0) x + ∫ s in (0 : ℝ)..τ, sg P W q B (τ - s) (S (clampT T s)) x)) := by
    refine (hB'.add hint).congr' (Eventually.of_forall fun n => ?_)
    exact (s67_duhamel_n hW hq hm hBm h hT n hτ x).symm
  exact tendsto_nhds_unique hLHS hfin

end HRS.MS.MovAdj
