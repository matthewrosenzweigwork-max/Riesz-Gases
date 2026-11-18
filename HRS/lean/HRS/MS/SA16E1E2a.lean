import HRS.MS.SA16E1E12
import HRS.MS.SA16JetSchwartz
import HRS.MS.SA16StrongApprox
import HRS.MS.SA16StrongConvN
import HRS.MS.SA16StrongSL6

/-!
# S.A.16 E2 (part a): jets of compactly supported `C^k` functions lie in `WmpSpace`
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Evolution
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixA.Phase2SA16

/-- Dominated convergence in `L^p` for a uniformly bounded, uniformly compactly supported, pointwise
convergent sequence. -/
lemma e2_lp_dct {d : ℕ} {V : Type*} [NormedAddCommGroup V] {p : ℝ} (hp : 1 ≤ p)
    {F : ℕ → Euc d → V} {G : Euc d → V} {Bd R : ℝ}
    (hmeas : ∀ n, AEStronglyMeasurable (fun x => F n x - G x) volume)
    (hb : ∀ n x, ‖F n x - G x‖ ≤ Bd) (hR : ∀ n x, R < ‖x‖ → F n x - G x = 0)
    (hlim : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (G x))) :
    Tendsto (fun n => eLpNorm (fun x => F n x - G x) (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
  have hp0 : 0 < p := by linarith
  have hpe0 : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have hpetop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpr : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have heq : ∀ n, eLpNorm (fun x => F n x - G x) (ENNReal.ofReal p) volume =
      (∫⁻ x, ‖F n x - G x‖ₑ ^ p) ^ (1 / p) := fun n => by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpe0 hpetop (hmeas n), hpr]
  simp_rw [heq]
  have hball : volume (Metric.closedBall (0 : Euc d) R) < ⊤ := measure_closedBall_lt_top
  have hlim' : Tendsto (fun n => ∫⁻ x, ‖F n x - G x‖ₑ ^ p) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence' (μ := (volume : Measure (Euc d)))
      (F := fun n x => ‖F n x - G x‖ₑ ^ p) (f := fun _ => 0)
      (bound := (Metric.closedBall (0 : Euc d) R).indicator (fun _ => ENNReal.ofReal Bd ^ p))
      (fun n => ((hmeas n).enorm.pow_const _))
      (fun n => Eventually.of_forall fun x => ?_)
      (by
        rw [lintegral_indicator measurableSet_closedBall]
        simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter]
        exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top)
          hball.ne)
      (Eventually.of_forall fun x => ?_)
    · simpa using this
    · by_cases hx : x ∈ Metric.closedBall (0 : Euc d) R
      · rw [Set.indicator_of_mem hx]
        refine ENNReal.rpow_le_rpow ?_ hp0.le
        beta_reduce
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hb n x)
      · rw [Set.indicator_of_notMem hx]
        have : R < ‖x‖ := by simpa [dist_zero_right] using hx
        beta_reduce
        rw [hR n x this]
        simp [ENNReal.zero_rpow_of_pos hp0]
    · have h1 : Tendsto (fun n => F n x - G x) atTop (𝓝 0) := by
        simpa using (hlim x).sub_const (G x)
      have h2 : Tendsto (fun n => ‖F n x - G x‖ₑ) atTop (𝓝 0) := by
        simpa using h1.enorm
      have h3 := ((ENNReal.continuous_rpow_const (y := p)).tendsto 0).comp h2
      rw [ENNReal.zero_rpow_of_pos hp0] at h3
      exact h3
  have h4 := ((ENNReal.continuous_rpow_const (y := 1 / p)).tendsto 0).comp hlim'
  rw [ENNReal.zero_rpow_of_pos (show 0 < 1 / p by positivity)] at h4
  exact h4

lemma e2_pd_zero {d : ℕ} {g : Euc d → ℝ} {j : ℕ} (idx : Fin j → Fin d) {y : Euc d}
    (hy : y ∉ tsupport g) : partialDeriv idx g y = 0 := by
  have hev : g =ᶠ[𝓝 y] 0 := notMem_tsupport_iff_eventuallyEq.1 hy
  simp only [partialDeriv]
  rw [(hev.iteratedFDeriv ℝ _).self_of_nhds]
  simp

lemma e2_conv_zero {d : ℕ} {u : Euc d → ℝ} {R : ℝ} (hu : ∀ y, R < ‖y‖ → u y = 0) (n : ℕ)
    {x : Euc d} (hx : R + 1 < ‖x‖) : sa16j_conv (sa16y_rho d n) u x = 0 := by
  unfold sa16j_conv
  refine integral_eq_zero_of_ae (Eventually.of_forall fun z => ?_)
  show sa16y_rho d n z * u (x - z) = 0
  by_cases hz : 1 / ((n : ℝ) + 1) < ‖z‖
  · rw [sa16y_rho_supp n z hz, zero_mul]
  · push Not at hz
    have h1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    have h2 : R < ‖x - z‖ := by
      have := norm_sub_norm_le x z
      linarith
    rw [hu _ h2, mul_zero]

lemma e2_jet_cont {d k : ℕ} {g : Euc d → ℝ} (hg : ContDiff ℝ k g) : Continuous (wJet k g) :=
  continuous_pi fun τ =>
    (sa16y_pd_contDiffN (j := (τ.1 : ℕ)) (r := k - (τ.1 : ℕ)) (f := g)
      (by have : (τ.1 : ℕ) + (k - (τ.1 : ℕ)) = k := by have := τ.1.2; omega
          rw [this]; exact hg) τ.2).continuous

/-- The jet of a compactly supported `C^k` function lies in `WmpSpace`. -/
theorem e2_jet_mem (d k : ℕ) (p : ℝ) [Fact (2 ≤ p)] {g : Euc d → ℝ} (hg : ContDiff ℝ k g)
    (hc : HasCompactSupport g) :
    ∃ G : WmpSpace d k p, ((G : WLp d k p) : Euc d → (WIndex d k → ℝ)) =ᵐ[volume] wJet k g := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  have hp1 : (1 : ℝ) ≤ p := by linarith
  have hpd : ∀ τ : WIndex d k, Continuous (partialDeriv τ.2 g) := fun τ =>
    (sa16y_pd_contDiffN (j := (τ.1 : ℕ)) (r := k - (τ.1 : ℕ)) (f := g)
      (by have : (τ.1 : ℕ) + (k - (τ.1 : ℕ)) = k := by have := τ.1.2; omega
          rw [this]; exact hg) τ.2).continuous
  have hjetc : Continuous (wJet k g) := continuous_pi fun τ => hpd τ
  have hjets : HasCompactSupport (wJet k g) := sa16j_jet_support hc k
  have hjet : MemLp (wJet k g) (ENNReal.ofReal p) volume := hjetc.memLp_of_hasCompactSupport hjets
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : Euc d)
  obtain ⟨B, hB⟩ := hjetc.bounded_above_of_compact_support hjets
  have hgR : ∀ y : Euc d, R < ‖y‖ → g y = 0 := fun y hy => by
    by_contra h
    have : y ∈ tsupport g := subset_tsupport _ (Function.mem_support.2 h)
    have := hR this
    rw [Metric.mem_closedBall, dist_zero_right] at this
    linarith
  have hpdR : ∀ τ : WIndex d k, ∀ y : Euc d, R < ‖y‖ → partialDeriv τ.2 g y = 0 := fun τ y hy =>
    e2_pd_zero τ.2 (fun h => by
      have := hR h
      rw [Metric.mem_closedBall, dist_zero_right] at this
      linarith)
  set m : ℕ → Euc d → ℝ := fun n => sa16j_conv (sa16y_rho d n) g with hm
  have hmsm : ∀ n, ContDiff ℝ ∞ (m n) := fun n => sa16y_mollify_smooth n hg.continuous
  have hpdm : ∀ n, ∀ τ : WIndex d k,
      partialDeriv τ.2 (m n) = sa16j_conv (sa16y_rho d n) (partialDeriv τ.2 g) := by
    intro n τ
    have hsupp : ∀ z, 1 / ((n : ℝ) + 1) < ‖z‖ → sa16y_rho d n z = 0 :=
      fun z hz => sa16y_rho_supp n z hz
    exact sa16y_conv_pdN hsupp (by positivity) (sa16y_rho_integrable n) (τ.1 : ℕ)
      (k - (τ.1 : ℕ)) τ.2 g (by
        have : (τ.1 : ℕ) + (k - (τ.1 : ℕ)) = k := by have := τ.1.2; omega
        rw [this]; exact hg)
  have hmjet : ∀ n x τ, wJet k (m n) x τ = sa16j_conv (sa16y_rho d n) (partialDeriv τ.2 g) x :=
    fun n x τ => by simp only [wJet]; rw [hpdm n τ]
  have hmbd : ∀ n x, ‖wJet k (m n) x‖ ≤ B := by
    intro n x
    refine (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans (hB 0))).2 fun τ => ?_
    rw [hmjet, Real.norm_eq_abs]
    exact sa16y_mollify_bound n (hpd τ) (fun y => by
      have := norm_le_pi_norm (wJet k g y) τ
      rw [Real.norm_eq_abs] at this
      exact this.trans (hB y)) x
  have hmcs : ∀ n, HasCompactSupport (m n) := fun n =>
    HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) (R + 1)) (fun x hx => by
      have : R + 1 < ‖x‖ := by simpa [dist_zero_right] using hx
      exact e2_conv_zero hgR n this)
  have hjetF : ∀ n, MemLp (wJet k (m n)) (ENNReal.ofReal p) volume := fun n =>
    (sa16j_jet_cont (hmsm n) k).memLp_of_hasCompactSupport (sa16j_jet_support (hmcs n) k)
  set Ψ : ℕ → WLp d k p := fun n => (hjetF n).toLp _ with hΨ
  set Φ : WLp d k p := hjet.toLp (wJet k g) with hΦ
  have hmem : ∀ n, Ψ n ∈ WmpSpace d k p := by
    intro n
    unfold WmpSpace
    refine Submodule.le_topologicalClosure _ (Submodule.subset_span ?_)
    exact ⟨m n, ⟨hmsm n, hmcs n⟩, (hjetF n).coeFn_toLp⟩
  have hdiff : ∀ n, ‖Ψ n - Φ‖ = (eLpNorm (wJet k (m n) - wJet k g)
      (ENNReal.ofReal p) volume).toReal := by
    intro n
    rw [hΨ, hΦ, ← MemLp.toLp_sub]
    exact Lp.norm_toLp _ _
  have hlim1 : Tendsto (fun n => eLpNorm (wJet k (m n) - wJet k g) (ENNReal.ofReal p) volume)
      atTop (𝓝 0) := by
    have := e2_lp_dct (d := d) (V := WIndex d k → ℝ) hp1 (F := fun n x => wJet k (m n) x)
      (G := wJet k g) (Bd := B + B) (R := R + 1)
      (fun n => ((sa16j_jet_cont (hmsm n) k).sub hjetc).aestronglyMeasurable)
      (fun n x => by
        refine (norm_sub_le _ _).trans ?_
        exact add_le_add (hmbd n x) (hB x))
      (fun n x hx => by
        funext τ
        simp only [Pi.sub_apply, Pi.zero_apply]
        rw [hmjet, e2_conv_zero (hpdR τ) n hx]
        have := hpdR τ x (by linarith)
        simp only [wJet, this, sub_zero])
      (fun x => tendsto_pi_nhds.2 fun τ => by
        simp only [hmjet]
        exact sa16y_mollify_tendsto (hpd τ) x)
    exact this
  have hlim2 : Tendsto (fun n => ‖Ψ n - Φ‖) atTop (𝓝 0) := by
    simp only [hdiff]
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim1
    simpa [Function.comp_def] using this
  have hΨΦ : Tendsto Ψ atTop (𝓝 Φ) := (tendsto_iff_norm_sub_tendsto_zero).2 hlim2
  have hΦmem : Φ ∈ WmpSpace d k p :=
    (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hΨΦ (Eventually.of_forall hmem)
  exact ⟨⟨Φ, hΦmem⟩, hjet.coeFn_toLp⟩

end HRS.Whole.AppendixA.Phase2SA16Evolution
