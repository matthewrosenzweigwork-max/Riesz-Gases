import HRS.MS.S81R_Rev
import HRS.MS.S81R_Det
import HRS.Whole.Critical

/-!
# S81R, packet R10: stationary path reversal of the canonical realization (S8.2 O04)

`s81r_canonical_reversible_windows`: for `1 ≤ d`, `0 ≤ s`, `0 < a`, `0 < β` and `IsCanonicalRealization d s a β N P X₀ W X`
(only its Brownian, independence, initial-law and strong-solution fields are used), the finite-dimensional marginals of `X` on every
window are invariant under time reversal: `ReversibleWindows P X` (the definition copied from the Pro skeleton `S8.2-Observed.lean`).

Route: the truncated kernels `k_M` give globally Lipschitz solutions `Y^M = X` eventually on every compact (S81G); the rescaled `Φ(Y^M)` is the Pois flow
of a `GapRef` reference measure, which is reversible (`Gap.gap_reversible` + Markov chain formula); the initial law is reweighted by
`r_M(X₀)` (total variation `≤ 2(1 - Z/Z_M)`), and cylinder products of test functions determine the law (characteristic functionals).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl HRS.MS.MfeConf HRS.MS.Gap HRS.MS.S81G
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S81R

/-- finite-dimensional marginals on windows are reversible (copy of `ReversibleWindows` of the Pro skeleton `S8.2-Observed.lean`) -/
def ReversibleWindows {d N : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → Whole.EucConfig d N) : Prop :=
  ∀ a T : ℝ, 0 ≤ a → 0 ≤ T → ∀ n : ℕ, ∀ t : Fin n → Set.Icc (0 : ℝ) T,
    P.map (fun w i => X (a + t i).toNNReal w) = P.map (fun w i => X (a + T - t i).toNNReal w)

/-- passage to the limit: reweighted bounded functionals converge to the unweighted limit -/
theorem s81r_lim {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {E : Type*} [MeasurableSpace E] {X0 : Ω → E} (hX0 : Measurable X0) (c : ℕ → ℝ)
    (hc1 : ∀ M, c M ≤ 1) (hcT : Tendsto c atTop (𝓝 1)) (r : ℕ → E → ℝ)
    (hrm : ∀ M, Measurable (r M)) (hr0 : ∀ M x, 0 ≤ r M x)
    (hrc : ∀ M, ∀ᵐ x ∂(P.map X0), c M ≤ r M x)
    (hrint : ∀ M, ∫⁻ x, ENNReal.ofReal (r M x) ∂(P.map X0) = 1) {C : ℝ} (hC0 : 0 ≤ C)
    (FM : ℕ → Ω → ℝ) (F : Ω → ℝ) (hFm : ∀ M, Measurable (FM M)) (hFb : ∀ M ω, |FM M ω| ≤ C)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun M => FM M ω) atTop (𝓝 (F ω))) :
    Tendsto (fun M => ∫ ω, FM M ω ∂(P.withDensity (fun ω => ENNReal.ofReal (r M (X0 ω)))))
      atTop (𝓝 (∫ ω, F ω ∂P)) := by
  have h1 : Tendsto (fun M => ∫ ω, FM M ω ∂P) atTop (𝓝 (∫ ω, F ω ∂P)) :=
    tendsto_integral_of_dominated_convergence (fun _ => C) (fun M => (hFm M).aestronglyMeasurable)
      (integrable_const C) (fun M => Filter.Eventually.of_forall fun ω => by
        simpa [Real.norm_eq_abs] using hFb M ω) hlim
  have h2 : Tendsto (fun M => ∫ ω, FM M ω ∂(P.withDensity (fun ω => ENNReal.ofReal (r M (X0 ω)))) -
      ∫ ω, FM M ω ∂P) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun M => ?_) (a := fun M => C * (2 * (1 - c M))) ?_
    · rw [Real.norm_eq_abs]
      exact s81r_tv_bound hX0 (r M) (hrm M) (hr0 M) (hc1 M) (hrc M) (hrint M) (hFm M) hC0
        (hFb M)
    · have := (((hcT.const_sub 1).const_mul 2).const_mul C)
      simpa using this
  have := h2.add h1
  simpa using this

/-- equality of expectations of cylinder products of test functions -/
theorem s81r_test_eq {d N : ℕ} (hd : 1 ≤ d) {s a β : ℝ} (hs : 0 ≤ s) (ha : 0 < a) (hβ : 0 < β)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X₀ : Ω → Whole.EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → Whole.EucConfig d N}
    (hX : Whole.IsCanonicalRealization d s a β N P X₀ W X) {a0 T : ℝ} (ha0 : 0 ≤ a0)
    (hT : 0 ≤ T) (n : ℕ)
    (t : Fin n → ℝ) (ht : ∀ i, t i ∈ Set.Icc 0 T) (f : Fin n → Euc (N * d) → ℝ)
    (hf : ∀ i, s81r_S (f i)) :
    ∫ ω, ∏ k, f k (s81r_Phi β d N (X (a0 + t k).toNNReal ω)) ∂P =
      ∫ ω, ∏ k, f k (s81r_Phi β d N (X (a0 + T - t k).toNNReal ω)) ∂P := by
  set D := Whole.quadraticGradientDyn d s a β with hD
  set T1 : ℝ := a0 + T + 1 with hT1
  have hT1pos : 0 < T1 := by linarith
  have hsol := hX.solution T1
  obtain ⟨B0, hB0⟩ := s81g_pot (d := d) a
  have H : S81Hyp D :=
    ⟨hs, hd, inv_pos.2 hβ, by show Continuous (fun x : Euc d => a * ‖x‖ ^ 2 / 2); fun_prop,
      ⟨a / 2, 0, by positivity, fun x => s81g_conf_lower a x⟩⟩
  obtain ⟨ℱ, W', Ys, hBF, hX0, hYm, hYpath, hident⟩ :=
    s81r_setup (N := N) D rfl hs hB0 hX.brownian hsol hX.indep
  have hae := hident T1 hT1pos hsol
  have hX0m : Measurable (X 0) := hsol.adapted 0
  have hlawX0 : P.map (X 0) = sb1Gam D (Whole.rieszKernel d s) N := by
    rw [Measure.map_congr hsol.init]
    exact hX.init.trans (s81g_canonical_eq (D := D) (k := Whole.rieszKernel d s) (N := N)
      (inv_inv β) (s81g_riesz_even s) (s81g_sing_gz_pos (N := N) H))
  have hmM := fun M : ℕ =>
    s81r_smooth_rev hd hs ha hβ M hBF (hX0 0) hlawX0 (hYpath M) ha0 n t ht f hf
  choose r hrm hr0 hrc hrint hrev using hmM
  -- bounds
  choose Mk hMk using fun k => s81r_S_bdd (hf k)
  set C : ℝ := ∏ k, Mk k with hC
  have hC0 : 0 ≤ C := Finset.prod_nonneg fun k _ => (abs_nonneg _).trans (hMk k 0)
  have hprod : ∀ y : Fin n → Euc (N * d), |∏ k, f k (y k)| ≤ C := fun y => by
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod₀ (fun k _ => abs_nonneg _) fun k _ => hMk k _
  have hc1 : ∀ M : ℕ, sb1Gz D (Whole.rieszKernel d s) N / sb1Gz D (sb1kM d s M) N ≤ 1 :=
    fun M => (div_le_one (s81g_reg_gz_pos (N := N) H M)).2 (s81g_Z_ge (N := N) H M)
  have hcT : Tendsto (fun M : ℕ => sb1Gz D (Whole.rieszKernel d s) N / sb1Gz D (sb1kM d s M) N)
      atTop (𝓝 1) := by
    have hz : 0 < sb1Gz D (Whole.rieszKernel d s) N := s81g_sing_gz_pos (N := N) H
    have h : Tendsto (fun M : ℕ => sb1Gz D (Whole.rieszKernel d s) N / sb1Gz D (sb1kM d s M) N)
        atTop (𝓝 (sb1Gz D (Whole.rieszKernel d s) N / sb1Gz D (Whole.rieszKernel d s) N)) :=
      (tendsto_const_nhds).div (s81g_Z_tendsto (N := N) H) hz.ne'
    rwa [div_self hz.ne'] at h
  have hid : ∀ (ζ : Ω) (M : ℕ), (∀ u : ℝ≥0, (u : ℝ) ≤ T1 → Ys M (u : ℝ) ζ = X u ζ) →
      ∀ τ : ℝ, 0 ≤ τ → τ ≤ a0 + T → Ys M τ ζ = X τ.toNNReal ζ := by
    intro ζ M hM τ hτ hτT
    have := hM τ.toNNReal (by rw [Real.coe_toNNReal _ hτ]; linarith)
    rwa [Real.coe_toNNReal _ hτ] at this
  have hPhim : Measurable (s81r_Phi β d N) := (s81r_Phi β d N).continuous.measurable
  have hFm : ∀ (u : Fin n → ℝ) (M : ℕ),
      Measurable (fun ζ => ∏ k, f k (s81r_Phi β d N (Ys M (u k) ζ))) := fun u M =>
    Finset.measurable_prod _ fun k _ =>
      (s81r_S_cont (hf k)).measurable.comp (hPhim.comp (hYm M _))
  have hlim : ∀ u : Fin n → ℝ, (∀ k, 0 ≤ u k) → (∀ k, u k ≤ a0 + T) →
      ∀ᵐ ζ ∂P, Tendsto (fun M : ℕ => ∏ k, f k (s81r_Phi β d N (Ys M (u k) ζ))) atTop
        (𝓝 (∏ k, f k (s81r_Phi β d N (X (u k).toNNReal ζ)))) := by
    intro u hu0 huT
    filter_upwards [hae] with ζ hζ
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hζ] with M hM
    exact Finset.prod_congr rfl fun k _ => by rw [hid ζ M hM (u k) (hu0 k) (huT k)]
  have hnn1 : ∀ k, 0 ≤ a0 + t k := fun k => by linarith [(ht k).1]
  have hnn2 : ∀ k, 0 ≤ a0 + T - t k := fun k => by linarith [(ht k).2]
  have hLlim := s81r_lim hX0m _ hc1 hcT r hrm hr0 hrc hrint hC0
    (fun M ζ => ∏ k, f k (s81r_Phi β d N (Ys M (a0 + t k) ζ)))
    (fun ζ => ∏ k, f k (s81r_Phi β d N (X (a0 + t k).toNNReal ζ)))
    (fun M => hFm (fun k => a0 + t k) M)
    (fun M ζ => hprod _) (hlim (fun k => a0 + t k) hnn1 (fun k => by linarith [(ht k).1, (ht k).2]))
  have hRlim := s81r_lim hX0m _ hc1 hcT r hrm hr0 hrc hrint hC0
    (fun M ζ => ∏ k, f k (s81r_Phi β d N (Ys M (a0 + T - t k) ζ)))
    (fun ζ => ∏ k, f k (s81r_Phi β d N (X (a0 + T - t k).toNNReal ζ)))
    (fun M => hFm (fun k => a0 + T - t k) M)
    (fun M ζ => hprod _) (hlim (fun k => a0 + T - t k) hnn2 (fun k => by linarith [(ht k).1, (ht k).2]))
  have hfun : (fun M : ℕ => ∫ ζ, ∏ k, f k (s81r_Phi β d N (Ys M (a0 + t k) ζ))
      ∂(P.withDensity (fun ζ => ENNReal.ofReal (r M (X 0 ζ))))) =
      fun M : ℕ => ∫ ζ, ∏ k, f k (s81r_Phi β d N (Ys M (a0 + T - t k) ζ))
      ∂(P.withDensity (fun ζ => ENNReal.ofReal (r M (X 0 ζ)))) := funext hrev
  rw [hfun] at hLlim
  exact tendsto_nhds_unique hLlim hRlim

/-- **S8.2 O04**: stationary reversibility of the canonical realization on every window -/
theorem s81r_canonical_reversible_windows {d N : ℕ} (hd : 1 ≤ d) {s a β : ℝ} (hs : 0 ≤ s)
    (ha : 0 < a) (hβ : 0 < β) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X₀ : Ω → Whole.EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → Whole.EucConfig d N}
    (hX : Whole.IsCanonicalRealization d s a β N P X₀ W X) : ReversibleWindows P X := by
  intro a0 T ha0 hT n t
  have hsol := hX.solution (a0 + T + 1)
  have hXm : ∀ u : ℝ≥0, Measurable (X u) := hsol.adapted
  set L : Ω → (Fin n → Whole.EucConfig d N) := fun w i => X (a0 + t i).toNNReal w with hL
  set R : Ω → (Fin n → Whole.EucConfig d N) := fun w i => X (a0 + T - t i).toNNReal w with hR
  have hLm : Measurable L := measurable_pi_iff.2 fun i => hXm _
  have hRm : Measurable R := measurable_pi_iff.2 fun i => hXm _
  let e : (Fin n → Whole.EucConfig d N) ≃ᵐ (Fin n → Euc (N * d)) :=
    MeasurableEquiv.piCongrRight fun _ => (s81r_PhiE hβ d N).toHomeomorph.toMeasurableEquiv
  have he : ∀ (x : Fin n → Whole.EucConfig d N) (k : Fin n), e x k = s81r_Phi β d N (x k) :=
    fun x k => rfl
  have key : (P.map L).map e = (P.map R).map e := by
    refine s81r_det _ _ fun f hf => ?_
    rw [Measure.map_map e.measurable hLm, Measure.map_map e.measurable hRm]
    have hcont : ∀ g : Fin n → Euc (N * d) → ℝ, (∀ k, s81r_S (g k)) →
        AEStronglyMeasurable (fun x : Fin n → Euc (N * d) => ∏ k, g k (x k)) (P.map (e ∘ L)) ∧
        AEStronglyMeasurable (fun x : Fin n → Euc (N * d) => ∏ k, g k (x k)) (P.map (e ∘ R)) := by
      intro g hg
      have : Continuous (fun x : Fin n → Euc (N * d) => ∏ k, g k (x k)) :=
        continuous_finsetProd _ fun k _ => (s81r_S_cont (hg k)).comp (continuous_apply k)
      exact ⟨this.aestronglyMeasurable, this.aestronglyMeasurable⟩
    rw [integral_map (e.measurable.comp hLm).aemeasurable (hcont f hf).1,
      integral_map (e.measurable.comp hRm).aemeasurable (hcont f hf).2]
    exact s81r_test_eq hd hs ha hβ P hX ha0 hT n (fun i => (t i : ℝ)) (fun i => (t i).2) f hf
  have h2 := congrArg (fun m => m.map e.symm) key
  simp only [Measure.map_map e.symm.measurable e.measurable] at h2
  have hid : e.symm ∘ e = id := funext fun x => e.symm_apply_apply x
  rw [hid, Measure.map_id, Measure.map_id] at h2
  exact h2

end HRS.MS.S81R
