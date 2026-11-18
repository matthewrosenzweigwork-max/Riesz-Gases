import HRS.Stochastic.DDS

/-!
# Time-change lemmas for the Dambis--Dubins--Schwarz theorem (packet T of SI-01n)

Statements and conventions as in `HRS/Stochastic/WIENER_SPEC.md` (B.1.5 and B.2--B.6).

* `measurableSet_sup_nullSets_iff`, `condExp_sup_nullSets`: completing a sub-sigma-algebra by the
  null sets does not change conditional expectations.
* optional sampling for continuous martingales at (unbounded) stopping times;
* hitting-time inverses `levelTime`, the right-limit completed filtration `timeChangedFiltration`;
* the constancy lemma `ae_const_on_const_of_qv`;
* the time-changed process `tcProcess` and `timeChange_levy_hypotheses`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

section NullSets
variable {P : Measure Ω}

theorem measurableSet_sup_nullSets_iff {𝒜 : MeasurableSpace Ω} (h𝒜 : 𝒜 ≤ mΩ) (G : Set Ω) :
    MeasurableSet[𝒜 ⊔ nullSets P] G ↔
      ∃ G₀, MeasurableSet[𝒜] G₀ ∧ MeasurableSet[mΩ] G ∧ G =ᵐ[P] G₀ := by
  constructor
  · intro hG
    let m : MeasurableSpace Ω :=
      { MeasurableSet' := fun G => ∃ G₀, MeasurableSet[𝒜] G₀ ∧ MeasurableSet[mΩ] G ∧ G =ᵐ[P] G₀
        measurableSet_empty := ⟨∅, @MeasurableSet.empty _ 𝒜, @MeasurableSet.empty _ mΩ,
          Filter.EventuallyEq.rfl⟩
        measurableSet_compl := fun G ⟨G₀, h1, h2, h3⟩ =>
          ⟨G₀ᶜ, @MeasurableSet.compl _ _ 𝒜 h1, @MeasurableSet.compl _ _ mΩ h2, h3.compl⟩
        measurableSet_iUnion := fun f hf => by
          choose G₀ h1 h2 h3 using hf
          exact ⟨⋃ i, G₀ i, @MeasurableSet.iUnion _ _ 𝒜 _ _ h1,
            @MeasurableSet.iUnion _ _ mΩ _ _ h2, Filter.EventuallyEqSet.countable_iUnion h3⟩ }
    have h1 : 𝒜 ≤ m := fun G hG => ⟨G, hG, h𝒜 _ hG, Filter.EventuallyEq.rfl⟩
    have h2 : nullSets P ≤ m := MeasurableSpace.generateFrom_le fun G hG =>
      ⟨∅, @MeasurableSet.empty _ 𝒜, hG.1, ae_eq_empty.2 hG.2⟩
    exact (sup_le h1 h2) G hG
  · rintro ⟨G₀, h0, hG, hae⟩
    have hG₀ : MeasurableSet[mΩ] G₀ := h𝒜 _ h0
    have e1 : MeasurableSet[nullSets P] (G₀ \ G) :=
      MeasurableSpace.measurableSet_generateFrom ⟨hG₀.diff hG, (ae_eq_set.1 hae.symm).1⟩
    have e2 : MeasurableSet[nullSets P] (G \ G₀) :=
      MeasurableSpace.measurableSet_generateFrom ⟨hG.diff hG₀, (ae_eq_set.1 hae).1⟩
    have hsup : ∀ s, MeasurableSet[𝒜] s → MeasurableSet[𝒜 ⊔ nullSets P] s :=
      fun s hs => (le_sup_left : 𝒜 ≤ 𝒜 ⊔ nullSets P) s hs
    have hsup' : ∀ s, MeasurableSet[nullSets P] s → MeasurableSet[𝒜 ⊔ nullSets P] s :=
      fun s hs => (le_sup_right : nullSets P ≤ 𝒜 ⊔ nullSets P) s hs
    have : G = (G₀ \ (G₀ \ G)) ∪ (G \ G₀) := by
      ext x; by_cases h1 : x ∈ G₀ <;> by_cases h2 : x ∈ G <;> simp [h1, h2]
    rw [this]
    exact ((hsup _ h0).diff (hsup' _ e1)).union (hsup' _ e2)

theorem condExp_sup_nullSets [IsFiniteMeasure P] {𝒜 : MeasurableSpace Ω} (h𝒜 : 𝒜 ≤ mΩ)
    (f : Ω → ℝ) : P[f | 𝒜 ⊔ nullSets P] =ᵐ[P] P[f | 𝒜] := by
  have hle : 𝒜 ⊔ nullSets P ≤ mΩ := sup_le h𝒜 (nullSets_le P)
  by_cases hf : Integrable f P
  · refine (ae_eq_condExp_of_forall_setIntegral_eq hle hf (fun s _ _ => integrable_condExp.integrableOn)
      (fun s hs _ => ?_) ?_).symm
    · obtain ⟨G₀, h0, hG, hae⟩ := (measurableSet_sup_nullSets_iff h𝒜 s).1 hs
      rw [setIntegral_congr_set hae, setIntegral_congr_set hae, setIntegral_condExp h𝒜 hf h0]
    · exact (stronglyMeasurable_condExp.mono (le_sup_left : 𝒜 ≤ 𝒜 ⊔ nullSets P)).aestronglyMeasurable
  · rw [condExp_of_not_integrable hf, condExp_of_not_integrable hf]

end NullSets

section L2Tools

variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- A sequence bounded in `L²` is uniformly integrable (in `L¹`). -/
theorem uniformIntegrable_one_of_sq_bound {f : ℕ → Ω → ℝ} (hfm : ∀ n, Measurable (f n)) (hf : ∀ n, MemLp (f n) 2 P) {C : ℝ}
    (hC : ∀ n, ∫ ω, f n ω ^ 2 ∂P ≤ C) : UniformIntegrable f 1 P := by
  refine uniformIntegrable_of le_rfl ENNReal.one_ne_top (fun n => (hf n).aestronglyMeasurable)
    fun ε hε => ?_
  by_cases hεtop : ε = ⊤
  · exact ⟨1, fun i => by rw [hεtop]; exact le_top⟩
  have hεpos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
  set K : ℝ := max C 0 with hK
  obtain ⟨m, hm⟩ := exists_nat_gt (K / ε.toReal)
  have hm0 : (0 : ℝ) < m := lt_of_le_of_lt (div_nonneg (le_max_right _ _) hεpos.le) hm
  refine ⟨(m : ℝ≥0), fun i => ?_⟩
  have hint : Integrable (fun ω => f i ω ^ 2) P := (hf i).integrable_sq
  have hmeas : AEStronglyMeasurable ({x | (m : ℝ≥0) ≤ ‖f i x‖₊}.indicator (f i)) P :=
    (hfm i).aestronglyMeasurable.indicator
      (measurableSet_le measurable_const (hfm i).nnnorm)
  rw [eLpNorm_one_eq_lintegral_enorm hmeas]
  calc ∫⁻ x, ‖{x | (m : ℝ≥0) ≤ ‖f i x‖₊}.indicator (f i) x‖ₑ ∂P
      ≤ ∫⁻ x, ENNReal.ofReal (f i x ^ 2 / m) ∂P := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ {x | (m : ℝ≥0) ≤ ‖f i x‖₊}
        · rw [Set.indicator_of_mem hx, Real.enorm_eq_ofReal_abs]
          refine ENNReal.ofReal_le_ofReal ?_
          have hx' : (m : ℝ) ≤ |f i x| := by
            have : (m : ℝ≥0) ≤ ‖f i x‖₊ := hx
            have := (NNReal.coe_le_coe.2 this)
            simpa using this
          rw [le_div_iff₀ hm0, ← sq_abs, sq]
          nlinarith [abs_nonneg (f i x)]
        · rw [Set.indicator_of_notMem hx]; simp
    _ = ENNReal.ofReal (∫ x, f i x ^ 2 / m ∂P) := by
        rw [ofReal_integral_eq_lintegral_ofReal (hint.div_const _)
          (Eventually.of_forall fun x => by positivity)]
    _ ≤ ENNReal.ofReal ε.toReal := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_div, div_le_iff₀ hm0]
        have h1 := hC i
        have h2 : K / ε.toReal * ε.toReal = K := div_mul_cancel₀ _ hεpos.ne'
        nlinarith [le_max_left C 0]
    _ = ε := ENNReal.ofReal_toReal hεtop

/-- A.e. convergence plus an `L²` bound gives integrability of the limit and `L¹` convergence. -/
theorem tendsto_integral_abs_sub_of_sq_bound {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n, MemLp (f n) 2 P) {C : ℝ}
    (hC : ∀ n, ∫ ω, f n ω ^ 2 ∂P ≤ C)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) :
    Integrable g P ∧ Tendsto (fun n => ∫ ω, |f n ω - g ω| ∂P) atTop (𝓝 0) := by
  have hUI := uniformIntegrable_one_of_sq_bound hfm hf hC
  have hint : Integrable g P := hUI.integrable_of_ae_tendsto hlim
  refine ⟨hint, ?_⟩
  have hfm' : ∀ n, AEStronglyMeasurable (f n) P := fun n => (hfm n).aestronglyMeasurable
  have h1 := tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top hfm'
    (memLp_one_iff_integrable.2 hint) hUI.unifIntegrable hlim
  have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
  rw [ENNReal.toReal_zero] at h2
  refine h2.congr fun n => ?_
  have hi : Integrable (fun ω => f n ω - g ω) P := (memLp_one_iff_integrable.1
    ((hf n).mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2))).sub hint
  simp only [Function.comp]
  have e : f n - g = fun ω => f n ω - g ω := rfl
  rw [e, eLpNorm_one_eq_lintegral_enorm (hi.aestronglyMeasurable), ← ofReal_integral_norm_eq_lintegral_enorm hi,
    ENNReal.toReal_ofReal (integral_nonneg fun _ => norm_nonneg _)]
  simp only [Real.norm_eq_abs]

/-- Cauchy–Schwarz in `L²`. -/
theorem integral_abs_mul_le_sqrt {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    ∫ ω, |f ω| * |g ω| ∂P ≤ Real.sqrt (∫ ω, f ω ^ 2 ∂P) * Real.sqrt (∫ ω, g ω ^ 2 ∂P) := by
  have h := integral_mul_norm_le_Lp_mul_Lq (μ := P) (f := f) (g := g) (p := 2) (q := 2)
    Real.HolderConjugate.two_two (by simpa using hf) (by simpa using hg)
  simp only [Real.norm_eq_abs] at h
  have e1 : ∀ (k : Ω → ℝ), ∫ ω, |k ω| ^ (2 : ℝ) ∂P = ∫ ω, k ω ^ 2 ∂P := fun k => by
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp [sq_abs]
  rw [e1 f, e1 g] at h
  simpa [Real.sqrt_eq_rpow] using h


theorem integral_abs_le_sqrt {f : Ω → ℝ} (hf : MemLp f 2 P) :
    ∫ ω, |f ω| ∂P ≤ Real.sqrt (∫ ω, f ω ^ 2 ∂P) := by
  have h := integral_abs_mul_le_sqrt hf (memLp_const (1 : ℝ) : MemLp (fun _ : Ω => (1 : ℝ)) 2 P)
  simpa using h

theorem integral_abs_sq_sub_sq_le {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    ∫ ω, |f ω ^ 2 - g ω ^ 2| ∂P ≤
      Real.sqrt (∫ ω, (f ω - g ω) ^ 2 ∂P) * Real.sqrt (∫ ω, (f ω + g ω) ^ 2 ∂P) := by
  have h := integral_abs_mul_le_sqrt (hf.sub hg) (hf.add hg)
  have e : ∀ ω, |f ω ^ 2 - g ω ^ 2| = |f ω - g ω| * |f ω + g ω| := fun ω => by
    rw [← abs_mul]; congr 1; ring
  simp_rw [e]
  simpa using h


theorem integral_abs_sq_sub_sq_le' {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) {a b c : ℝ}
    (ha : ∫ ω, f ω ^ 2 ∂P ≤ a) (hb : ∫ ω, g ω ^ 2 ∂P ≤ b)
    (hc : ∫ ω, (f ω - g ω) ^ 2 ∂P ≤ c) :
    ∫ ω, |f ω ^ 2 - g ω ^ 2| ∂P ≤ Real.sqrt c * Real.sqrt (2 * a + 2 * b) := by
  refine (integral_abs_sq_sub_sq_le hf hg).trans ?_
  have h1 : ∫ ω, (f ω + g ω) ^ 2 ∂P ≤ 2 * a + 2 * b := by
    have hi : Integrable (fun ω => 2 * f ω ^ 2 + 2 * g ω ^ 2) P :=
      (hf.integrable_sq.const_mul 2).add (hg.integrable_sq.const_mul 2)
    calc ∫ ω, (f ω + g ω) ^ 2 ∂P ≤ ∫ ω, (2 * f ω ^ 2 + 2 * g ω ^ 2) ∂P :=
          integral_mono (hf.add hg).integrable_sq hi (fun ω => by nlinarith [sq_nonneg (f ω - g ω)])
      _ = 2 * ∫ ω, f ω ^ 2 ∂P + 2 * ∫ ω, g ω ^ 2 ∂P := by
          rw [integral_add (hf.integrable_sq.const_mul 2) (hg.integrable_sq.const_mul 2),
            integral_const_mul, integral_const_mul]
      _ ≤ 2 * a + 2 * b := by linarith
  exact mul_le_mul (Real.sqrt_le_sqrt hc) (Real.sqrt_le_sqrt h1) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _)

/-- Fatou's lemma for squares. -/
theorem integrable_sq_of_ae_tendsto {f : ℕ → Ω → ℝ} {g : Ω → ℝ} (hfm : ∀ n, Measurable (f n))
    (hgm : Measurable g) (hf : ∀ n, Integrable (fun ω => f n ω ^ 2) P) {K : ℝ}
    (hK : ∀ n, ∫ ω, f n ω ^ 2 ∂P ≤ K)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) :
    Integrable (fun ω => g ω ^ 2) P ∧ ∫ ω, g ω ^ 2 ∂P ≤ K := by
  have hK0 : 0 ≤ K := (integral_nonneg fun _ => sq_nonneg _).trans (hK 0)
  set F : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal (f n ω ^ 2) with hF
  have hFm : ∀ n, AEMeasurable (F n) P := fun n =>
    (ENNReal.measurable_ofReal.comp ((hfm n).pow_const 2)).aemeasurable
  have hlim' : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (𝓝 (ENNReal.ofReal (g ω ^ 2))) := by
    filter_upwards [hlim] with ω hω
    exact (ENNReal.tendsto_ofReal ((hω.pow 2)))
  have hlin : ∫⁻ ω, ENNReal.ofReal (g ω ^ 2) ∂P ≤ ENNReal.ofReal K := by
    calc ∫⁻ ω, ENNReal.ofReal (g ω ^ 2) ∂P = ∫⁻ ω, liminf (fun n => F n ω) atTop ∂P :=
          lintegral_congr_ae (hlim'.mono fun ω hω => hω.liminf_eq.symm)
      _ ≤ liminf (fun n => ∫⁻ ω, F n ω ∂P) atTop := lintegral_liminf_le' hFm
      _ ≤ ENNReal.ofReal K := by
          refine liminf_le_of_le (by isBoundedDefault) fun b hb => ?_
          obtain ⟨n, hn⟩ := hb.exists
          refine hn.trans ?_
          rw [hF]
          simp only
          rw [← ofReal_integral_eq_lintegral_ofReal (hf n) (Eventually.of_forall fun _ => sq_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (hK n)
  have hint : Integrable (fun ω => g ω ^ 2) P := by
    refine ⟨(hgm.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => sq_nonneg _)]
    exact lt_of_le_of_lt hlin ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  rw [← ENNReal.ofReal_le_ofReal_iff hK0,
    ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => sq_nonneg _)]
  exact hlin

end L2Tools

section OptionalSampling

variable {P : Measure Ω} [IsProbabilityMeasure P] {𝒢 : Filtration ℝ mΩ} {N : ℝ → Ω → ℝ}

/-- Bounded optional sampling in set-integral form. -/
theorem setIntegral_stoppedValue_eq_of_le_const (hN : Martingale N 𝒢 P)
    (hc : ∀ ω, Continuous fun s => N s ω) {σ : Ω → WithTop ℝ} (hσ : IsStoppingTime 𝒢 σ)
    {n : ℝ} (hσn : ∀ ω, σ ω ≤ (n : WithTop ℝ)) :
    Integrable (stoppedValue N σ) P ∧
      ∀ G, MeasurableSet[hσ.measurableSpace] G →
        ∫ ω in G, N n ω ∂P = ∫ ω in G, stoppedValue N σ ω ∂P := by
  have hsv : stoppedProcess N σ n = stoppedValue N σ := by
    funext ω; exact stoppedProcess_eq_of_ge (hσn ω)
  refine ⟨?_, fun G hG => ?_⟩
  · rw [← hsv]; exact (tendsto_setIntegral_stoppedProcess_dyadicUp hN hc hσ n ∅).1
  · have hmain := (tendsto_setIntegral_stoppedProcess_dyadicUp hN hc hσ n G).2
    rw [hsv] at hmain
    have hconst : ∀ m : ℕ, ∫ ω in G, stoppedProcess N (dyadicUp m σ) n ω ∂P = ∫ ω in G, N n ω ∂P := by
      intro m
      have hτ : IsStoppingTime 𝒢 (fun ω => min (n : WithTop ℝ) (dyadicUp m σ ω)) :=
        (isStoppingTime_const 𝒢 n).min (isStoppingTime_dyadicUp 𝒢 hσ m)
      have hle : ∀ ω, min (n : WithTop ℝ) (dyadicUp m σ ω) ≤ (n : WithTop ℝ) := fun ω => min_le_left _ _
      have hcd := stoppedValue_ae_eq_condExp_aux hN hτ hle
        (countable_range_min_const _ (countable_range_dyadicUp m σ))
      have hGm : MeasurableSet[hτ.measurableSpace] G :=
        hσ.measurableSpace_mono hτ (fun ω => le_min (hσn ω) (le_dyadicUp m σ ω)) G hG
      calc ∫ ω in G, stoppedProcess N (dyadicUp m σ) n ω ∂P
          = ∫ ω in G, (P[N n | hτ.measurableSpace]) ω ∂P := setIntegral_congr_ae
              (hτ.measurableSpace_le G hGm) (hcd.mono fun ω h _ => h)
        _ = ∫ ω in G, N n ω ∂P := setIntegral_condExp (hτ.measurableSpace_le) (hN.integrable n) hGm
    simp_rw [hconst] at hmain
    exact tendsto_nhds_unique tendsto_const_nhds hmain

theorem integrable_stoppedProcess_of_continuous (hN : Martingale N 𝒢 P)
    (hc : ∀ ω, Continuous fun s => N s ω) {ρ : Ω → WithTop ℝ} (hρ : IsStoppingTime 𝒢 ρ) (n : ℝ) :
    Integrable (stoppedProcess N ρ n) P :=
  (tendsto_setIntegral_stoppedProcess_dyadicUp hN hc hρ n ∅).1

/-- Optional sampling at unbounded finite stopping times, in the `L¹`-convergence form. -/
theorem setIntegral_stoppedValue_eq_of_le_core (hN : Martingale N 𝒢 P)
    (hc : ∀ ω, Continuous fun s => N s ω) {σ ρ : Ω → WithTop ℝ}
    (hσ : IsStoppingTime 𝒢 σ) (hρ : IsStoppingTime 𝒢 ρ) (hσρ : ∀ ω, σ ω ≤ ρ ω)
    (hρfin : ∀ ω, ρ ω ≠ ⊤)
    (hσint : Integrable (stoppedValue N σ) P) (hρint : Integrable (stoppedValue N ρ) P)
    (hρL1 : Tendsto (fun n : ℕ => ∫ ω, |stoppedProcess N ρ n ω - stoppedValue N ρ ω| ∂P) atTop
      (𝓝 0))
    {G : Set Ω} (hG : MeasurableSet[hσ.measurableSpace] G) :
    ∫ ω in G, stoppedValue N ρ ω ∂P = ∫ ω in G, stoppedValue N σ ω ∂P := by
  have hσfin : ∀ ω, σ ω ≠ ⊤ := fun ω => ne_top_of_le_ne_top (hρfin ω) (hσρ ω)
  set Gn : ℕ → Set Ω := fun n => G ∩ {ω | σ ω ≤ ((n : ℝ) : WithTop ℝ)} with hGn
  have hGnσ : ∀ n : ℕ, MeasurableSet[(hσ.min_const (n : ℝ)).measurableSpace] (Gn n) := fun n =>
    (hσ.measurableSet_inter_le_const_iff G n).1 (hG.inter (hσ.measurableSet_le' n))
  have hGnm : ∀ n : ℕ, MeasurableSet (Gn n) := fun n =>
    (hσ.measurableSpace_le G hG).inter (hσ.measurableSpace_le _ (hσ.measurableSet_le' n))
  have hmono : Monotone Gn := by
    intro m n hmn ω hω
    refine ⟨hω.1, ?_⟩
    have h1 : σ ω ≤ ((m : ℝ) : WithTop ℝ) := hω.2
    exact h1.trans (by exact_mod_cast (Nat.cast_le.2 hmn : (m : ℝ) ≤ n))
  have hunion : ⋃ n, Gn n = G := by
    ext ω
    simp only [hGn, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, h, -⟩; exact h
    · intro h
      obtain ⟨c, hc'⟩ := WithTop.ne_top_iff_exists.1 (hσfin ω)
      obtain ⟨n, hn⟩ := exists_nat_ge c
      exact ⟨n, h, by rw [← hc']; exact_mod_cast hn⟩
  -- the identity at level `n`
  have hlevel : ∀ n : ℕ, ∫ ω in Gn n, stoppedProcess N ρ n ω ∂P =
      ∫ ω in Gn n, stoppedValue N σ ω ∂P := by
    intro n
    have hσn : IsStoppingTime 𝒢 (fun ω => min (σ ω) ((n : ℝ) : WithTop ℝ)) := hσ.min_const n
    have hρn : IsStoppingTime 𝒢 (fun ω => min (ρ ω) ((n : ℝ) : WithTop ℝ)) := hρ.min_const n
    have hle1 : ∀ ω, min (σ ω) ((n : ℝ) : WithTop ℝ) ≤ ((n : ℝ) : WithTop ℝ) :=
      fun ω => min_le_right _ _
    have hle2 : ∀ ω, min (ρ ω) ((n : ℝ) : WithTop ℝ) ≤ ((n : ℝ) : WithTop ℝ) :=
      fun ω => min_le_right _ _
    have hG2 : MeasurableSet[hρn.measurableSpace] (Gn n) :=
      (hσn.measurableSpace_mono hρn (fun ω => min_le_min_right _ (hσρ ω))) _ (hGnσ n)
    have e1 := (setIntegral_stoppedValue_eq_of_le_const hN hc hσn hle1).2 _ (hGnσ n)
    have e2 := (setIntegral_stoppedValue_eq_of_le_const hN hc hρn hle2).2 _ hG2
    have e3 : ∫ ω in Gn n, stoppedValue N (fun ω => min (σ ω) ((n : ℝ) : WithTop ℝ)) ω ∂P =
        ∫ ω in Gn n, stoppedValue N σ ω ∂P := by
      refine setIntegral_congr_fun (hGnm n) fun ω hω => ?_
      have h1 : σ ω ≤ ((n : ℝ) : WithTop ℝ) := hω.2
      simp only [stoppedValue, min_eq_left h1]
    have e4 : ∫ ω in Gn n, stoppedValue N (fun ω => min (ρ ω) ((n : ℝ) : WithTop ℝ)) ω ∂P =
        ∫ ω in Gn n, stoppedProcess N ρ n ω ∂P := by
      refine setIntegral_congr_fun (hGnm n) fun ω hω => ?_
      simp only [stoppedValue, stoppedProcess, min_comm]
    rw [← e4, ← e2, e1, e3]
  have hXn : ∀ n : ℕ, Integrable (stoppedProcess N ρ n) P :=
    fun n => integrable_stoppedProcess_of_continuous hN hc hρ n
  -- limits
  have hlimσ : Tendsto (fun n => ∫ ω in Gn n, stoppedValue N σ ω ∂P) atTop
      (𝓝 (∫ ω in G, stoppedValue N σ ω ∂P)) := by
    have := tendsto_setIntegral_of_monotone hGnm hmono (by rw [hunion]; exact hσint.integrableOn)
    rwa [hunion] at this
  have hlimρ : Tendsto (fun n => ∫ ω in Gn n, stoppedValue N ρ ω ∂P) atTop
      (𝓝 (∫ ω in G, stoppedValue N ρ ω ∂P)) := by
    have := tendsto_setIntegral_of_monotone hGnm hmono (by rw [hunion]; exact hρint.integrableOn)
    rwa [hunion] at this
  have hdiff : Tendsto (fun n : ℕ => ∫ ω in Gn n, (stoppedProcess N ρ n ω - stoppedValue N ρ ω) ∂P)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) hρL1
    calc ‖∫ ω in Gn n, (stoppedProcess N ρ n ω - stoppedValue N ρ ω) ∂P‖
        ≤ ∫ ω in Gn n, ‖stoppedProcess N ρ n ω - stoppedValue N ρ ω‖ ∂P :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ ω, ‖stoppedProcess N ρ n ω - stoppedValue N ρ ω‖ ∂P :=
          setIntegral_le_integral ((hXn n).sub hρint).norm (Eventually.of_forall fun _ => norm_nonneg _)
      _ = ∫ ω, |stoppedProcess N ρ n ω - stoppedValue N ρ ω| ∂P := by
          simp only [Real.norm_eq_abs]
  have hlimX : Tendsto (fun n : ℕ => ∫ ω in Gn n, stoppedProcess N ρ n ω ∂P) atTop
      (𝓝 (∫ ω in G, stoppedValue N ρ ω ∂P)) := by
    have := hdiff.add hlimρ
    rw [zero_add] at this
    refine this.congr fun n => ?_
    rw [integral_sub (hXn n).integrableOn hρint.integrableOn, sub_add_cancel]
  have hlimX' : Tendsto (fun n : ℕ => ∫ ω in Gn n, stoppedProcess N ρ n ω ∂P) atTop
      (𝓝 (∫ ω in G, stoppedValue N σ ω ∂P)) := by
    simp_rw [hlevel]; exact hlimσ
  exact tendsto_nhds_unique hlimX hlimX'

theorem tendsto_stoppedProcess_nat {ρ : Ω → WithTop ℝ} (hρfin : ∀ ω, ρ ω ≠ ⊤) (ω : Ω) :
    Tendsto (fun n : ℕ => stoppedProcess N ρ n ω) atTop (𝓝 (stoppedValue N ρ ω)) := by
  obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.1 (hρfin ω)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop c] with n hn
  symm
  exact stoppedProcess_eq_of_ge (by rw [← hc]; exact_mod_cast hn)

omit [IsProbabilityMeasure P] in
theorem measurable_stoppedProcess_of_continuous (hN : Martingale N 𝒢 P)
    (hc : ∀ ω, Continuous fun s => N s ω) {ρ : Ω → WithTop ℝ} (hρ : IsStoppingTime 𝒢 ρ) (n : ℝ) :
    Measurable (stoppedProcess N ρ n) :=
  (hN.1.stronglyMeasurable_stoppedProcess hc hρ n).measurable

omit [IsProbabilityMeasure P] in
theorem measurable_stoppedValue_of_continuous (hN : Martingale N 𝒢 P)
    (hc : ∀ ω, Continuous fun s => N s ω) {ρ : Ω → WithTop ℝ} (hρ : IsStoppingTime 𝒢 ρ) :
    Measurable[hρ.measurableSpace] (stoppedValue N ρ) :=
  measurable_stoppedValue (hN.1.isStronglyProgressive_of_continuous hc) hρ

/-- **Optional sampling at unbounded stopping times** (B.2.2).  Corrected form of the interface
statement: the hypothesis `hL2` alone is vacuous when the squares are not integrable (the Bochner
integral of a non-integrable function is `0`), so integrability of the squares is assumed. -/
theorem setIntegral_stoppedValue_eq_of_le_of_memLp (hN : Martingale N 𝒢 P)
    (hc : ∀ ω, Continuous fun s => N s ω) {σ ρ : Ω → WithTop ℝ}
    (hσ : IsStoppingTime 𝒢 σ) (hρ : IsStoppingTime 𝒢 ρ) (hσρ : ∀ ω, σ ω ≤ ρ ω)
    (hρfin : ∀ ω, ρ ω ≠ ⊤) {C : ℝ}
    (hL2m : ∀ n : ℕ, MemLp (stoppedProcess N ρ n) 2 P)
    (hL2 : ∀ n : ℕ, ∫ ω, (stoppedProcess N ρ n ω) ^ 2 ∂P ≤ C)
    {G : Set Ω} (hG : MeasurableSet[hσ.measurableSpace] G) :
    Integrable (stoppedValue N ρ) P ∧ Integrable (stoppedValue N σ) P ∧
      ∫ ω in G, stoppedValue N ρ ω ∂P = ∫ ω in G, stoppedValue N σ ω ∂P := by
  have hσfin : ∀ ω, σ ω ≠ ⊤ := fun ω => ne_top_of_le_ne_top (hρfin ω) (hσρ ω)
  obtain ⟨hρint, hρL1⟩ := tendsto_integral_abs_sub_of_sq_bound
    (fun n : ℕ => measurable_stoppedProcess_of_continuous hN hc hρ n) hL2m hL2
    (Eventually.of_forall (tendsto_stoppedProcess_nat hρfin))
  -- the stopped values at `σ ∧ n` are conditional expectations of those at `ρ ∧ n`
  have hcond : ∀ n : ℕ, stoppedProcess N σ n =ᵐ[P]
      P[stoppedProcess N ρ n | (hσ.min_const (n : ℝ)).measurableSpace] := by
    intro n
    have hσn : IsStoppingTime 𝒢 (fun ω => min (σ ω) ((n : ℝ) : WithTop ℝ)) := hσ.min_const n
    have hρn : IsStoppingTime 𝒢 (fun ω => min (ρ ω) ((n : ℝ) : WithTop ℝ)) := hρ.min_const n
    have hle1 : ∀ ω, min (σ ω) ((n : ℝ) : WithTop ℝ) ≤ ((n : ℝ) : WithTop ℝ) :=
      fun ω => min_le_right _ _
    have hle2 : ∀ ω, min (ρ ω) ((n : ℝ) : WithTop ℝ) ≤ ((n : ℝ) : WithTop ℝ) :=
      fun ω => min_le_right _ _
    have hY : stoppedProcess N σ n = stoppedValue N (fun ω => min (σ ω) ((n : ℝ) : WithTop ℝ)) := by
      funext ω; simp only [stoppedProcess, stoppedValue, min_comm]
    have hX : stoppedProcess N ρ n = stoppedValue N (fun ω => min (ρ ω) ((n : ℝ) : WithTop ℝ)) := by
      funext ω; simp only [stoppedProcess, stoppedValue, min_comm]
    have hint : Integrable (stoppedProcess N ρ n) P :=
      integrable_stoppedProcess_of_continuous hN hc hρ n
    refine ae_eq_condExp_of_forall_setIntegral_eq (hσn.measurableSpace_le) hint
      (fun s _ _ => ?_) (fun s hs _ => ?_) ?_
    · rw [hY]; exact (setIntegral_stoppedValue_eq_of_le_const hN hc hσn hle1).1.integrableOn
    · have hs2 : MeasurableSet[hρn.measurableSpace] s :=
        (hσn.measurableSpace_mono hρn (fun ω => min_le_min_right _ (hσρ ω))) _ hs
      rw [hY, hX]
      have e1 := (setIntegral_stoppedValue_eq_of_le_const hN hc hσn hle1).2 s hs
      have e2 := (setIntegral_stoppedValue_eq_of_le_const hN hc hρn hle2).2 s hs2
      rw [← e1, ← e2]
    · rw [hY]
      exact (measurable_stoppedValue_of_continuous hN hc hσn).stronglyMeasurable.aestronglyMeasurable
  have hYm2 : ∀ n : ℕ, MemLp (stoppedProcess N σ n) 2 P := fun n =>
    (memLp_congr_ae (hcond n)).2 ((hL2m n).condExp (by norm_num))
  have hYC : ∀ n : ℕ, ∫ ω, (stoppedProcess N σ n ω) ^ 2 ∂P ≤ C := by
    intro n
    have h1 := integral_sq_sub_condExp (hσ.min_const (n : ℝ)).measurableSpace_le (hL2m n)
    have h2 : 0 ≤ ∫ ω, (stoppedProcess N ρ n ω - (P[stoppedProcess N ρ n |
        (hσ.min_const (n : ℝ)).measurableSpace]) ω) ^ 2 ∂P := integral_nonneg fun _ => sq_nonneg _
    have h3 : ∫ ω, (stoppedProcess N σ n ω) ^ 2 ∂P =
        ∫ ω, ((P[stoppedProcess N ρ n | (hσ.min_const (n : ℝ)).measurableSpace]) ω) ^ 2 ∂P :=
      integral_congr_ae ((hcond n).mono fun ω h => by simp only [h])
    linarith [hL2 n]
  obtain ⟨hσint, -⟩ := tendsto_integral_abs_sub_of_sq_bound
    (fun n : ℕ => measurable_stoppedProcess_of_continuous hN hc hσ n) hYm2 hYC
    (Eventually.of_forall (tendsto_stoppedProcess_nat hσfin))
  exact ⟨hρint, hσint, setIntegral_stoppedValue_eq_of_le_core hN hc hσ hρ hσρ hρfin hσint hρint hρL1 hG⟩

end OptionalSampling

/-! ### B.3  The level times -/

section LevelTime

/-- B.3: the first time a continuous nondecreasing process `A` (with `A 0 = 0`, `A → ∞`) reaches
level `u`. -/
noncomputable def levelTime (A : ℝ → Ω → ℝ) (u : ℝ) : Ω → WithTop ℝ :=
  hittingAfter A (Set.Ici u) 0

/-- The real value of `levelTime` (the junk value `0` is irrelevant when `levelTime ≠ ⊤`). -/
noncomputable def levelTimeR (A : ℝ → Ω → ℝ) (u : ℝ) (ω : Ω) : ℝ := (levelTime A u ω).untopA

theorem isStoppingTime_levelTime (𝒢 : Filtration ℝ mΩ) (A : ℝ → Ω → ℝ) (hA : Adapted 𝒢 A)
    (hc : ∀ ω, Continuous fun s => A s ω) (u : ℝ) : IsStoppingTime 𝒢 (levelTime A u) :=
  isStoppingTime_hittingAfter_Ici 𝒢 A hA hc u

section Pointwise

variable {A : ℝ → Ω → ℝ} {ω : Ω}

theorem levelTime_ne_top (htop : Tendsto (fun s => A s ω) atTop atTop) (u : ℝ) :
    levelTime A u ω ≠ ⊤ := by
  obtain ⟨s, hs0, hsu⟩ := ((eventually_ge_atTop (0 : ℝ)).and (htop.eventually_ge_atTop u)).exists
  exact ne_top_of_le_ne_top WithTop.coe_ne_top
    (hittingAfter_le_of_mem hs0 (show A s ω ∈ Set.Ici u from hsu))

theorem levelTime_nonneg (u : ℝ) : ((0 : ℝ) : WithTop ℝ) ≤ levelTime A u ω :=
  le_hittingAfter ω

theorem coe_levelTimeR {u : ℝ} (hne : levelTime A u ω ≠ ⊤) :
    ((levelTimeR A u ω : ℝ) : WithTop ℝ) = levelTime A u ω := by
  obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.1 hne
  simp only [levelTimeR, ← hc]
  simp

theorem levelTimeR_nonneg (htop : Tendsto (fun s => A s ω) atTop atTop) (u : ℝ) :
    0 ≤ levelTimeR A u ω := by
  have h := levelTime_nonneg (A := A) (ω := ω) u
  rw [← coe_levelTimeR (levelTime_ne_top htop u)] at h
  exact_mod_cast h

theorem levelTime_mono (ω : Ω) : Monotone fun u => levelTime A u ω := by
  intro u v huv
  exact hittingAfter_anti A 0 (Set.Ici_subset_Ici.2 huv : Set.Ici v ≤ Set.Ici u) ω

theorem levelTimeR_mono (htop : Tendsto (fun s => A s ω) atTop atTop) :
    Monotone fun u => levelTimeR A u ω := by
  intro u v huv
  have h : levelTime A u ω ≤ levelTime A v ω := levelTime_mono (A := A) ω huv
  rw [← coe_levelTimeR (levelTime_ne_top htop u), ← coe_levelTimeR (levelTime_ne_top htop v)] at h
  exact_mod_cast h

theorem levelTime_of_nonpos (h0 : A 0 ω = 0) {u : ℝ} (hu : u ≤ 0) : levelTime A u ω = 0 := by
  refine le_antisymm ?_ (levelTime_nonneg u)
  exact hittingAfter_le_of_mem (le_refl (0 : ℝ)) (show A 0 ω ∈ Set.Ici u by simp [h0, hu])

theorem levelTimeR_of_nonpos (h0 : A 0 ω = 0) {u : ℝ} (hu : u ≤ 0) : levelTimeR A u ω = 0 := by
  simp [levelTimeR, levelTime_of_nonpos h0 hu]

theorem levelTime_le_iff (hc : Continuous fun s => A s ω) (hm : Monotone fun s => A s ω) (u : ℝ)
    {s : ℝ} (hs : 0 ≤ s) : levelTime A u ω ≤ (s : WithTop ℝ) ↔ u ≤ A s ω := by
  rw [levelTime, hittingAfter_le_iff_of_isClosed A ω hc isClosed_Ici 0 s]
  constructor
  · rintro ⟨r, -, hrs, hr⟩
    exact le_trans hr (hm hrs)
  · intro h
    exact ⟨s, hs, le_rfl, h⟩

theorem lt_levelTime_iff (hc : Continuous fun s => A s ω) (hm : Monotone fun s => A s ω) (u : ℝ)
    {s : ℝ} (hs : 0 ≤ s) : (s : WithTop ℝ) < levelTime A u ω ↔ A s ω < u := by
  rw [← not_le, levelTime_le_iff hc hm u hs, not_le]

theorem levelTimeR_le_of_le (htop : Tendsto (fun s => A s ω) atTop atTop)
    (hc : Continuous fun s => A s ω) (hm : Monotone fun s => A s ω) {u s : ℝ} (hs : 0 ≤ s)
    (h : u ≤ A s ω) : levelTimeR A u ω ≤ s := by
  have := (levelTime_le_iff hc hm u hs).2 h
  rw [← coe_levelTimeR (levelTime_ne_top htop u)] at this
  exact_mod_cast this

/-- A continuous function that is `≤ c` on `[a, b)` is `≤ c` at `b`. -/
theorem le_of_forall_Ico_le {f : ℝ → ℝ} (hf : Continuous f) {a b c : ℝ} (hab : a < b)
    (h : ∀ r ∈ Set.Ico a b, f r ≤ c) : f b ≤ c := by
  have hcl : IsClosed {r | f r ≤ c} := isClosed_le hf continuous_const
  have : Set.Icc a b ⊆ {r | f r ≤ c} := by
    rw [← closure_Ico hab.ne]
    exact closure_minimal h hcl
  exact this ⟨hab.le, le_rfl⟩

theorem A_levelTimeR (htop : Tendsto (fun s => A s ω) atTop atTop)
    (hc : Continuous fun s => A s ω) (h0 : A 0 ω = 0) {u : ℝ} (hu : 0 ≤ u) :
    A (levelTimeR A u ω) ω = u := by
  have hne := levelTime_ne_top htop u
  have hcoe := coe_levelTimeR hne
  have hnn := levelTimeR_nonneg htop u
  apply le_antisymm
  · rcases hnn.eq_or_lt with h | h
    · rw [← h, h0]; exact hu
    · refine le_of_forall_Ico_le hc h fun r hr => ?_
      have hlt : (r : WithTop ℝ) < levelTime A u ω := by
        rw [← hcoe]; exact_mod_cast hr.2
      exact le_of_lt (not_le.1 (notMem_of_lt_hittingAfter hlt hr.1 : A r ω ∉ Set.Ici u))
  · exact mem_of_hittingAfter_eq_of_isClosed A ω hc isClosed_Ici 0 _ hcoe.symm

end Pointwise

end LevelTime

/-! ### B.4  The time-changed filtration -/

section TimeChangedFiltration

/-- B.4: the right-limit, completed, time-changed filtration
`ℱ'_u = (⋂_{v > u} 𝒢_{S_v}) ∨ nullSets P`. -/
noncomputable def timeChangedFiltration (P : Measure Ω) (𝒢 : Filtration ℝ mΩ) (A : ℝ → Ω → ℝ)
    (hA : Adapted 𝒢 A) (hc : ∀ ω, Continuous fun s => A s ω) : Filtration ℝ mΩ where
  seq u := (⨅ (v : ℝ) (_ : u < v), (isStoppingTime_levelTime 𝒢 A hA hc v).measurableSpace) ⊔
    nullSets P
  mono' := fun u u' h => sup_le_sup_right (le_iInf₂ fun v hv => iInf₂_le v (h.trans_lt hv)) _
  le' := fun u => sup_le ((iInf₂_le (u + 1) (by linarith)).trans
    (IsStoppingTime.measurableSpace_le _)) (nullSets_le P)

variable {P : Measure Ω} {𝒢 : Filtration ℝ mΩ} {A : ℝ → Ω → ℝ} {hA : Adapted 𝒢 A}
  {hc : ∀ ω, Continuous fun s => A s ω}

theorem timeChangedFiltration_isComplete :
    IsCompleteFiltration P (timeChangedFiltration P 𝒢 A hA hc) := by
  intro t s hs hP
  have h1 : MeasurableSet[nullSets P] s := MeasurableSpace.measurableSet_generateFrom ⟨hs, hP⟩
  exact (le_sup_right : nullSets P ≤ _) s h1

theorem timeChangedFiltration_apply (u : ℝ) :
    timeChangedFiltration P 𝒢 A hA hc u =
      (⨅ (v : ℝ) (_ : u < v), (isStoppingTime_levelTime 𝒢 A hA hc v).measurableSpace) ⊔
        nullSets P := rfl

/-- (F1) `𝒢_{S_u} ≤ ℱ'_u`. -/
theorem stoppingSigma_levelTime_le (u : ℝ) :
    (isStoppingTime_levelTime 𝒢 A hA hc u).measurableSpace ≤ timeChangedFiltration P 𝒢 A hA hc u := by
  refine le_trans ?_ (le_sup_left : _ ≤ _ ⊔ nullSets P)
  refine le_iInf₂ fun v hv => ?_
  exact (isStoppingTime_levelTime 𝒢 A hA hc u).measurableSpace_mono
    (isStoppingTime_levelTime 𝒢 A hA hc v) (fun ω => levelTime_mono ω hv.le)

/-- (F2) `ℱ'_u ≤ 𝒢_{S_v} ∨ nullSets P` for `u < v`. -/
theorem timeChangedFiltration_le (u v : ℝ) (huv : u < v) :
    timeChangedFiltration P 𝒢 A hA hc u ≤
      (isStoppingTime_levelTime 𝒢 A hA hc v).measurableSpace ⊔ nullSets P :=
  sup_le_sup_right (iInf₂_le v huv) _

/-- B.4.3: the stopping-time clause of `dambis_dubins_schwarz`. -/
theorem isStoppingTime_max_level (hm : ∀ ω, Monotone fun s => A s ω) (h0 : ∀ ω, A 0 ω = 0)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    IsStoppingTime (timeChangedFiltration P 𝒢 A hA hc)
      fun ω => ((max (A τ ω) 0 : ℝ) : WithTop ℝ) := by
  intro u
  have hAτ : ∀ ω, 0 ≤ A τ ω := fun ω => by simpa [h0 ω] using hm ω hτ
  have hset : {ω | ((max (A τ ω) 0 : ℝ) : WithTop ℝ) ≤ (u : WithTop ℝ)} = {ω | A τ ω ≤ u} := by
    ext ω
    simp only [Set.mem_ofPred_eq, WithTop.coe_le_coe, max_eq_left (hAτ ω)]
  rw [hset]
  rcases lt_or_ge u 0 with hu | hu
  · have : {ω | A τ ω ≤ u} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le hu (hAτ ω)
    rw [this]
    exact @MeasurableSet.empty _ (timeChangedFiltration P 𝒢 A hA hc u)
  · -- `{A τ ≤ u}` is in `⨅_{v > u} 𝒢_{S_v}`
    have hmem : MeasurableSet[⨅ (v : ℝ) (_ : u < v),
        (isStoppingTime_levelTime 𝒢 A hA hc v).measurableSpace] {ω | A τ ω ≤ u} := by
      rw [MeasurableSpace.measurableSet_iInf]
      intro v
      rw [MeasurableSpace.measurableSet_iInf]
      intro hv
      have hkey : {ω | A τ ω ≤ u} =
          ⋂ q : ℚ, ⋂ (_ : u < (q : ℝ) ∧ (q : ℝ) < v), {ω | A τ ω < (q : ℝ)} := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_iInter]
        constructor
        · intro h q hq
          exact lt_of_le_of_lt h hq.1
        · intro h
          by_contra hlt
          rw [not_le] at hlt
          obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_min hlt hv)
          have h1 := h q ⟨hq1, hq2.trans_le (min_le_right _ _)⟩
          have h2 := hq2.trans_le (min_le_left _ _)
          linarith
      rw [hkey]
      refine MeasurableSet.iInter fun q => MeasurableSet.iInter fun hq => ?_
      have hlevel : {ω | A τ ω < (q : ℝ)} =
          {ω | levelTime A (q : ℝ) ω ≤ (τ : WithTop ℝ)}ᶜ := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
        rw [lt_levelTime_iff (hc ω) (hm ω) _ hτ]
      rw [hlevel]
      refine MeasurableSet.compl ?_
      exact ((isStoppingTime_levelTime 𝒢 A hA hc (q : ℝ)).measurableSpace_mono
        (isStoppingTime_levelTime 𝒢 A hA hc v) (fun ω => levelTime_mono ω hq.2.le)) _
        ((isStoppingTime_levelTime 𝒢 A hA hc (q : ℝ)).measurableSet_le' τ)
    exact (le_sup_left : _ ≤ _ ⊔ nullSets P) _ hmem

end TimeChangedFiltration

/-! ### B.5  The constancy lemma -/

section Constancy

variable {P : Measure Ω} [IsProbabilityMeasure P] {𝒢 : Filtration ℝ mΩ} {N A : ℝ → Ω → ℝ}

/-- Hypotheses of the time-change lemmas B.5--B.6: `N` is a continuous `L²` martingale, started
at `0`, whose quadratic variation is the continuous nondecreasing adapted process `A` (with
`A 0 = 0`, `A → ∞`), i.e. `N² - A` is a martingale. -/
structure TCData (P : Measure Ω) (𝒢 : Filtration ℝ mΩ) (N A : ℝ → Ω → ℝ) : Prop where
  mart : Martingale N 𝒢 P
  cont : ∀ ω, Continuous fun s => N s ω
  zero : ∀ ω, N 0 ω = 0
  memLp : ∀ s, MemLp (N s) 2 P
  compensator : Martingale (fun s ω => N s ω ^ 2 - A s ω) 𝒢 P
  adapted : Adapted 𝒢 A
  contA : ∀ ω, Continuous fun s => A s ω
  monoA : ∀ ω, Monotone fun s => A s ω
  zeroA : ∀ ω, A 0 ω = 0
  topA : ∀ ω, Tendsto (fun s => A s ω) atTop atTop

/-- A continuous function equal to `c` at the rationals of `(a, b)` equals `c` on `[a, b]`. -/
theorem eq_on_Icc_of_forall_rat {f : ℝ → ℝ} (hf : Continuous f) {a b c : ℝ} (hab : a < b)
    (h : ∀ q : ℚ, a < (q : ℝ) → (q : ℝ) < b → f q = c) : ∀ s ∈ Set.Icc a b, f s = c := by
  have hIoo : Set.Ioo a b ⊆ {r | f r = c} := by
    intro s hs
    by_contra hne
    have hopen : IsOpen ({r | f r ≠ c} ∩ Set.Ioo a b) :=
      (isOpen_ne_fun hf continuous_const).inter isOpen_Ioo
    obtain ⟨q, hq⟩ := Rat.denseRange_cast.exists_mem_open hopen ⟨s, hne, hs⟩
    exact hq.1 (h q hq.2.1 hq.2.2)
  have : Set.Icc a b ⊆ {r | f r = c} := by
    rw [← closure_Ioo hab.ne]
    exact closure_minimal hIoo (isClosed_eq hf continuous_const)
  exact fun s hs => this hs

/-- Pathwise form of the constancy lemma, given the rational-endpoint information. -/
theorem const_of_good_rat {N A : ℝ → ℝ} (hNc : Continuous N) (hAm : Monotone A)
    (hgood : ∀ q q' : ℚ, 0 ≤ (q : ℝ) → q ≤ q' → A q' = A q → N q' = N q)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hAab : A b = A a) : ∀ s ∈ Set.Icc a b, N s = N a := by
  rcases hab.eq_or_lt with rfl | hab
  · intro s hs
    rw [le_antisymm hs.2 hs.1]
  obtain ⟨q₀, hq₀a, hq₀b⟩ := exists_rat_btwn hab
  have hAq : ∀ q : ℚ, a < (q : ℝ) → (q : ℝ) < b → A q = A a := fun q h1 h2 =>
    le_antisymm (hAab ▸ hAm h2.le) (hAm h1.le)
  have hconst : ∀ q : ℚ, a < (q : ℝ) → (q : ℝ) < b → N q = N q₀ := by
    intro q h1 h2
    have hq0 : (0 : ℝ) ≤ q₀ := ha.trans hq₀a.le
    rcases le_total q₀ q with hle | hle
    · exact hgood q₀ q hq0 hle ((hAq q h1 h2).trans (hAq q₀ hq₀a hq₀b).symm)
    · exact (hgood q q₀ (ha.trans h1.le) hle ((hAq q₀ hq₀a hq₀b).trans (hAq q h1 h2).symm)).symm
  have hall := eq_on_Icc_of_forall_rat hNc hab hconst
  intro s hs
  rw [hall s hs, hall a ⟨le_rfl, hab.le⟩]


namespace TCData

variable (h : TCData P 𝒢 N A)
include h

theorem stronglyAdapted_A : StronglyAdapted 𝒢 A := fun s => (h.adapted s).stronglyMeasurable

theorem measurable_A (s : ℝ) : Measurable (A s) := (h.adapted s).mono (𝒢.le s) le_rfl

theorem integrable_A (s : ℝ) : Integrable (A s) P := by
  have : A s = fun ω => N s ω ^ 2 - (N s ω ^ 2 - A s ω) := by funext ω; ring
  rw [this]
  exact (h.memLp s).integrable_sq.sub (h.compensator.integrable s)

theorem contQ (ω : Ω) : Continuous fun s => N s ω ^ 2 - A s ω :=
  ((h.cont ω).pow 2).sub (h.contA ω)

theorem nonneg_A (ω : Ω) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ A s ω := by
  simpa [h.zeroA ω] using h.monoA ω hs

/-- A stopping time with values in `[0, n]` takes real values there. -/
theorem exists_real_of_bdd {σ : Ω → WithTop ℝ} {n : ℝ} (h0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ σ ω)
    (hσn : ∀ ω, σ ω ≤ (n : WithTop ℝ)) (ω : Ω) : ∃ c : ℝ, σ ω = c ∧ 0 ≤ c ∧ c ≤ n := by
  obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top (hσn ω))
  refine ⟨c, hc.symm, ?_, ?_⟩
  · have := h0 ω; rw [← hc] at this; exact_mod_cast this
  · have := hσn ω; rw [← hc] at this; exact_mod_cast this

theorem integrable_stoppedValue_A {σ : Ω → WithTop ℝ} (hσ : IsStoppingTime 𝒢 σ)
    (h0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ σ ω) {n : ℝ} (hσn : ∀ ω, σ ω ≤ (n : WithTop ℝ)) :
    Integrable (stoppedValue A σ) P := by
  have hmeas : Measurable (stoppedValue A σ) :=
    (measurable_stoppedValue (h.stronglyAdapted_A.isStronglyProgressive_of_continuous h.contA)
      hσ).mono hσ.measurableSpace_le le_rfl
  refine Integrable.mono' (h.integrable_A n) hmeas.aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  obtain ⟨c, hc, hc0, hcn⟩ := h.exists_real_of_bdd h0 hσn ω
  have e : stoppedValue A σ ω = A c ω := by simp [stoppedValue, hc]
  rw [e, Real.norm_eq_abs, abs_of_nonneg (h.nonneg_A ω hc0)]
  exact h.monoA ω hcn

theorem integrable_stoppedValue_Q {σ : Ω → WithTop ℝ} (hσ : IsStoppingTime 𝒢 σ) {n : ℝ}
    (hσn : ∀ ω, σ ω ≤ (n : WithTop ℝ)) :
    Integrable (stoppedValue (fun s ω => N s ω ^ 2 - A s ω) σ) P :=
  (setIntegral_stoppedValue_eq_of_le_const h.compensator h.contQ hσ hσn).1

theorem memLp_stoppedValue_N {σ : Ω → WithTop ℝ} (hσ : IsStoppingTime 𝒢 σ)
    (h0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ σ ω) {n : ℝ} (hσn : ∀ ω, σ ω ≤ (n : WithTop ℝ)) :
    MemLp (stoppedValue N σ) 2 P := by
  have hmeas : Measurable (stoppedValue N σ) :=
    (measurable_stoppedValue_of_continuous h.mart h.cont hσ).mono hσ.measurableSpace_le le_rfl
  rw [memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable]
  have := (h.integrable_stoppedValue_Q hσ hσn).add (h.integrable_stoppedValue_A hσ h0 hσn)
  refine this.congr (Eventually.of_forall fun ω => ?_)
  simp only [stoppedValue, Pi.add_apply]
  ring

theorem integral_stoppedValue_mul {σ ρ : Ω → WithTop ℝ} (hσ : IsStoppingTime 𝒢 σ)
    (hρ : IsStoppingTime 𝒢 ρ) (h0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ σ ω)
    (hσρ : ∀ ω, σ ω ≤ ρ ω) {n : ℝ} (hρn : ∀ ω, ρ ω ≤ (n : WithTop ℝ)) :
    ∫ ω, stoppedValue N σ ω * stoppedValue N ρ ω ∂P = ∫ ω, stoppedValue N σ ω ^ 2 ∂P := by
  have hσn : ∀ ω, σ ω ≤ (n : WithTop ℝ) := fun ω => (hσρ ω).trans (hρn ω)
  have h0ρ : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ ρ ω := fun ω => (h0 ω).trans (hσρ ω)
  have hLσ := h.memLp_stoppedValue_N hσ h0 hσn
  have hLρ := h.memLp_stoppedValue_N hρ h0ρ hρn
  have hint_ρ := (setIntegral_stoppedValue_eq_of_le_const h.mart h.cont hρ hρn).1
  have hint_σ := (setIntegral_stoppedValue_eq_of_le_const h.mart h.cont hσ hσn).1
  have hstr : StronglyMeasurable[hσ.measurableSpace] (stoppedValue N σ) :=
    (measurable_stoppedValue_of_continuous h.mart h.cont hσ).stronglyMeasurable
  have hce : stoppedValue N σ =ᵐ[P] P[stoppedValue N ρ | hσ.measurableSpace] := by
    refine ae_eq_condExp_of_forall_setIntegral_eq hσ.measurableSpace_le hint_ρ
      (fun s _ _ => hint_σ.integrableOn) (fun s hs _ => ?_) hstr.aestronglyMeasurable
    have e1 := (setIntegral_stoppedValue_eq_of_le_const h.mart h.cont hσ hσn).2 s hs
    have e2 := (setIntegral_stoppedValue_eq_of_le_const h.mart h.cont hρ hρn).2 s
      (hσ.measurableSpace_mono hρ hσρ s hs)
    rw [← e1, ← e2]
  have hprod : Integrable (stoppedValue N σ * stoppedValue N ρ) P := hLσ.integrable_mul hLρ
  calc ∫ ω, stoppedValue N σ ω * stoppedValue N ρ ω ∂P
      = ∫ ω, (P[stoppedValue N σ * stoppedValue N ρ | hσ.measurableSpace]) ω ∂P :=
        (integral_condExp hσ.measurableSpace_le).symm
    _ = ∫ ω, (stoppedValue N σ * P[stoppedValue N ρ | hσ.measurableSpace]) ω ∂P :=
        integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hstr hprod hint_ρ)
    _ = ∫ ω, stoppedValue N σ ω ^ 2 ∂P := by
        refine integral_congr_ae (hce.mono fun ω hω => ?_)
        simp only [Pi.mul_apply, ← hω, sq]

/-- B.5.1: second-moment identity at bounded stopping times `0 ≤ σ ≤ ρ ≤ n`. -/
theorem integral_sq_stoppedValue_sub {σ ρ : Ω → WithTop ℝ} (hσ : IsStoppingTime 𝒢 σ)
    (hρ : IsStoppingTime 𝒢 ρ) (h0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ σ ω)
    (hσρ : ∀ ω, σ ω ≤ ρ ω) {n : ℝ} (hρn : ∀ ω, ρ ω ≤ (n : WithTop ℝ)) :
    ∫ ω, (stoppedValue N ρ ω - stoppedValue N σ ω) ^ 2 ∂P =
      ∫ ω, (stoppedValue A ρ ω - stoppedValue A σ ω) ∂P := by
  have hσn : ∀ ω, σ ω ≤ (n : WithTop ℝ) := fun ω => (hσρ ω).trans (hρn ω)
  have h0ρ : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ ρ ω := fun ω => (h0 ω).trans (hσρ ω)
  have hLσ := h.memLp_stoppedValue_N hσ h0 hσn
  have hLρ := h.memLp_stoppedValue_N hρ h0ρ hρn
  have hAσ := h.integrable_stoppedValue_A hσ h0 hσn
  have hAρ := h.integrable_stoppedValue_A hρ h0ρ hρn
  have hcross := h.integral_stoppedValue_mul hσ hρ h0 hσρ hρn
  -- `E Q_ρ = E Q_n = E Q_σ`
  have hQρ := (setIntegral_stoppedValue_eq_of_le_const h.compensator h.contQ hρ hρn).2 Set.univ
    MeasurableSet.univ
  have hQσ := (setIntegral_stoppedValue_eq_of_le_const h.compensator h.contQ hσ hσn).2 Set.univ
    MeasurableSet.univ
  simp only [Measure.restrict_univ] at hQρ hQσ
  have hQ : ∫ ω, stoppedValue (fun s ω => N s ω ^ 2 - A s ω) ρ ω ∂P =
      ∫ ω, stoppedValue (fun s ω => N s ω ^ 2 - A s ω) σ ω ∂P := hQρ.symm.trans hQσ
  have hQ' : ∀ τ : Ω → WithTop ℝ, MemLp (stoppedValue N τ) 2 P → Integrable (stoppedValue A τ) P →
      ∫ ω, stoppedValue (fun s ω => N s ω ^ 2 - A s ω) τ ω ∂P =
        ∫ ω, stoppedValue N τ ω ^ 2 ∂P - ∫ ω, stoppedValue A τ ω ∂P := by
    intro τ h1 h2
    exact integral_sub h1.integrable_sq h2
  rw [hQ' ρ hLρ hAρ, hQ' σ hLσ hAσ] at hQ
  have hexp : ∀ ω, (stoppedValue N ρ ω - stoppedValue N σ ω) ^ 2 =
      stoppedValue N ρ ω ^ 2 - 2 * (stoppedValue N σ ω * stoppedValue N ρ ω) +
        stoppedValue N σ ω ^ 2 := fun ω => by ring
  have i1 : Integrable (fun ω => stoppedValue N ρ ω ^ 2) P := hLρ.integrable_sq
  have i2 : Integrable (fun ω => stoppedValue N σ ω * stoppedValue N ρ ω) P :=
    hLσ.integrable_mul hLρ
  have i3 : Integrable (fun ω => stoppedValue N σ ω ^ 2) P := hLσ.integrable_sq
  have i4 : Integrable (fun ω => stoppedValue N ρ ω ^ 2 -
      2 * (stoppedValue N σ ω * stoppedValue N ρ ω)) P := i1.sub (i2.const_mul 2)
  have key : ∫ ω, (stoppedValue N ρ ω - stoppedValue N σ ω) ^ 2 ∂P =
      ∫ ω, stoppedValue N ρ ω ^ 2 ∂P - 2 * ∫ ω, stoppedValue N σ ω * stoppedValue N ρ ω ∂P +
        ∫ ω, stoppedValue N σ ω ^ 2 ∂P := by
    rw [show (fun ω => (stoppedValue N ρ ω - stoppedValue N σ ω) ^ 2) =
      fun ω => (stoppedValue N ρ ω ^ 2 - 2 * (stoppedValue N σ ω * stoppedValue N ρ ω)) +
        stoppedValue N σ ω ^ 2 from funext hexp, integral_add i4 i3, integral_sub i1 (i2.const_mul 2),
      integral_const_mul]
  rw [key, integral_sub hAρ hAσ]
  linarith

/-- B.5.2: almost surely, if `A` does not increase between `a` and `b` then `N b = N a`. -/
theorem ae_eq_of_qv_eq {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∀ᵐ ω ∂P, A b ω = A a ω → N b ω = N a ω := by
  set E : Set Ω := {ω | A b ω = A a ω} with hE
  have hEm : MeasurableSet E := measurableSet_eq_fun (h.measurable_A b) (h.measurable_A a)
  set f : Ω → ℝ := fun ω => (N b ω - N a ω) ^ 2 with hf
  have hfint : Integrable f P := ((h.memLp b).sub (h.memLp a)).integrable_sq
  have hfnn : ∀ ω, 0 ≤ f ω := fun ω => sq_nonneg _
  -- the key bound
  have hkey : ∀ ε : ℝ, 0 < ε → ∫ ω, E.indicator f ω ∂P ≤ ε := by
    intro ε hε
    set X : ℝ → Ω → ℝ := fun s ω => A (max s a) ω - A a ω with hX
    have hXad : Adapted 𝒢 X := by
      intro s
      by_cases hs : a ≤ s
      · have : X s = fun ω => A s ω - A a ω := by funext ω; simp [X, max_eq_left hs]
        rw [this]
        exact (h.adapted s).sub ((h.adapted a).mono (𝒢.mono hs) le_rfl)
      · have : X s = fun _ => 0 := by
          funext ω; simp [X, max_eq_right (le_of_not_ge hs)]
        rw [this]; exact measurable_const
    have hXc : ∀ ω, Continuous fun s => X s ω := fun ω =>
      ((h.contA ω).comp (continuous_id.max continuous_const)).sub continuous_const
    set T : Ω → WithTop ℝ := hittingAfter X (Set.Ici ε) a with hT
    have hTst : IsStoppingTime 𝒢 T :=
      isStoppingTime_hittingAfter_of_isClosed 𝒢 X hXad hXc isClosed_Ici a
    have hσ : IsStoppingTime 𝒢 (fun _ : Ω => (a : WithTop ℝ)) := isStoppingTime_const 𝒢 a
    have hρ : IsStoppingTime 𝒢 (fun ω => min (b : WithTop ℝ) (T ω)) :=
      (isStoppingTime_const 𝒢 b).min hTst
    have h0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ (fun _ : Ω => (a : WithTop ℝ)) ω :=
      fun ω => (WithTop.coe_le_coe.2 ha : ((0 : ℝ) : WithTop ℝ) ≤ (a : WithTop ℝ))
    have hσρ : ∀ ω, (fun _ : Ω => (a : WithTop ℝ)) ω ≤ (fun ω => min (b : WithTop ℝ) (T ω)) ω :=
      fun ω => le_min (WithTop.coe_le_coe.2 hab) (le_hittingAfter ω)
    have hρn : ∀ ω, (fun ω => min (b : WithTop ℝ) (T ω)) ω ≤ (b : WithTop ℝ) :=
      fun ω => min_le_left _ _
    have hiso := h.integral_sq_stoppedValue_sub hσ hρ h0 hσρ hρn
    have hσN : stoppedValue N (fun _ : Ω => (a : WithTop ℝ)) = N a := rfl
    have hσA : stoppedValue A (fun _ : Ω => (a : WithTop ℝ)) = A a := rfl
    rw [hσN, hσA] at hiso
    -- pointwise bounds
    have hAbound : ∀ ω, stoppedValue A (fun ω => min (b : WithTop ℝ) (T ω)) ω - A a ω ≤ ε := by
      intro ω
      obtain ⟨r, hr, hr0, hrb⟩ := h.exists_real_of_bdd (fun ω => (h0 ω).trans (hσρ ω)) hρn ω
      have hr' : (fun ω => min (b : WithTop ℝ) (T ω)) ω = r := hr
      have har : a ≤ r := by
        have h1 : (a : WithTop ℝ) ≤ (r : WithTop ℝ) := hr' ▸ hσρ ω
        exact WithTop.coe_le_coe.1 h1
      have hrT : (r : WithTop ℝ) ≤ T ω := by
        rw [← hr']; exact min_le_right _ _
      have e : stoppedValue A (fun ω => min (b : WithTop ℝ) (T ω)) ω = A r ω := by
        simp [stoppedValue, hr']
      rw [e]
      have hXr : X r ω ≤ ε := by
        rcases har.eq_or_lt with hra | hra
        · simp [X, ← hra]; exact hε.le
        · refine le_of_forall_Ico_le (hXc ω) hra fun s hs => ?_
          have hs' : (s : WithTop ℝ) < T ω := lt_of_lt_of_le (by exact_mod_cast hs.2) hrT
          exact le_of_lt (not_le.1 (notMem_of_lt_hittingAfter hs' hs.1 : X s ω ∉ Set.Ici ε))
      simpa [X, max_eq_left har] using hXr
    have hind : ∀ ω, E.indicator f ω ≤ (stoppedValue N (fun ω => min (b : WithTop ℝ) (T ω)) ω -
        N a ω) ^ 2 := by
      intro ω
      by_cases hω : ω ∈ E
      · rw [Set.indicator_of_mem hω]
        have hbT : (b : WithTop ℝ) < T ω := by
          by_contra hle
          rw [not_lt] at hle
          obtain ⟨r, har, hrb, hr⟩ :=
            (hittingAfter_le_iff_of_isClosed X ω (hXc ω) isClosed_Ici a b).1 hle
          have h1 : A r ω ≤ A b ω := h.monoA ω hrb
          have h2 : X r ω ≥ ε := hr
          have : X r ω = A r ω - A a ω := by simp [X, max_eq_left har]
          have hω' : A b ω = A a ω := hω
          linarith
        have : stoppedValue N (fun ω => min (b : WithTop ℝ) (T ω)) ω = N b ω := by
          simp [stoppedValue, min_eq_left hbT.le]
        rw [this]
      · rw [Set.indicator_of_notMem hω]; exact sq_nonneg _
    have hLρ : MemLp (stoppedValue N (fun ω => min (b : WithTop ℝ) (T ω))) 2 P :=
      h.memLp_stoppedValue_N hρ (fun ω => (h0 ω).trans (hσρ ω)) hρn
    have hint2 : Integrable (fun ω => (stoppedValue N (fun ω => min (b : WithTop ℝ) (T ω)) ω -
        N a ω) ^ 2) P := (hLρ.sub (h.memLp a)).integrable_sq
    calc ∫ ω, E.indicator f ω ∂P
        ≤ ∫ ω, (stoppedValue N (fun ω => min (b : WithTop ℝ) (T ω)) ω - N a ω) ^ 2 ∂P :=
          integral_mono (hfint.indicator hEm) hint2 hind
      _ = ∫ ω, (stoppedValue A (fun ω => min (b : WithTop ℝ) (T ω)) ω - A a ω) ∂P := hiso
      _ ≤ ∫ ω, ε ∂P := by
          refine integral_mono ?_ (integrable_const ε) hAbound
          exact (h.integrable_stoppedValue_A hρ (fun ω => (h0 ω).trans (hσρ ω)) hρn).sub
            (h.integrable_A a)
      _ = ε := by simp
  have hzero : ∫ ω, E.indicator f ω ∂P ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds tendsto_one_div_add_atTop_nhds_zero_nat
      (fun k : ℕ => hkey _ (by positivity))
  have hnn : 0 ≤ E.indicator f := fun ω => Set.indicator_nonneg (fun ω _ => hfnn ω) ω
  have heq : ∫ ω, E.indicator f ω ∂P = 0 :=
    le_antisymm hzero (integral_nonneg fun ω => hnn ω)
  have hae := (integral_eq_zero_iff_of_nonneg hnn (hfint.indicator hEm)).1 heq
  filter_upwards [hae] with ω hω hωE
  have h1 : E.indicator f ω = f ω := Set.indicator_of_mem (show ω ∈ E from hωE) f
  have h2 : f ω = 0 := by rw [← h1]; exact hω
  have : N b ω - N a ω = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 h2
  linarith

theorem ae_good_rat : ∀ᵐ ω ∂P, ∀ q q' : ℚ, 0 ≤ (q : ℝ) → q ≤ q' → A q' ω = A q ω →
    N q' ω = N q ω := by
  rw [ae_all_iff]; intro q; rw [ae_all_iff]; intro q'
  by_cases hq : 0 ≤ (q : ℝ) ∧ q ≤ q'
  · filter_upwards [h.ae_eq_of_qv_eq (b := (q' : ℝ)) hq.1 (Rat.cast_le.2 hq.2)] with ω hω h1 h2 h3
    exact hω h3
  · exact Eventually.of_forall fun ω h1 h2 => absurd ⟨h1, h2⟩ hq

/-- B.5.3, rational form (the interface statement): almost surely, `N` is constant on every
interval with rational endpoints on which `A` is constant. -/
theorem ae_const_on_const_of_qv : ∀ᵐ ω ∂P, ∀ a b : ℚ, 0 ≤ a → a ≤ b → A b ω = A a ω →
    ∀ s ∈ Set.Icc (a : ℝ) b, N s ω = N a ω := by
  filter_upwards [h.ae_good_rat] with ω hω a b ha hab hAab
  exact const_of_good_rat (h.cont ω) (h.monoA ω) hω (by exact_mod_cast ha)
    (by exact_mod_cast hab) hAab

/-- B.5.3, real form: almost surely, for all real `0 ≤ a ≤ b`, if `A b = A a` then `N` is constant
on `[a, b]`. -/
theorem ae_const_on_const_of_qv_real : ∀ᵐ ω ∂P, ∀ a b : ℝ, 0 ≤ a → a ≤ b → A b ω = A a ω →
    ∀ s ∈ Set.Icc a b, N s ω = N a ω := by
  filter_upwards [h.ae_good_rat] with ω hω a b ha hab hAab
  exact const_of_good_rat (h.cont ω) (h.monoA ω) hω ha hab hAab

end TCData

end Constancy

/-! ### B.6.3  The martingale property for the time-changed filtration -/

section MartingaleTimeChanged

variable {P : Measure Ω} [IsProbabilityMeasure P] {𝒢 : Filtration ℝ mΩ} {A : ℝ → Ω → ℝ}

theorem tendsto_setIntegral_of_tendsto_abs {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ n, Integrable (f n) P) (hg : Integrable g P)
    (hlim : Tendsto (fun n => ∫ ω, |f n ω - g ω| ∂P) atTop (𝓝 0)) (G : Set Ω) :
    Tendsto (fun n => ∫ ω in G, f n ω ∂P) atTop (𝓝 (∫ ω in G, g ω ∂P)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
  rw [← integral_sub (hf n).integrableOn hg.integrableOn]
  calc ‖∫ ω in G, (f n ω - g ω) ∂P‖ ≤ ∫ ω in G, ‖f n ω - g ω‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, ‖f n ω - g ω‖ ∂P :=
        setIntegral_le_integral ((hf n).sub hg).norm (Eventually.of_forall fun _ => norm_nonneg _)
    _ = ∫ ω, |f n ω - g ω| ∂P := by simp only [Real.norm_eq_abs]

/-- B.6.3: the stopped values `Y_{S_u}` of a continuous martingale `Y` form a martingale for the
right-limit completed filtration `ℱ'`, provided they are suitably `L¹`-regular. -/
theorem martingale_timeChanged {hA : Adapted 𝒢 A} {hAc : ∀ ω, Continuous fun s => A s ω}
    (htop : ∀ ω, Tendsto (fun s => A s ω) atTop atTop)
    {Y : ℝ → Ω → ℝ} (hY : Martingale Y 𝒢 P) (hYc : ∀ ω, Continuous fun s => Y s ω)
    (hYint : ∀ v, Integrable (stoppedValue Y (levelTime A v)) P)
    (hYL1 : ∀ v, Tendsto (fun n : ℕ => ∫ ω, |stoppedProcess Y (levelTime A v) n ω -
      stoppedValue Y (levelTime A v) ω| ∂P) atTop (𝓝 0))
    (hYright : ∀ u : ℝ, ∀ w : ℕ → ℝ, (∀ n, u < w n) → Tendsto w atTop (𝓝 u) →
      Tendsto (fun n => ∫ ω, |stoppedValue Y (levelTime A (w n)) ω -
        stoppedValue Y (levelTime A u) ω| ∂P) atTop (𝓝 0)) :
    Martingale (fun u ω => stoppedValue Y (levelTime A u) ω)
      (timeChangedFiltration P 𝒢 A hA hAc) P := by
  set ℱ' := timeChangedFiltration P 𝒢 A hA hAc with hℱ'
  have hst : ∀ u, IsStoppingTime 𝒢 (levelTime A u) := isStoppingTime_levelTime 𝒢 A hA hAc
  have hmeas : ∀ u, Measurable[ℱ' u] (stoppedValue Y (levelTime A u)) := fun u =>
    (measurable_stoppedValue_of_continuous hY hYc (hst u)).mono
      (stoppingSigma_levelTime_le u) le_rfl
  have hfin : ∀ ω v, levelTime A v ω ≠ ⊤ := fun ω v => levelTime_ne_top (htop ω) v
  refine ⟨fun u => (hmeas u).stronglyMeasurable, fun u v huv => ?_⟩
  rcases huv.eq_or_lt with rfl | huv
  · exact (condExp_of_stronglyMeasurable (ℱ'.le u) (hmeas u).stronglyMeasurable (hYint u)).eventuallyEq
  refine (ae_eq_condExp_of_forall_setIntegral_eq (ℱ'.le u) (hYint v)
    (fun s _ _ => (hYint u).integrableOn) (fun G hG _ => ?_)
    (hmeas u).stronglyMeasurable.aestronglyMeasurable).symm
  -- `G ∈ ℱ' u` differs from a set of `⋂_{w > u} 𝒢_{S_w}` by a null set
  have hle : (⨅ (v : ℝ) (_ : u < v), (hst v).measurableSpace) ≤ mΩ :=
    (iInf₂_le (u + 1) (by linarith)).trans (hst (u + 1)).measurableSpace_le
  obtain ⟨G₀, hG₀, hGm, hae⟩ := (measurableSet_sup_nullSets_iff hle G).1 hG
  rw [setIntegral_congr_set hae, setIntegral_congr_set hae]
  have hG₀' : ∀ w, u < w → MeasurableSet[(hst w).measurableSpace] G₀ := by
    intro w hw
    rw [MeasurableSpace.measurableSet_iInf] at hG₀
    have h1 := hG₀ w
    rw [MeasurableSpace.measurableSet_iInf] at h1
    exact h1 hw
  -- approximate `u` from the right by `w k = u + (v - u) / (k + 1)`
  set w : ℕ → ℝ := fun k => u + (v - u) * (1 / ((k : ℝ) + 1)) with hw
  have hwu : ∀ k, u < w k := fun k => by
    have : 0 < (v - u) * (1 / ((k : ℝ) + 1)) := mul_pos (sub_pos.2 huv) (by positivity)
    simp only [hw]; linarith
  have hwv : ∀ k, w k ≤ v := fun k => by
    have h1 : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have : (v - u) * (1 / ((k : ℝ) + 1)) ≤ v - u := mul_le_of_le_one_right (sub_pos.2 huv).le h1
    simp only [hw]; linarith
  have hwlim : Tendsto w atTop (𝓝 u) := by
    have := (tendsto_const_nhds (x := u)).add
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (v - u))
    rw [hw]
    simpa using this
  have hseq : ∀ k : ℕ, ∫ ω in G₀, stoppedValue Y (levelTime A (w k)) ω ∂P =
      ∫ ω in G₀, stoppedValue Y (levelTime A v) ω ∂P := fun k =>
    (setIntegral_stoppedValue_eq_of_le_core hY hYc (hst (w k)) (hst v)
      (fun ω => levelTime_mono ω (hwv k)) (hfin · v) (hYint (w k)) (hYint v) (hYL1 v)
      (hG₀' (w k) (hwu k))).symm
  have hlim := tendsto_setIntegral_of_tendsto_abs (fun k => hYint (w k)) (hYint u)
    (hYright u w hwu hwlim) G₀
  simp_rw [hseq] at hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim |>.symm

end MartingaleTimeChanged

/-! ### B.6  The time-changed process -/

section TimeChangeProcess

/-- B.6: the time-changed process `u ↦ N_{S_u}`, `S_u = levelTime A u`. -/
noncomputable def tcProcess (N A : ℝ → Ω → ℝ) (u : ℝ) (ω : Ω) : ℝ := N (levelTimeR A u ω) ω

theorem tcProcess_eq_stoppedValue {N A : ℝ → Ω → ℝ} (u : ℝ) :
    tcProcess N A u = stoppedValue N (levelTime A u) := rfl

section Pointwise6

variable {A N : ℝ → Ω → ℝ} {ω : Ω}

theorem levelTime_max_zero (h0 : A 0 ω = 0) (u : ℝ) : levelTime A (max u 0) ω = levelTime A u ω := by
  rcases le_total u 0 with hu | hu
  · rw [max_eq_right hu, levelTime_of_nonpos h0 le_rfl, levelTime_of_nonpos h0 hu]
  · rw [max_eq_left hu]

theorem levelTimeR_max_zero (h0 : A 0 ω = 0) (u : ℝ) :
    levelTimeR A (max u 0) ω = levelTimeR A u ω := by
  simp only [levelTimeR, levelTime_max_zero h0]

theorem A_levelTimeR_max (htop : Tendsto (fun s => A s ω) atTop atTop)
    (hc : Continuous fun s => A s ω) (h0 : A 0 ω = 0) (u : ℝ) :
    A (levelTimeR A u ω) ω = max u 0 := by
  rcases le_total u 0 with hu | hu
  · rw [levelTimeR_of_nonpos h0 hu, h0, max_eq_right hu]
  · rw [max_eq_left hu]; exact A_levelTimeR htop hc h0 hu

theorem tcProcess_of_nonpos (hN0 : N 0 ω = 0) (h0 : A 0 ω = 0) {u : ℝ} (hu : u ≤ 0) :
    tcProcess N A u ω = 0 := by
  simp [tcProcess, levelTimeR_of_nonpos h0 hu, hN0]

/-- Left-continuity of `u ↦ S_u` at `u₀ > 0`. -/
theorem tendsto_levelTimeR_nhdsLT (htop : Tendsto (fun s => A s ω) atTop atTop)
    (hc : Continuous fun s => A s ω) (hm : Monotone fun s => A s ω) (h0 : A 0 ω = 0)
    {u₀ : ℝ} (hu₀ : 0 < u₀) :
    Tendsto (fun u => levelTimeR A u ω) (𝓝[<] u₀) (𝓝 (levelTimeR A u₀ ω)) := by
  have hmono := levelTimeR_mono htop (A := A) (ω := ω)
  have hlim := hmono.tendsto_nhdsLT u₀
  set L := sSup ((fun u => levelTimeR A u ω) '' Set.Iio u₀) with hL
  have hev : ∀ᶠ u in 𝓝[<] u₀, 0 < u := by
    have : Set.Ioo 0 u₀ ∈ 𝓝[<] u₀ := Ioo_mem_nhdsLT hu₀
    filter_upwards [this] with u hu using hu.1
  have hAL : A L ω = u₀ := by
    have h1 := (hc.tendsto L).comp hlim
    have h2 : Tendsto (fun u => A (levelTimeR A u ω) ω) (𝓝[<] u₀) (𝓝 u₀) := by
      refine Tendsto.congr' ?_ ((continuous_id.tendsto u₀).mono_left nhdsWithin_le_nhds)
      filter_upwards [hev] with u hu
      exact (A_levelTimeR htop hc h0 hu.le).symm
    exact tendsto_nhds_unique h1 h2
  have hL0 : 0 ≤ L := ge_of_tendsto hlim (Eventually.of_forall fun u => levelTimeR_nonneg htop u)
  have h1 : levelTimeR A u₀ ω ≤ L := levelTimeR_le_of_le htop hc hm hL0 (le_of_eq hAL.symm)
  have h2 : L ≤ levelTimeR A u₀ ω := by
    refine le_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact hmono (le_of_lt hu)
  rwa [le_antisymm h2 h1] at hlim

/-- Right limit of `u ↦ S_u` at `u₀ ≥ 0`: it exists, `A` is constant `u₀` on `[S_{u₀}, T]`. -/
theorem exists_right_limit_levelTimeR (htop : Tendsto (fun s => A s ω) atTop atTop)
    (hc : Continuous fun s => A s ω) (h0 : A 0 ω = 0) {u₀ : ℝ} (hu₀ : 0 ≤ u₀) :
    ∃ T : ℝ, levelTimeR A u₀ ω ≤ T ∧ A T ω = u₀ ∧
      Tendsto (fun u => levelTimeR A u ω) (𝓝[>] u₀) (𝓝 T) := by
  have hmono := levelTimeR_mono htop (A := A) (ω := ω)
  have hlim := hmono.tendsto_nhdsGT u₀
  set T := sInf ((fun u => levelTimeR A u ω) '' Set.Ioi u₀) with hT
  refine ⟨T, ?_, ?_, hlim⟩
  · refine le_csInf ⟨_, ⟨u₀ + 1, by simp, rfl⟩⟩ ?_
    rintro _ ⟨u, hu, rfl⟩
    exact hmono (le_of_lt hu)
  · have h1 := (hc.tendsto T).comp hlim
    have h2 : Tendsto (fun u => A (levelTimeR A u ω) ω) (𝓝[>] u₀) (𝓝 u₀) := by
      refine Tendsto.congr' ?_ ((continuous_id.tendsto u₀).mono_left nhdsWithin_le_nhds)
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact (A_levelTimeR htop hc h0 (hu₀.trans (le_of_lt hu))).symm
    exact tendsto_nhds_unique h1 h2

end Pointwise6

section StopMin

variable {A : ℝ → Ω → ℝ} {ω : Ω}

/-- `S_u ∧ n`, the bounded version of the level time. -/
noncomputable def stopMin (A : ℝ → Ω → ℝ) (u : ℝ) (n : ℕ) : Ω → WithTop ℝ :=
  fun ω => min (levelTime A u ω) ((n : ℝ) : WithTop ℝ)

theorem stoppedProcess_levelTime_eq (F : ℝ → Ω → ℝ) (u : ℝ) (n : ℕ) :
    stoppedProcess F (levelTime A u) n = stoppedValue F (stopMin A u n) := by
  funext ω
  simp only [stoppedProcess, stoppedValue, stopMin, min_comm]

theorem stopMin_le (u : ℝ) (n : ℕ) (ω : Ω) : stopMin A u n ω ≤ ((n : ℝ) : WithTop ℝ) :=
  min_le_right _ _

theorem stopMin_nonneg (u : ℝ) (n : ℕ) (ω : Ω) : ((0 : ℝ) : WithTop ℝ) ≤ stopMin A u n ω :=
  le_min (levelTime_nonneg u) (by exact_mod_cast Nat.cast_nonneg n)

theorem stopMin_mono_u {u w : ℝ} (huw : u ≤ w) (n : ℕ) (ω : Ω) :
    stopMin A u n ω ≤ stopMin A w n ω :=
  min_le_min_right _ (levelTime_mono ω huw)

theorem stopMin_mono_n (u : ℝ) {n m : ℕ} (hnm : n ≤ m) (ω : Ω) :
    stopMin A u n ω ≤ stopMin A u m ω :=
  min_le_min_left _ (by exact_mod_cast (Nat.cast_le.2 hnm : (n : ℝ) ≤ m))

theorem stoppedValue_stopMin (htop : Tendsto (fun s => A s ω) atTop atTop) (F : ℝ → Ω → ℝ)
    (u : ℝ) (n : ℕ) :
    stoppedValue F (stopMin A u n) ω = F (min (levelTimeR A u ω) n) ω := by
  have hc := coe_levelTimeR (A := A) (ω := ω) (levelTime_ne_top htop u)
  simp only [stoppedValue, stopMin]
  rw [← hc]
  have e : min ((levelTimeR A u ω : ℝ) : WithTop ℝ) (((n : ℕ) : ℝ) : WithTop ℝ) =
      ((min (levelTimeR A u ω) (n : ℝ) : ℝ) : WithTop ℝ) := (WithTop.coe_min _ _).symm
  rw [e]
  simp only [WithTop.untopA, WithTop.untopD_coe]

theorem isStoppingTime_stopMin (𝒢 : Filtration ℝ mΩ) (hA : Adapted 𝒢 A)
    (hc : ∀ ω, Continuous fun s => A s ω) (u : ℝ) (n : ℕ) :
    IsStoppingTime 𝒢 (stopMin A u n) :=
  (isStoppingTime_levelTime 𝒢 A hA hc u).min_const (n : ℝ)

theorem monotone_sub_min_le {a : ℝ → ℝ} (ha : Monotone a) {s s' : ℝ} (hss' : s ≤ s') (k : ℝ) :
    a (min s' k) - a (min s k) ≤ a s' - a s := by
  rcases le_total s' k with h1 | h1
  · rw [min_eq_left h1, min_eq_left (hss'.trans h1)]
  · rw [min_eq_right h1]
    rcases le_total s k with h2 | h2
    · rw [min_eq_left h2]; linarith [ha h1]
    · rw [min_eq_right h2]; linarith [ha hss']

end StopMin

namespace TCData

variable {P : Measure Ω} [IsProbabilityMeasure P] {𝒢 : Filtration ℝ mΩ} {N A : ℝ → Ω → ℝ}
variable (h : TCData P 𝒢 N A)
include h

theorem A_levelTimeR_max' (ω : Ω) (u : ℝ) : A (levelTimeR A u ω) ω = max u 0 :=
  A_levelTimeR_max (h.topA ω) (h.contA ω) (h.zeroA ω) u

/-- B.6.1: almost surely the time-changed path is continuous. -/
theorem ae_continuous_tcProcess : ∀ᵐ ω ∂P, Continuous fun u => tcProcess N A u ω := by
  filter_upwards [h.ae_const_on_const_of_qv_real] with ω hω
  rw [continuous_iff_continuousAt]
  intro u₀
  have hz : ∀ u ≤ 0, tcProcess N A u ω = 0 := fun u hu =>
    tcProcess_of_nonpos (h.zero ω) (h.zeroA ω) hu
  rcases lt_or_ge u₀ 0 with hu₀ | hu₀
  · have : (fun u => tcProcess N A u ω) =ᶠ[𝓝 u₀] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hu₀] with u hu using hz u hu.le
    exact continuousAt_const.congr this.symm
  · rw [continuousAt_iff_continuous_left_right]
    constructor
    · rcases hu₀.eq_or_lt with h0 | hpos
      · subst h0
        exact continuousWithinAt_const.congr (fun u hu => hz u hu) (hz 0 le_rfl)
      · have hlt := tendsto_levelTimeR_nhdsLT (h.topA ω) (h.contA ω) (h.monoA ω) (h.zeroA ω) hpos
        have : ContinuousWithinAt (fun u => tcProcess N A u ω) (Set.Iio u₀) u₀ :=
          ((h.cont ω).continuousAt.tendsto).comp hlt
        exact continuousWithinAt_Iio_iff_Iic.1 this
    · obtain ⟨T, hT1, hT2, hlim⟩ :=
        exists_right_limit_levelTimeR (h.topA ω) (h.contA ω) (h.zeroA ω) hu₀
      have hSu := A_levelTimeR (h.topA ω) (h.contA ω) (h.zeroA ω) hu₀
      have hconst := hω (levelTimeR A u₀ ω) T (levelTimeR_nonneg (h.topA ω) u₀) hT1
        (hT2.trans hSu.symm) T ⟨hT1, le_rfl⟩
      have : ContinuousWithinAt (fun u => tcProcess N A u ω) (Set.Ioi u₀) u₀ := by
        have := ((h.cont ω).continuousAt.tendsto).comp hlim
        show Tendsto (fun u => tcProcess N A u ω) (𝓝[>] u₀) (𝓝 (tcProcess N A u₀ ω))
        have e : tcProcess N A u₀ ω = N T ω := hconst.symm
        rw [e]
        exact this
      exact continuousWithinAt_Ioi_iff_Ici.1 this

theorem memLp_stoppedProcess_levelTime (u : ℝ) (n : ℕ) :
    MemLp (stoppedProcess N (levelTime A u) n) 2 P := by
  rw [stoppedProcess_levelTime_eq]
  exact h.memLp_stoppedValue_N (isStoppingTime_stopMin 𝒢 h.adapted h.contA u n)
    (stopMin_nonneg u n) (stopMin_le u n)

theorem integrable_stoppedValue_A_stopMin (u : ℝ) (n : ℕ) :
    Integrable (stoppedValue A (stopMin A u n)) P :=
  h.integrable_stoppedValue_A (isStoppingTime_stopMin 𝒢 h.adapted h.contA u n)
    (stopMin_nonneg u n) (stopMin_le u n)

theorem stoppedValue_A_stopMin_bounds (u : ℝ) (n : ℕ) (ω : Ω) :
    0 ≤ stoppedValue A (stopMin A u n) ω ∧ stoppedValue A (stopMin A u n) ω ≤ max u 0 := by
  rw [stoppedValue_stopMin (h.topA ω)]
  refine ⟨h.nonneg_A ω (le_min (levelTimeR_nonneg (h.topA ω) u) (Nat.cast_nonneg n)), ?_⟩
  calc A (min (levelTimeR A u ω) n) ω ≤ A (levelTimeR A u ω) ω := h.monoA ω (min_le_left _ _)
    _ = max u 0 := h.A_levelTimeR_max' ω u

theorem integral_stopMin_A_le (u : ℝ) (n : ℕ) :
    ∫ ω, stoppedValue A (stopMin A u n) ω ∂P ≤ max u 0 := by
  have := integral_mono (h.integrable_stoppedValue_A_stopMin u n) (integrable_const (max u 0))
    (fun ω => (h.stoppedValue_A_stopMin_bounds u n ω).2)
  simpa using this

theorem tendsto_integral_stopMin_A (u : ℝ) :
    Tendsto (fun n : ℕ => ∫ ω, stoppedValue A (stopMin A u n) ω ∂P) atTop (𝓝 (max u 0)) := by
  have := tendsto_integral_of_dominated_convergence (μ := P)
    (F := fun (n : ℕ) ω => stoppedValue A (stopMin A u n) ω) (f := fun _ => max u 0)
    (fun _ => max u 0) (fun n => (h.integrable_stoppedValue_A_stopMin u n).aestronglyMeasurable)
    (integrable_const _)
    (fun n => Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (h.stoppedValue_A_stopMin_bounds u n ω).1]
      exact (h.stoppedValue_A_stopMin_bounds u n ω).2)
    (Eventually.of_forall fun ω => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (levelTimeR A u ω)] with n hn
      rw [stoppedValue_stopMin (h.topA ω), min_eq_left hn, h.A_levelTimeR_max' ω u])
  simpa using this

theorem integral_sq_stoppedProcess_levelTime (u : ℝ) (n : ℕ) :
    ∫ ω, (stoppedProcess N (levelTime A u) n ω) ^ 2 ∂P =
      ∫ ω, stoppedValue A (stopMin A u n) ω ∂P := by
  have hiso := h.integral_sq_stoppedValue_sub (isStoppingTime_const 𝒢 (0 : ℝ))
    (isStoppingTime_stopMin 𝒢 h.adapted h.contA u n) (fun _ => le_rfl) (stopMin_nonneg u n)
    (stopMin_le u n)
  have hN0 : stoppedValue N (fun _ : Ω => ((0 : ℝ) : WithTop ℝ)) = fun _ => 0 := by
    funext ω; simp only [stoppedValue, WithTop.untopA, WithTop.untopD_coe]; exact h.zero ω
  have hA0 : stoppedValue A (fun _ : Ω => ((0 : ℝ) : WithTop ℝ)) = fun _ => 0 := by
    funext ω; simp only [stoppedValue, WithTop.untopA, WithTop.untopD_coe]; exact h.zeroA ω
  rw [hN0, hA0] at hiso
  rw [stoppedProcess_levelTime_eq]
  simpa using hiso

theorem measurable_tcProcess (u : ℝ) : Measurable (tcProcess N A u) :=
  (measurable_stoppedValue_of_continuous h.mart h.cont
    (isStoppingTime_levelTime 𝒢 A h.adapted h.contA u)).mono
      (isStoppingTime_levelTime 𝒢 A h.adapted h.contA u).measurableSpace_le le_rfl

theorem tendsto_stoppedProcess_levelTime_pt (u : ℝ) (ω : Ω) :
    Tendsto (fun n : ℕ => stoppedProcess N (levelTime A u) n ω) atTop
      (𝓝 (tcProcess N A u ω)) :=
  tendsto_stoppedProcess_nat (fun ω => levelTime_ne_top (h.topA ω) u) ω

/-- B.6.2: `L²` bounds for the time-changed process and `L²` convergence along `n ↦ S_u ∧ n`. -/
theorem tcProcess_L2 (u : ℝ) :
    MemLp (tcProcess N A u) 2 P ∧ ∫ ω, tcProcess N A u ω ^ 2 ∂P ≤ max u 0 ∧
      Tendsto (fun n : ℕ => ∫ ω, (stoppedProcess N (levelTime A u) n ω -
        tcProcess N A u ω) ^ 2 ∂P) atTop (𝓝 0) := by
  have hXm : ∀ n : ℕ, Measurable (stoppedProcess N (levelTime A u) n) := fun n =>
    measurable_stoppedProcess_of_continuous h.mart h.cont
      (isStoppingTime_levelTime 𝒢 A h.adapted h.contA u) n
  have hβm := h.measurable_tcProcess u
  have hlim := h.tendsto_stoppedProcess_levelTime_pt u
  obtain ⟨hint, hbound⟩ := integrable_sq_of_ae_tendsto hXm hβm
    (fun n => (h.memLp_stoppedProcess_levelTime u n).integrable_sq) (K := max u 0)
    (fun n => by rw [h.integral_sq_stoppedProcess_levelTime]; exact h.integral_stopMin_A_le u n)
    (Eventually.of_forall hlim)
  refine ⟨(memLp_two_iff_integrable_sq hβm.aestronglyMeasurable).2 hint, hbound, ?_⟩
  -- Fatou on the differences
  set a : ℕ → ℝ := fun n => ∫ ω, stoppedValue A (stopMin A u n) ω ∂P with ha
  have hdiff : ∀ n : ℕ, ∫ ω, (tcProcess N A u ω - stoppedProcess N (levelTime A u) n ω) ^ 2 ∂P ≤
      max u 0 - a n := by
    intro n
    have hk : ∀ k : ℕ, ∫ ω, (stoppedProcess N (levelTime A u) ((n + k : ℕ) : ℝ) ω -
        stoppedProcess N (levelTime A u) (n : ℝ) ω) ^ 2 ∂P = a (n + k) - a n := by
      intro k
      have hiso := h.integral_sq_stoppedValue_sub
        (isStoppingTime_stopMin 𝒢 h.adapted h.contA u n)
        (isStoppingTime_stopMin 𝒢 h.adapted h.contA u (n + k)) (stopMin_nonneg u n)
        (fun ω => stopMin_mono_n u (Nat.le_add_right n k) ω) (stopMin_le u (n + k))
      rw [integral_sub (h.integrable_stoppedValue_A_stopMin u (n + k))
        (h.integrable_stoppedValue_A_stopMin u n)] at hiso
      simp only [stoppedProcess_levelTime_eq]
      rw [hiso]
    obtain ⟨-, hle⟩ := integrable_sq_of_ae_tendsto
      (f := fun k : ℕ => fun ω => stoppedProcess N (levelTime A u) ((n + k : ℕ) : ℝ) ω -
        stoppedProcess N (levelTime A u) (n : ℝ) ω)
      (g := fun ω => tcProcess N A u ω - stoppedProcess N (levelTime A u) (n : ℝ) ω)
      (fun k => (hXm (n + k)).sub (hXm n)) (hβm.sub (hXm n))
      (fun k => ((h.memLp_stoppedProcess_levelTime u (n + k)).sub
        (h.memLp_stoppedProcess_levelTime u n)).integrable_sq) (K := max u 0 - a n)
      (fun k => by
        rw [hk k]
        have := h.integral_stopMin_A_le u (n + k)
        simp only [ha] at this ⊢
        linarith)
      (Eventually.of_forall fun ω => by
        have := (Filter.tendsto_add_atTop_iff_nat (f := fun m : ℕ =>
          stoppedProcess N (levelTime A u) (m : ℝ) ω) n).2 (hlim ω)
        have h1 : Tendsto (fun k : ℕ => stoppedProcess N (levelTime A u) ((n + k : ℕ) : ℝ) ω)
            atTop (𝓝 (tcProcess N A u ω)) :=
          this.congr fun k => by rw [Nat.add_comm k n]
        exact h1.sub tendsto_const_nhds)
    exact hle
  refine squeeze_zero (g := fun n : ℕ => max u 0 - a n)
    (fun n => integral_nonneg fun _ => sq_nonneg _) (fun n => ?_) ?_
  · have := hdiff n
    have e : ∀ ω, (stoppedProcess N (levelTime A u) n ω - tcProcess N A u ω) ^ 2 =
        (tcProcess N A u ω - stoppedProcess N (levelTime A u) n ω) ^ 2 := fun ω => by ring
    simp_rw [e]
    exact this
  · have := (tendsto_const_nhds (x := max u 0)).sub (h.tendsto_integral_stopMin_A u)
    simpa using this

/-- B.6.2 (increments): `E (β_w - β_u)² ≤ w⁺ - u⁺` for `u ≤ w`. -/
theorem tcProcess_sub_L2 {u w : ℝ} (huw : u ≤ w) :
    Integrable (fun ω => (tcProcess N A w ω - tcProcess N A u ω) ^ 2) P ∧
      ∫ ω, (tcProcess N A w ω - tcProcess N A u ω) ^ 2 ∂P ≤ max w 0 - max u 0 := by
  have hXm : ∀ (v : ℝ) (n : ℕ), Measurable (stoppedProcess N (levelTime A v) n) := fun v n =>
    measurable_stoppedProcess_of_continuous h.mart h.cont
      (isStoppingTime_levelTime 𝒢 A h.adapted h.contA v) n
  refine integrable_sq_of_ae_tendsto
    (f := fun k : ℕ => fun ω => stoppedProcess N (levelTime A w) k ω -
      stoppedProcess N (levelTime A u) k ω)
    (fun k => (hXm w k).sub (hXm u k)) ((h.measurable_tcProcess w).sub (h.measurable_tcProcess u))
    (fun k => ((h.memLp_stoppedProcess_levelTime w k).sub
      (h.memLp_stoppedProcess_levelTime u k)).integrable_sq) (K := max w 0 - max u 0)
    (fun k => ?_)
    (Eventually.of_forall fun ω =>
      (h.tendsto_stoppedProcess_levelTime_pt w ω).sub (h.tendsto_stoppedProcess_levelTime_pt u ω))
  have hiso := h.integral_sq_stoppedValue_sub
    (isStoppingTime_stopMin 𝒢 h.adapted h.contA u k)
    (isStoppingTime_stopMin 𝒢 h.adapted h.contA w k) (stopMin_nonneg u k)
    (fun ω => stopMin_mono_u huw k ω) (stopMin_le w k)
  have e : ∀ ω, stoppedProcess N (levelTime A w) k ω - stoppedProcess N (levelTime A u) k ω =
      stoppedValue N (stopMin A w k) ω - stoppedValue N (stopMin A u k) ω := fun ω => by
    simp only [stoppedProcess_levelTime_eq]
  simp_rw [e]
  rw [hiso]
  have := integral_mono ((h.integrable_stoppedValue_A_stopMin w k).sub
    (h.integrable_stoppedValue_A_stopMin u k)) (integrable_const (max w 0 - max u 0))
    (fun ω => by
      simp only [Pi.sub_apply]
      rw [stoppedValue_stopMin (h.topA ω), stoppedValue_stopMin (h.topA ω)]
      have := monotone_sub_min_le (h.monoA ω) (levelTimeR_mono (h.topA ω) huw) k
      rwa [h.A_levelTimeR_max' ω w, h.A_levelTimeR_max' ω u] at this)
  simpa using this

theorem stoppedValue_levelTime_Q (v : ℝ) :
    stoppedValue (fun s ω => N s ω ^ 2 - A s ω) (levelTime A v) =
      fun ω => tcProcess N A v ω ^ 2 - max v 0 := by
  funext ω
  show N (levelTimeR A v ω) ω ^ 2 - A (levelTimeR A v ω) ω = _
  rw [h.A_levelTimeR_max' ω v]
  rfl

theorem memLp_tcProcess (v : ℝ) : MemLp (tcProcess N A v) 2 P := (h.tcProcess_L2 v).1

/-- `L¹`-continuity from the right of `u ↦ β_u`. -/
theorem tendsto_integral_abs_tcProcess {u : ℝ} {w : ℕ → ℝ} (hwu : ∀ n, u < w n)
    (hw : Tendsto w atTop (𝓝 u)) :
    Tendsto (fun n => ∫ ω, |tcProcess N A (w n) ω - tcProcess N A u ω| ∂P) atTop (𝓝 0) := by
  have hb : Tendsto (fun n => Real.sqrt (max (w n) 0 - max u 0)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => max (w n) 0 - max u 0) atTop (𝓝 (max u 0 - max u 0)) :=
      ((hw.max tendsto_const_nhds)).sub tendsto_const_nhds
    have h2 := (Real.continuous_sqrt.tendsto (max u 0 - max u 0)).comp h1
    rw [sub_self, Real.sqrt_zero] at h2
    exact h2
  refine squeeze_zero (fun n => integral_nonneg fun _ => abs_nonneg _) (fun n => ?_) hb
  exact (integral_abs_le_sqrt ((h.memLp_tcProcess (w n)).sub (h.memLp_tcProcess u))).trans
    (Real.sqrt_le_sqrt (h.tcProcess_sub_L2 (hwu n).le).2)

theorem martingale_tcProcess :
    Martingale (tcProcess N A) (timeChangedFiltration P 𝒢 A h.adapted h.contA) P := by
  refine martingale_timeChanged h.topA h.mart h.cont
    (fun v => (h.memLp_tcProcess v).integrable one_le_two) (fun v => ?_)
    (fun u w hwu hw => h.tendsto_integral_abs_tcProcess hwu hw)
  obtain ⟨-, -, hlim⟩ := h.tcProcess_L2 v
  have hb : Tendsto (fun n : ℕ => Real.sqrt (∫ ω, (stoppedProcess N (levelTime A v) n ω -
      tcProcess N A v ω) ^ 2 ∂P)) atTop (𝓝 0) := by
    have h2 := (Real.continuous_sqrt.tendsto 0).comp hlim
    rw [Real.sqrt_zero] at h2
    exact h2
  refine squeeze_zero (fun n => integral_nonneg fun _ => abs_nonneg _) (fun n => ?_) hb
  exact integral_abs_le_sqrt ((h.memLp_stoppedProcess_levelTime v n).sub (h.memLp_tcProcess v))

theorem martingale_tcProcess_sq_sub :
    Martingale (fun u ω => tcProcess N A u ω * tcProcess N A u ω - max u 0)
      (timeChangedFiltration P 𝒢 A h.adapted h.contA) P := by
  have hYint : ∀ v, Integrable (stoppedValue (fun s ω => N s ω ^ 2 - A s ω) (levelTime A v)) P := by
    intro v
    rw [h.stoppedValue_levelTime_Q v]
    exact (h.memLp_tcProcess v).integrable_sq.sub (integrable_const _)
  have hYL1 : ∀ v, Tendsto (fun n : ℕ => ∫ ω, |stoppedProcess (fun s ω => N s ω ^ 2 - A s ω)
      (levelTime A v) n ω - stoppedValue (fun s ω => N s ω ^ 2 - A s ω) (levelTime A v) ω| ∂P)
      atTop (𝓝 0) := by
    intro v
    obtain ⟨-, hβ2, hlim⟩ := h.tcProcess_L2 v
    have hb : Tendsto (fun n : ℕ => Real.sqrt (∫ ω, (stoppedProcess N (levelTime A v) n ω -
        tcProcess N A v ω) ^ 2 ∂P) * Real.sqrt (2 * max v 0 + 2 * max v 0) +
        (max v 0 - ∫ ω, stoppedValue A (stopMin A v n) ω ∂P)) atTop (𝓝 0) := by
      have h2 := (Real.continuous_sqrt.tendsto 0).comp hlim
      rw [Real.sqrt_zero] at h2
      have h3 := (h2.mul_const (Real.sqrt (2 * max v 0 + 2 * max v 0))).add
        ((tendsto_const_nhds (x := max v 0)).sub (h.tendsto_integral_stopMin_A v))
      simpa using h3
    refine squeeze_zero (fun n => integral_nonneg fun _ => abs_nonneg _) (fun n => ?_) hb
    have hXn := h.memLp_stoppedProcess_levelTime v n
    have hβ := h.memLp_tcProcess v
    have hi1 : Integrable (fun ω => |stoppedProcess N (levelTime A v) n ω ^ 2 -
        tcProcess N A v ω ^ 2|) P := (hXn.integrable_sq.sub hβ.integrable_sq).abs
    have hi2 : Integrable (fun ω => max v 0 - stoppedValue A (stopMin A v n) ω) P :=
      (integrable_const (max v 0)).sub (h.integrable_stoppedValue_A_stopMin v n)
    have hXsq : ∫ ω, stoppedProcess N (levelTime A v) n ω ^ 2 ∂P ≤ max v 0 := by
      rw [h.integral_sq_stoppedProcess_levelTime]; exact h.integral_stopMin_A_le v n
    have hbd := integral_abs_sq_sub_sq_le' hXn hβ hXsq hβ2 le_rfl
    calc ∫ ω, |stoppedProcess (fun s ω => N s ω ^ 2 - A s ω) (levelTime A v) n ω -
          stoppedValue (fun s ω => N s ω ^ 2 - A s ω) (levelTime A v) ω| ∂P
        ≤ ∫ ω, (|stoppedProcess N (levelTime A v) n ω ^ 2 - tcProcess N A v ω ^ 2| +
            (max v 0 - stoppedValue A (stopMin A v n) ω)) ∂P := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun ω => abs_nonneg _)
            (hi1.add hi2) (Eventually.of_forall fun ω => ?_)
          beta_reduce
          have hq : stoppedValue (fun s ω => N s ω ^ 2 - A s ω) (levelTime A v) ω =
              tcProcess N A v ω ^ 2 - max v 0 := congrFun (h.stoppedValue_levelTime_Q v) ω
          have hp : stoppedProcess (fun s ω => N s ω ^ 2 - A s ω) (levelTime A v) n ω =
              stoppedProcess N (levelTime A v) n ω ^ 2 - stoppedValue A (stopMin A v n) ω := by
            rw [stoppedProcess_levelTime_eq, stoppedProcess_levelTime_eq]; rfl
          rw [hq, hp]
          have hbnd := (h.stoppedValue_A_stopMin_bounds v n ω).2
          have h1 := le_abs_self (stoppedProcess N (levelTime A v) n ω ^ 2 - tcProcess N A v ω ^ 2)
          have h2 := neg_abs_le (stoppedProcess N (levelTime A v) n ω ^ 2 - tcProcess N A v ω ^ 2)
          rw [abs_le]
          constructor <;> linarith
      _ ≤ _ := by
          rw [integral_add hi1 hi2, integral_sub (integrable_const _)
            (h.integrable_stoppedValue_A_stopMin v n)]
          simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
          linarith
  have hYright : ∀ u : ℝ, ∀ w : ℕ → ℝ, (∀ n, u < w n) → Tendsto w atTop (𝓝 u) →
      Tendsto (fun n => ∫ ω, |stoppedValue (fun s ω => N s ω ^ 2 - A s ω) (levelTime A (w n)) ω -
        stoppedValue (fun s ω => N s ω ^ 2 - A s ω) (levelTime A u) ω| ∂P) atTop (𝓝 0) := by
    intro u w hwu hw
    have hd : Tendsto (fun n => max (w n) 0 - max u 0) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => max (w n) 0 - max u 0) atTop (𝓝 (max u 0 - max u 0)) :=
        ((hw.max tendsto_const_nhds)).sub tendsto_const_nhds
      rwa [sub_self] at h1
    have hb : Tendsto (fun n => Real.sqrt (max (w n) 0 - max u 0) *
        Real.sqrt (2 * max (w n) 0 + 2 * max u 0) + (max (w n) 0 - max u 0)) atTop (𝓝 0) := by
      have h2 := (Real.continuous_sqrt.tendsto 0).comp hd
      rw [Real.sqrt_zero] at h2
      have h4 : Tendsto (fun n => Real.sqrt (2 * max (w n) 0 + 2 * max u 0)) atTop
          (𝓝 (Real.sqrt (2 * max u 0 + 2 * max u 0))) := by
        refine (Real.continuous_sqrt.tendsto _).comp ?_
        exact (((hw.max tendsto_const_nhds).const_mul 2).add tendsto_const_nhds)
      have h3 := (h2.mul h4).add hd
      simpa using h3
    refine squeeze_zero (fun n => integral_nonneg fun _ => abs_nonneg _) (fun n => ?_) hb
    have hwu' := (hwu n).le
    obtain ⟨hint, hsub⟩ := h.tcProcess_sub_L2 hwu'
    have hmono : max u 0 ≤ max (w n) 0 := max_le_max hwu' le_rfl
    have hβw := h.memLp_tcProcess (w n)
    have hβu := h.memLp_tcProcess u
    have hi1 : Integrable (fun ω => |tcProcess N A (w n) ω ^ 2 - tcProcess N A u ω ^ 2|) P :=
      (hβw.integrable_sq.sub hβu.integrable_sq).abs
    have hbd := integral_abs_sq_sub_sq_le' hβw hβu (h.tcProcess_L2 (w n)).2.1
      (h.tcProcess_L2 u).2.1 hsub
    calc ∫ ω, |stoppedValue (fun s ω => N s ω ^ 2 - A s ω) (levelTime A (w n)) ω -
          stoppedValue (fun s ω => N s ω ^ 2 - A s ω) (levelTime A u) ω| ∂P
        ≤ ∫ ω, (|tcProcess N A (w n) ω ^ 2 - tcProcess N A u ω ^ 2| +
            (max (w n) 0 - max u 0)) ∂P := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun ω => abs_nonneg _)
            (hi1.add (integrable_const _)) (Eventually.of_forall fun ω => ?_)
          beta_reduce
          have hq1 : stoppedValue (fun s ω => N s ω ^ 2 - A s ω) (levelTime A (w n)) ω =
              tcProcess N A (w n) ω ^ 2 - max (w n) 0 :=
            congrFun (h.stoppedValue_levelTime_Q (w n)) ω
          have hq2 : stoppedValue (fun s ω => N s ω ^ 2 - A s ω) (levelTime A u) ω =
              tcProcess N A u ω ^ 2 - max u 0 := congrFun (h.stoppedValue_levelTime_Q u) ω
          rw [hq1, hq2]
          have h1 := le_abs_self (tcProcess N A (w n) ω ^ 2 - tcProcess N A u ω ^ 2)
          have h2 := neg_abs_le (tcProcess N A (w n) ω ^ 2 - tcProcess N A u ω ^ 2)
          rw [abs_le]
          constructor <;> linarith
      _ ≤ _ := by
          rw [integral_add hi1 (integrable_const _)]
          simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
          linarith
  have hmain := martingale_timeChanged (hA := h.adapted) (hAc := h.contA) h.topA
    (Y := fun s ω => N s ω ^ 2 - A s ω) h.compensator h.contQ hYint hYL1 hYright
  have e : (fun u ω => tcProcess N A u ω * tcProcess N A u ω - max u 0) =
      fun u ω => stoppedValue (fun s ω => N s ω ^ 2 - A s ω) (levelTime A u) ω := by
    funext u ω
    have hq : stoppedValue (fun s ω => N s ω ^ 2 - A s ω) (levelTime A u) ω =
        tcProcess N A u ω ^ 2 - max u 0 := congrFun (h.stoppedValue_levelTime_Q u) ω
    rw [hq]; ring
  rw [e]
  exact hmain

theorem measurable_tcProcess_timeChanged (u : ℝ) :
    Measurable[timeChangedFiltration P 𝒢 A h.adapted h.contA u] (tcProcess N A u) :=
  (measurable_stoppedValue_of_continuous h.mart h.cont
    (isStoppingTime_levelTime 𝒢 A h.adapted h.contA u)).mono
      (stoppingSigma_levelTime_le u) le_rfl

end TCData

/-- B.6.4 The Lévy hypotheses for the time-changed process. -/
theorem timeChange_levy_hypotheses {P : Measure Ω} [IsProbabilityMeasure P]
    {𝒢 : Filtration ℝ mΩ} {N A : ℝ → Ω → ℝ} (h : TCData P 𝒢 N A) :
    IsCompleteFiltration P (timeChangedFiltration P 𝒢 A h.adapted h.contA) ∧
      (∀ u, Measurable[timeChangedFiltration P 𝒢 A h.adapted h.contA u] (tcProcess N A u)) ∧
      (∀ ω, tcProcess N A 0 ω = 0) ∧
      (∀ᵐ ω ∂P, Continuous fun u => tcProcess N A u ω) ∧
      Martingale (tcProcess N A) (timeChangedFiltration P 𝒢 A h.adapted h.contA) P ∧
      Martingale (fun u ω => tcProcess N A u ω * tcProcess N A u ω - max u 0)
        (timeChangedFiltration P 𝒢 A h.adapted h.contA) P :=
  ⟨timeChangedFiltration_isComplete, h.measurable_tcProcess_timeChanged,
    fun ω => tcProcess_of_nonpos (h.zero ω) (h.zeroA ω) le_rfl, h.ae_continuous_tcProcess,
    h.martingale_tcProcess, h.martingale_tcProcess_sq_sub⟩

end TimeChangeProcess


end HRS
