import HRS.MS.R2ChaosAux1

/-!
# HRS.MS.R2ChaosAux2 -- abstract convergence in law tools for S9.4

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.

* `s94_abs_sub_integral_le`: for a bounded Lipschitz `F` and two random elements with `E‖A-B‖² ≤ D`,
  `|E F(A) - E F(B)| ≤ Lε + (M/ε²) D`.
* `s94_tid_of_approx`: "convergence together" across varying probability spaces: if `Y^{(j)}_N ⇒ Z^{(j)}` for each `j`,
  `E‖Z^{(j)}-Z‖² ≤ η_j → 0` and `limsup_N E‖Y^{(j)}_N - Y_N‖² ≤ η_j` then `Y_N ⇒ Z`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction

noncomputable section

namespace HRS.MS.R2Chaos

section Approx

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]

theorem s94_pointwise_le {F : E → ℝ} {M : ℝ} {L : ℝ≥0} (hbd : ∀ x y, |F x - F y| ≤ M)
    (hL : LipschitzWith L F) {ε : ℝ} (hε : 0 < ε) (a b : E) :
    |F a - F b| ≤ L * ε + M / ε ^ 2 * ‖a - b‖ ^ 2 := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hbd a b)
  have hlip : |F a - F b| ≤ L * ‖a - b‖ := by
    have := hL.dist_le_mul a b
    rwa [Real.dist_eq, dist_eq_norm] at this
  by_cases h : ‖a - b‖ < ε
  · calc |F a - F b| ≤ L * ‖a - b‖ := hlip
      _ ≤ L * ε := by gcongr
      _ ≤ _ := by have : 0 ≤ M / ε ^ 2 * ‖a - b‖ ^ 2 := by positivity
                  linarith
  · push Not at h
    have h1 : ε ^ 2 ≤ ‖a - b‖ ^ 2 := by gcongr
    have h2 : M ≤ M / ε ^ 2 * ‖a - b‖ ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      exact mul_le_mul_of_nonneg_left h1 hM
    have : 0 ≤ (L : ℝ) * ε := by positivity
    linarith [hbd a b]

theorem s94_abs_sub_integral_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {F : E → ℝ} {M : ℝ} {L : ℝ≥0} (hbd : ∀ x y, |F x - F y| ≤ M) (hL : LipschitzWith L F)
    (A B : Ω → E) (hA : AEMeasurable A P) (hB : AEMeasurable B P) {ε : ℝ} (hε : 0 < ε) {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∫⁻ ζ, ‖A ζ - B ζ‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal D) :
    |∫ ζ, F (A ζ) ∂P - ∫ ζ, F (B ζ) ∂P| ≤ L * ε + M / ε ^ 2 * D := by
  haveI : Nonempty Ω := nonempty_of_isProbabilityMeasure P
  obtain ⟨ζ₀⟩ := ‹Nonempty Ω›
  have hM : 0 ≤ M := (abs_nonneg _).trans (hbd (A ζ₀) (A ζ₀))
  have hFm : Measurable F := hL.continuous.measurable
  have hintA : Integrable (fun ζ => F (A ζ)) P := by
    refine Integrable.of_bound (hFm.comp_aemeasurable hA).aestronglyMeasurable (|F (A ζ₀)| + M)
      (ae_of_all _ fun ζ => ?_)
    have := hbd (A ζ) (A ζ₀)
    rw [Real.norm_eq_abs]
    linarith [abs_sub_abs_le_abs_sub (F (A ζ)) (F (A ζ₀))]
  have hintB : Integrable (fun ζ => F (B ζ)) P := by
    refine Integrable.of_bound (hFm.comp_aemeasurable hB).aestronglyMeasurable (|F (B ζ₀)| + M)
      (ae_of_all _ fun ζ => ?_)
    have := hbd (B ζ) (B ζ₀)
    rw [Real.norm_eq_abs]
    linarith [abs_sub_abs_le_abs_sub (F (B ζ)) (F (B ζ₀))]
  rw [← integral_sub hintA hintB]
  have h1 : ‖∫ ζ, (F (A ζ) - F (B ζ)) ∂P‖ ≤
      (∫⁻ ζ, ENNReal.ofReal ‖F (A ζ) - F (B ζ)‖ ∂P).toReal := norm_integral_le_lintegral_norm _
  have hc : 0 ≤ (L : ℝ) * ε := by positivity
  have h2 : ∫⁻ ζ, ENNReal.ofReal ‖F (A ζ) - F (B ζ)‖ ∂P ≤
      ∫⁻ ζ, (ENNReal.ofReal ((L : ℝ) * ε) + ENNReal.ofReal (M / ε ^ 2) * ‖A ζ - B ζ‖ₑ ^ 2) ∂P := by
    refine lintegral_mono fun ζ => ?_
    have := s94_pointwise_le hbd hL hε (A ζ) (B ζ)
    rw [Real.norm_eq_abs]
    calc ENNReal.ofReal |F (A ζ) - F (B ζ)|
        ≤ ENNReal.ofReal ((L : ℝ) * ε + M / ε ^ 2 * ‖A ζ - B ζ‖ ^ 2) := ENNReal.ofReal_le_ofReal this
      _ = _ := by
        have hq : 0 ≤ M / ε ^ 2 := by positivity
        rw [ENNReal.ofReal_add hc (by positivity), ENNReal.ofReal_mul hq,
          ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  have h3 : ∫⁻ ζ, (ENNReal.ofReal ((L : ℝ) * ε) + ENNReal.ofReal (M / ε ^ 2) * ‖A ζ - B ζ‖ₑ ^ 2) ∂P ≤
      ENNReal.ofReal ((L : ℝ) * ε) + ENNReal.ofReal (M / ε ^ 2) * ENNReal.ofReal D := by
    rw [lintegral_add_left measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    simp only [lintegral_const, measure_univ, mul_one]
    gcongr
  have h4 : (∫⁻ ζ, ENNReal.ofReal ‖F (A ζ) - F (B ζ)‖ ∂P) ≤
      ENNReal.ofReal ((L : ℝ) * ε + M / ε ^ 2 * D) := by
    refine (h2.trans h3).trans (le_of_eq ?_)
    have hq : 0 ≤ M / ε ^ 2 := by positivity
    rw [ENNReal.ofReal_add hc (by positivity), ENNReal.ofReal_mul hq]
  have h5 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h4
  rw [ENNReal.toReal_ofReal (by positivity)] at h5
  rw [← Real.norm_eq_abs]
  exact h1.trans h5

theorem s94_integral_map_F {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {F : E → ℝ} (hF : Continuous F)
    (A : Ω → E) (hA : AEMeasurable A P) : ∫ x, F x ∂(P.map A) = ∫ ζ, F (A ζ) ∂P :=
  integral_map hA hF.aestronglyMeasurable

/-- Convergence together across varying probability spaces (bounded Lipschitz test functions). -/
theorem s94_tid_of_approx {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)] {P : ∀ N, Measure (Ω N)}
    [∀ N, IsProbabilityMeasure (P N)] {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] (Y : ∀ N, Ω N → E) (Z : Ω' → E) (Yj : ℕ → ∀ N, Ω N → E)
    (Zj : ℕ → Ω' → E) (hY : ∀ N, AEMeasurable (Y N) (P N)) (hZ : AEMeasurable Z P')
    (hYj : ∀ j N, AEMeasurable (Yj j N) (P N)) (hZj : ∀ j, AEMeasurable (Zj j) P')
    (h1 : ∀ j, TendstoInDistribution (Yj j) atTop (Zj j) P P')
    (η : ℕ → ℝ) (hη0 : ∀ j, 0 ≤ η j) (hη : Tendsto η atTop (𝓝 0))
    (h2 : ∀ j, ∫⁻ ζ, ‖Zj j ζ - Z ζ‖ₑ ^ 2 ∂P' ≤ ENNReal.ofReal (η j))
    (h3 : ∀ j, ∀ᶠ N in atTop, ∫⁻ ζ, ‖Yj j N ζ - Y N ζ‖ₑ ^ 2 ∂(P N) ≤ ENNReal.ofReal (η j)) :
    TendstoInDistribution Y atTop Z P P' := by
  refine ⟨hY, hZ, ?_⟩
  refine tendsto_iff_forall_lipschitz_integral_tendsto.2 ?_
  rintro F ⟨M, hM⟩ ⟨L, hL⟩
  have hbd : ∀ x y, |F x - F y| ≤ M := fun x y => by simpa [Real.dist_eq] using hM x y
  have hFc : Continuous F := hL.continuous
  have hM0 : 0 ≤ M := by
    haveI : Nonempty Ω' := nonempty_of_isProbabilityMeasure P'
    obtain ⟨ζ⟩ := ‹Nonempty Ω'›
    exact (abs_nonneg _).trans (hbd (Z ζ) (Z ζ))
  have e1 : ∀ N, ∫ x, F x ∂(((⟨(P N).map (Y N), inferInstance⟩ : ProbabilityMeasure E)) : Measure E) =
      ∫ ζ, F (Y N ζ) ∂(P N) := fun N => s94_integral_map_F hFc _ (hY N)
  have e2 : ∫ x, F x ∂(((⟨P'.map Z, inferInstance⟩ : ProbabilityMeasure E)) : Measure E) =
      ∫ ζ, F (Z ζ) ∂P' := s94_integral_map_F hFc _ hZ
  have hj : ∀ j, Tendsto (fun N => ∫ ζ, F (Yj j N ζ) ∂(P N)) atTop (𝓝 (∫ ζ, F (Zj j ζ) ∂P')) := by
    intro j
    have := (tendsto_iff_forall_lipschitz_integral_tendsto.1 (h1 j).tendsto) F ⟨M, hM⟩ ⟨L, hL⟩
    have e1' : ∀ N, ∫ x, F x ∂(((⟨(P N).map (Yj j N), inferInstance⟩ : ProbabilityMeasure E)) : Measure E) =
        ∫ ζ, F (Yj j N ζ) ∂(P N) := fun N => s94_integral_map_F hFc _ (hYj j N)
    have e2' : ∫ x, F x ∂(((⟨P'.map (Zj j), inferInstance⟩ : ProbabilityMeasure E)) : Measure E) =
        ∫ ζ, F (Zj j ζ) ∂P' := s94_integral_map_F hFc _ (hZj j)
    exact e2' ▸ (tendsto_congr e1').1 this
  suffices key : Tendsto (fun N => ∫ ζ, F (Y N ζ) ∂(P N)) atTop (𝓝 (∫ ζ, F (Z ζ) ∂P')) by
    rw [← e2] at key
    exact (tendsto_congr e1).2 key
  rw [Metric.tendsto_nhds]
  intro η0 hη0pos
  set ε : ℝ := η0 / (8 * ((L : ℝ) + 1)) with hε
  have hLp : 0 < (L : ℝ) + 1 := by positivity
  have hεpos : 0 < ε := by positivity
  have hLε : (L : ℝ) * ε ≤ η0 / 8 := by
    rw [hε, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [NNReal.coe_nonneg L]
  have hsmall : ∀ᶠ j in atTop, M / ε ^ 2 * η j < η0 / 8 := by
    have : Tendsto (fun j => M / ε ^ 2 * η j) atTop (𝓝 (M / ε ^ 2 * 0)) := hη.const_mul _
    rw [mul_zero] at this
    exact this.eventually (gt_mem_nhds (by positivity))
  obtain ⟨j, hjs⟩ := hsmall.exists
  have hZb : |∫ ζ, F (Zj j ζ) ∂P' - ∫ ζ, F (Z ζ) ∂P'| ≤ L * ε + M / ε ^ 2 * η j :=
    s94_abs_sub_integral_le hbd hL _ _ (hZj j) hZ hεpos (hη0 j) (h2 j)
  filter_upwards [h3 j, (Metric.tendsto_nhds.1 (hj j)) (η0 / 4) (by positivity)] with N hN hN2
  have hYb : |∫ ζ, F (Yj j N ζ) ∂(P N) - ∫ ζ, F (Y N ζ) ∂(P N)| ≤ L * ε + M / ε ^ 2 * η j :=
    s94_abs_sub_integral_le hbd hL _ _ (hYj j N) (hY N) hεpos (hη0 j) hN
  rw [Real.dist_eq] at hN2 ⊢
  have := abs_sub_le (∫ ζ, F (Y N ζ) ∂(P N)) (∫ ζ, F (Yj j N ζ) ∂(P N)) (∫ ζ, F (Z ζ) ∂P')
  have h6 := abs_sub_le (∫ ζ, F (Yj j N ζ) ∂(P N)) (∫ ζ, F (Zj j ζ) ∂P') (∫ ζ, F (Z ζ) ∂P')
  rw [abs_sub_comm] at hYb
  linarith [abs_sub_comm (∫ ζ, F (Y N ζ) ∂(P N)) (∫ ζ, F (Yj j N ζ) ∂(P N))]

end Approx

section UI

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]

theorem s94_trunc_tendsto {μs : ℕ → ProbabilityMeasure E} {μ : ProbabilityMeasure E}
    (h : Tendsto μs atTop (𝓝 μ)) {g : E → ℝ} (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x) (K : ℝ)
    (hK : 0 ≤ K) :
    Tendsto (fun n => ∫ x, min (g x) K ∂(μs n : Measure E)) atTop
      (𝓝 (∫ x, min (g x) K ∂(μ : Measure E))) := by
  let f : E →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨fun x => min (g x) K, hg.min continuous_const⟩ K
    (fun x y => by
      show dist (min (g x) K) (min (g y) K) ≤ K
      rw [Real.dist_eq, abs_le]
      have h1 := le_min (hg0 x) hK
      have h2 := le_min (hg0 y) hK
      have h3 := min_le_right (g x) K
      have h4 := min_le_right (g y) K
      constructor <;> linarith)
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 h) f

theorem s94_integral_sub_trunc_le {ν : Measure E} [IsProbabilityMeasure ν] {g : E → ℝ}
    (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x) {q : ℝ} (hq : 1 < q) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∫⁻ x, ENNReal.ofReal (g x ^ q) ∂ν ≤ ENNReal.ofReal M) {K : ℝ} (hK : 0 < K) :
    Integrable g ν ∧ ∫ x, g x ∂ν - ∫ x, min (g x) K ∂ν ≤ K ^ (1 - q) * M := by
  have hgm : Measurable g := hg.measurable
  have hgq : Measurable fun x => g x ^ q := hgm.pow_const q
  have hiq : Integrable (fun x => g x ^ q) ν := by
    refine ⟨hgq.aestronglyMeasurable, ?_⟩
    have : ∀ x, ‖g x ^ q‖ₑ = ENNReal.ofReal (g x ^ q) := fun x => by
      rw [← ofReal_norm_eq_enorm, Real.norm_of_nonneg (Real.rpow_nonneg (hg0 x) q)]
    simp only [HasFiniteIntegral, this]
    exact hM.trans_lt ENNReal.ofReal_lt_top
  have hig : Integrable g ν := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hiq) hgm.aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg (hg0 x)]
    simp only [Pi.add_apply]
    by_cases h1 : g x ≤ 1
    · have := Real.rpow_nonneg (hg0 x) q
      linarith
    · push Not at h1
      have : g x ^ (1 : ℝ) ≤ g x ^ q := Real.rpow_le_rpow_of_exponent_le h1.le hq.le
      rw [Real.rpow_one] at this
      linarith
  refine ⟨hig, ?_⟩
  have hmin : Integrable (fun x => min (g x) K) ν :=
    hig.mono' (hgm.min measurable_const).aestronglyMeasurable (ae_of_all _ fun x => by
      rw [Real.norm_of_nonneg (le_min (hg0 x) hK.le)]; exact min_le_left _ _)
  have hI : ∫ x, g x ^ q ∂ν ≤ M := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => Real.rpow_nonneg (hg0 x) q)
      hgq.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hM0 hM
  rw [← integral_sub hig hmin]
  calc ∫ x, (g x - min (g x) K) ∂ν ≤ ∫ x, K ^ (1 - q) * g x ^ q ∂ν := by
        refine integral_mono (hig.sub hmin) (hiq.const_mul _) fun x => ?_
        simp only
        by_cases h1 : g x ≤ K
        · rw [min_eq_left h1, sub_self]
          exact mul_nonneg (Real.rpow_nonneg hK.le _) (Real.rpow_nonneg (hg0 x) q)
        · push Not at h1
          rw [min_eq_right h1.le]
          have hgp : 0 < g x := hK.trans h1
          have e : g x = g x ^ q * g x ^ (1 - q) := by
            rw [← Real.rpow_add hgp]; simp
          have h2 : g x ^ (1 - q) ≤ K ^ (1 - q) :=
            Real.rpow_le_rpow_of_nonpos hK h1.le (by linarith)
          have h3 : 0 ≤ g x ^ q := Real.rpow_nonneg (hg0 x) q
          nlinarith
    _ = K ^ (1 - q) * ∫ x, g x ^ q ∂ν := integral_const_mul _ _
    _ ≤ K ^ (1 - q) * M := by gcongr

theorem s94_integral_min_le {ν : Measure E} [IsProbabilityMeasure ν] {G : E → ℝ} (hG : Continuous G)
    (hG0 : ∀ x, 0 ≤ G x) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∫⁻ x, ENNReal.ofReal (G x) ∂ν ≤ ENNReal.ofReal M)
    {k : ℝ} (hk : 0 ≤ k) : ∫ x, min (G x) k ∂ν ≤ M := by
  have hmeas : Measurable fun x => min (G x) k := (hG.measurable.min measurable_const)
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => le_min (hG0 x) hk)
    hmeas.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal hM0 ((lintegral_mono fun x => ?_).trans hM)
  exact ENNReal.ofReal_le_ofReal (min_le_left _ _)

theorem s94_lintegral_le_of_weak {μs : ℕ → ProbabilityMeasure E} {μ : ProbabilityMeasure E}
    (h : Tendsto μs atTop (𝓝 μ)) {G : E → ℝ} (hG : Continuous G) (hG0 : ∀ x, 0 ≤ G x) {M : ℝ}
    (hM0 : 0 ≤ M)
    (hM : ∀ᶠ n in atTop, ∫⁻ x, ENNReal.ofReal (G x) ∂(μs n : Measure E) ≤ ENNReal.ofReal M) :
    ∫⁻ x, ENNReal.ofReal (G x) ∂(μ : Measure E) ≤ ENNReal.ofReal M := by
  have hk : ∀ k : ℕ, ∫ x, min (G x) (k : ℝ) ∂(μ : Measure E) ≤ M := by
    intro k
    refine le_of_tendsto (s94_trunc_tendsto h hG hG0 (k : ℝ) (Nat.cast_nonneg k)) ?_
    filter_upwards [hM] with n hn
    exact s94_integral_min_le hG hG0 hM0 hn (Nat.cast_nonneg k)
  have hmeas : ∀ k : ℕ, Measurable fun x => ENNReal.ofReal (min (G x) (k : ℝ)) := fun k =>
    ENNReal.measurable_ofReal.comp (hG.measurable.min measurable_const)
  have hsup : (fun x => ENNReal.ofReal (G x)) = fun x => ⨆ k : ℕ, ENNReal.ofReal (min (G x) (k : ℝ)) := by
    funext x
    apply le_antisymm
    · obtain ⟨k, hk'⟩ := exists_nat_ge (G x)
      refine le_iSup_of_le k ?_
      rw [min_eq_left hk']
    · exact iSup_le fun k => ENNReal.ofReal_le_ofReal (min_le_left _ _)
  have hmono : Monotone fun k : ℕ => fun x => ENNReal.ofReal (min (G x) (k : ℝ)) := by
    intro a b hab x
    exact ENNReal.ofReal_le_ofReal (min_le_min le_rfl (Nat.cast_le.2 hab))
  rw [hsup, lintegral_iSup hmeas hmono]
  refine iSup_le fun k => ?_
  have hint : Integrable (fun x => min (G x) (k : ℝ)) (μ : Measure E) := by
    refine Integrable.of_bound (hG.measurable.min measurable_const).aestronglyMeasurable (k : ℝ)
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg (le_min (hG0 x) (Nat.cast_nonneg k))]
    exact min_le_right _ _
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x => le_min (hG0 x) (Nat.cast_nonneg k))]
  exact ENNReal.ofReal_le_ofReal (hk k)

theorem s94_weak_integral_tendsto {μs : ℕ → ProbabilityMeasure E} {μ : ProbabilityMeasure E}
    (h : Tendsto μs atTop (𝓝 μ)) {g : E → ℝ} (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x) {q : ℝ}
    (hq : 1 < q) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ᶠ n in atTop, ∫⁻ x, ENNReal.ofReal (g x ^ q) ∂(μs n : Measure E) ≤ ENNReal.ofReal M) :
    Integrable g (μ : Measure E) ∧
      Tendsto (fun n => ∫ x, g x ∂(μs n : Measure E)) atTop (𝓝 (∫ x, g x ∂(μ : Measure E))) ∧
      ∫⁻ x, ENNReal.ofReal (g x ^ q) ∂(μ : Measure E) ≤ ENNReal.ofReal M := by
  have hGc : Continuous fun x => g x ^ q := hg.rpow_const fun _ => Or.inr (by linarith)
  have hlsc := s94_lintegral_le_of_weak h hGc (fun x => Real.rpow_nonneg (hg0 x) q) hM0 hM
  have hmu := fun {K : ℝ} (hK : 0 < K) => s94_integral_sub_trunc_le (ν := (μ : Measure E)) hg hg0 hq hM0 hlsc hK
  refine ⟨(hmu one_pos).1, ?_, hlsc⟩
  rw [Metric.tendsto_nhds]
  intro η0 hη0
  have hKt : Tendsto (fun K : ℝ => K ^ (1 - q) * M) atTop (𝓝 (0 * M)) :=
    (tendsto_rpow_neg_atTop (by linarith : 0 < q - 1)).congr' (by
      filter_upwards with K using by rw [neg_sub]) |>.mul_const M
  rw [zero_mul] at hKt
  obtain ⟨K, hK1, hKsmall⟩ := ((eventually_ge_atTop (1 : ℝ)).and
    (hKt.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < η0 / 3)))).exists
  have hKpos : 0 < K := lt_of_lt_of_le one_pos hK1
  have hlim := s94_trunc_tendsto h hg hg0 K hKpos.le
  filter_upwards [hM, (Metric.tendsto_nhds.1 hlim) (η0 / 3) (by positivity)] with n hn hn2
  obtain ⟨hint_n, hbn⟩ := s94_integral_sub_trunc_le (ν := (μs n : Measure E)) hg hg0 hq hM0 hn hKpos
  obtain ⟨hint, hb⟩ := hmu hKpos
  have hminn : Integrable (fun x => min (g x) K) (μs n : Measure E) :=
    hint_n.mono' (hg.measurable.min measurable_const).aestronglyMeasurable (ae_of_all _ fun x => by
      rw [Real.norm_of_nonneg (le_min (hg0 x) hKpos.le)]; exact min_le_left _ _)
  have hmin : Integrable (fun x => min (g x) K) (μ : Measure E) :=
    hint.mono' (hg.measurable.min measurable_const).aestronglyMeasurable (ae_of_all _ fun x => by
      rw [Real.norm_of_nonneg (le_min (hg0 x) hKpos.le)]; exact min_le_left _ _)
  have h0n : ∫ x, min (g x) K ∂(μs n : Measure E) ≤ ∫ x, g x ∂(μs n : Measure E) :=
    integral_mono hminn hint_n fun x => min_le_left _ _
  have h0 : ∫ x, min (g x) K ∂(μ : Measure E) ≤ ∫ x, g x ∂(μ : Measure E) :=
    integral_mono hmin hint fun x => min_le_left _ _
  rw [Real.dist_eq] at hn2 ⊢
  rw [abs_lt] at hn2 ⊢
  constructor <;> linarith [hn2.1, hn2.2]

theorem s94_integral_map_F' {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {F : E → ℝ} (hF : Measurable F)
    (A : Ω → E) (hA : AEMeasurable A P) : ∫ x, F x ∂(P.map A) = ∫ ζ, F (A ζ) ∂P :=
  integral_map hA hF.aestronglyMeasurable

/-- Uniform higher moments upgrade convergence in law to convergence of the expectations of `g`. -/
theorem s94_tid_integral_tendsto {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)] {P : ∀ N, Measure (Ω N)}
    [∀ N, IsProbabilityMeasure (P N)] {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {Y : ∀ N, Ω N → E} {Z : Ω' → E}
    (h : TendstoInDistribution Y atTop Z P P') {g : E → ℝ} (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x)
    {q : ℝ} (hq : 1 < q) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ᶠ N in atTop, ∫⁻ ζ, ENNReal.ofReal (g (Y N ζ) ^ q) ∂(P N) ≤ ENNReal.ofReal M) :
    Integrable (fun ζ => g (Z ζ)) P' ∧
      Tendsto (fun N => ∫ ζ, g (Y N ζ) ∂(P N)) atTop (𝓝 (∫ ζ, g (Z ζ) ∂P')) ∧
      ∫⁻ ζ, ENNReal.ofReal (g (Z ζ) ^ q) ∂P' ≤ ENNReal.ofReal M := by
  have hGc : Continuous fun x => g x ^ q := hg.rpow_const fun _ => Or.inr (by linarith)
  have hGm : Measurable fun x => ENNReal.ofReal (g x ^ q) := ENNReal.measurable_ofReal.comp hGc.measurable
  have e1 : ∀ N, ∫⁻ x, ENNReal.ofReal (g x ^ q)
      ∂((⟨(P N).map (Y N), inferInstance⟩ : ProbabilityMeasure E) : Measure E) =
      ∫⁻ ζ, ENNReal.ofReal (g (Y N ζ) ^ q) ∂(P N) := fun N =>
    lintegral_map' hGm.aemeasurable (h.forall_aemeasurable N)
  have := s94_weak_integral_tendsto h.tendsto hg hg0 hq hM0 (by
    filter_upwards [hM] with N hN
    exact (e1 N).symm ▸ hN)
  refine ⟨?_, ?_, ?_⟩
  · have hi := this.1
    exact (integrable_map_measure hg.aestronglyMeasurable h.aemeasurable_limit).1 hi
  · have e2 : ∀ N, ∫ x, g x ∂(((⟨(P N).map (Y N), inferInstance⟩ : ProbabilityMeasure E)) : Measure E) =
        ∫ ζ, g (Y N ζ) ∂(P N) := fun N => s94_integral_map_F' hg.measurable _ (h.forall_aemeasurable N)
    have e3 : ∫ x, g x ∂(((⟨P'.map Z, inferInstance⟩ : ProbabilityMeasure E)) : Measure E) =
        ∫ ζ, g (Z ζ) ∂P' := s94_integral_map_F' hg.measurable _ h.aemeasurable_limit
    exact e3 ▸ (tendsto_congr e2).1 this.2.1
  · have e4 : ∫⁻ x, ENNReal.ofReal (g x ^ q) ∂(((⟨P'.map Z, inferInstance⟩ : ProbabilityMeasure E)) : Measure E) =
        ∫⁻ ζ, ENNReal.ofReal (g (Z ζ) ^ q) ∂P' := lintegral_map' hGm.aemeasurable h.aemeasurable_limit
    exact e4 ▸ this.2.2

end UI

end HRS.MS.R2Chaos
