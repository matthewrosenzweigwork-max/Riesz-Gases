import HRS.MS.PoisResAux1

/-!
# POIS-RESOLVENT, part 2: the resolvent integral and the master theorem `pois_resolvent`

`χ(x) = ∫_0^∞ P_t r(x) dt` for `r ∈ C^m` with bounded derivatives of orders `1..m` (no bound on `r`).
* `rf_commute`: `P_t L r = L P_t r` for such `r` (truncation limit of `ld_L_commute`);
* `rf_chi_smooth`: `χ ∈ C^m`, `D^jχ = ∫_0^∞ D^j P_t r dt`, bounds (differentiation under `∫ dt`);
* `rf_chi_eq`: `L χ = -r` (integrated Kolmogorov identity and decay of `P_T r`);
* `rf_chi_mean`: `χ` is `μ`-integrable with `μ(χ) = 0` (Fubini and `pois_inv`);
* `rf_log_real`: `|∫_0^∞ u| ≤ ...(1 + log(2 + |x|))` from `pois_logbound`;
* `pois_resolvent`: the master theorem (statement and adjustments in its docstring).  Adjustments
  relative to the sketch: `Mb < 0` is vacuous (handled by cases); the constants for the order-`≤ 2`
  bounds (`C2`, `Cl2`) are produced for the same `χ`, because S4.2/S4.3 measure the low-order and the
  logarithmic bounds by `cbNorm 2 r` while the higher bounds use `cbNorm m r`.
Helper lemmas carry the prefix `rf_`.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal ContDiff
open HRS HRS.Whole

noncomputable section

namespace HRS.MS.PoisRes

variable {d : ℕ}

section Sg

open HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm
  HRS.MS.PoisHigh HRS.MS.PoisLip HRS.MS.PoisMax

universe u

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → Fin d → ℝ}

theorem rf_kolmL_iter (q : ℝ) (B : Euc d → Euc d) (h : Euc d → ℝ) (y : Euc d) :
    kolmL q B h y = (∑ i : Fin d, iteratedFDeriv ℝ 2 h y ![EuclideanSpace.single i 1,
      EuclideanSpace.single i 1]) + iteratedFDeriv ℝ 1 h y ![-q • y + B y] := by
  rw [kl_L_eq, iteratedFDeriv_one_apply]
  simp [iteratedFDeriv_two_apply]

theorem rf_kolmL_tendsto {q : ℝ} {B : Euc d → Euc d} {ι : Type*} {l : Filter ι} {h : ι → Euc d → ℝ}
    {h0 : Euc d → ℝ} {y : Euc d}
    (h1 : Tendsto (fun n => iteratedFDeriv ℝ 1 (h n) y) l (𝓝 (iteratedFDeriv ℝ 1 h0 y)))
    (h2 : Tendsto (fun n => iteratedFDeriv ℝ 2 (h n) y) l (𝓝 (iteratedFDeriv ℝ 2 h0 y))) :
    Tendsto (fun n => kolmL q B (h n) y) l (𝓝 (kolmL q B h0 y)) := by
  simp_rw [rf_kolmL_iter]
  refine Tendsto.add (tendsto_finsetSum _ fun i _ => ?_) ?_
  · exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Euc d) ℝ
      ![EuclideanSpace.single i 1, EuclideanSpace.single i 1]).continuous.tendsto _).comp h2
  · exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => Euc d) ℝ
      ![-q • y + B y]).continuous.tendsto _).comp h1

/-- `P_t L r = L P_t r` for a Lipschitz `r` (no bound on `r`), by truncation. -/
theorem rf_commute [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) {q Mb : ℝ} (hq : 0 < q)
    {m : ℕ} (hm : 2 ≤ m) {B : Euc d → Euc d} (hB : HasCbBound m Mb B) {r : Euc d → ℝ}
    (hr : ContDiff ℝ (m : WithTop ℕ∞) r) {D : ℝ}
    (hD : ∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ x, ‖iteratedFDeriv ℝ j r x‖ ≤ D) {t : ℝ} (ht : 0 ≤ t)
    (x : Euc d) :
    sg P W q B t (kolmL q B r) x = kolmL q B (sg P W q B t r) x := by
  have hn := sgNoise_of_brownian hW
  have hD0 := rf_D_nonneg (by omega : 1 ≤ m) hD
  obtain ⟨K, hK0, hK⟩ := rf_tr_bounds (d := d) m (by omega)
  obtain ⟨Df, hDf1, hfl⟩ := rf_comp_bound (d := d) q Mb hq hm ht
  obtain ⟨Cs, hCs0, hCs⟩ := sg_second_moment.{u} (d := d) q Mb hq t ht
  have hmeasF := sg_measurable_flowMap hn hq.le (by omega : 1 ≤ m) hB ht
  have hBb : ∀ y, ‖B y‖ ≤ Mb := fun y => by simpa using hB.2 0 (Nat.zero_le _) y
  have hev : ∀ᶠ N : ℕ in atTop, (D ≤ (N : ℝ) ∧ 1 ≤ (N : ℝ)) :=
    (tendsto_natCast_atTop_atTop.eventually_ge_atTop D).and
      (tendsto_natCast_atTop_atTop.eventually_ge_atTop 1)
  have hX := hmeasF.comp (measurable_id.prodMk (measurable_const (a := x)))
  have hX2 := (hCs P ℱ W hW m (by omega) B hB t ⟨ht, le_rfl⟩ x).1
  have hXn : Integrable (fun o => ‖flowMap q B (fun s => W s o) t x‖) P :=
    kl_integrable_lin P (continuous_norm.measurable) (a := 0) (a' := 1) zero_le_one
      (fun y => by simp) (X := fun o => flowMap q B (fun s => W s o) t x) hX hX2
  -- the two limits
  have hL : Tendsto (fun N : ℕ => sg P W q B t (kolmL q B (rfTr (N : ℝ) r)) x) atTop
      (𝓝 (sg P W q B t (kolmL q B r) x)) := by
    unfold sg
    set a0 : ℝ := (d : ℝ) * (K * D) + (K * D) * Mb with ha0
    set a1 : ℝ := (K * D) * |q| with ha1
    refine tendsto_integral_filter_of_dominated_convergence (fun o => a0 + a1 *
      ‖flowMap q B (fun s => W s o) t x‖) (hev.mono fun N hN => ?_)
      (hev.mono fun N hN => Eventually.of_forall fun o => ?_)
      ((integrable_const _).add (hXn.const_mul a1)) (Eventually.of_forall fun o => ?_)
    · have hc := kl_L_continuous q hB.1.continuous
        ((rf_tr_contDiff (N := (N : ℝ)) hr).of_le (by exact_mod_cast hm) : ContDiff ℝ 2 (rfTr (N : ℝ) r))
      exact (hc.measurable.comp hX).aestronglyMeasurable
    · have hrN := rf_tr_contDiff (N := (N : ℝ)) hr
      have hDN : ∀ i : ℕ, 1 ≤ i → i ≤ m → ∀ y, ‖iteratedFDeriv ℝ i (rfTr (N : ℝ) r) y‖ ≤ K * D :=
        fun i h1 h2 y => hK hr hD0 hN.2 hN.1 hD i h1 h2 y
      have := kl_L_growth q hBb (h := rfTr (N : ℝ) r) (M1 := K * D) (M2 := K * D)
        (fun y => by have := hDN 1 le_rfl (by omega) y; rwa [norm_iteratedFDeriv_one] at this)
        (fun y => by rw [kl_norm_fderiv_fderiv']; exact hDN 2 (by norm_num) hm y)
        (flowMap q B (fun s => W s o) t x)
      rw [Real.norm_eq_abs]
      refine this.trans (le_of_eq ?_)
      simp only [ha0, ha1] <;> ring
    · have hlim : ∀ᶠ N : ℕ in atTop, kolmL q B (rfTr (N : ℝ) r) (flowMap q B (fun s => W s o) t x) =
          kolmL q B r (flowMap q B (fun s => W s o) t x) := by
        filter_upwards [tendsto_natCast_atTop_atTop.eventually_gt_atTop
          (|r (flowMap q B (fun s => W s o) t x)|)] with N h1
        have h2 := rf_tr_eventuallyEq (d := d) (N := (N : ℝ)) (lt_of_le_of_lt (abs_nonneg _) h1)
          hr.continuous h1
        rw [kl_L_eq, kl_L_eq, h2.fderiv_eq, (h2.fderiv (𝕜 := ℝ)).fderiv_eq]
      exact tendsto_const_nhds.congr' (hlim.mono fun N hN => hN.symm)
  have hR : Tendsto (fun N : ℕ => kolmL q B (sg P W q B t (rfTr (N : ℝ) r)) x) atTop
      (𝓝 (kolmL q B (sg P W q B t r) x)) :=
    rf_kolmL_tendsto (rf_tr_tendsto hW hq hm hB hr hD ht (by omega) x)
      (rf_tr_tendsto hW hq hm hB hr hD ht hm x)
  refine tendsto_nhds_unique hL (hR.congr' (hev.mono fun N hN => ?_))
  have hrN := rf_tr_contDiff (N := (N : ℝ)) hr
  have hN0 : 0 < (N : ℝ) := by linarith [hN.2]
  have hDN : ∀ i : ℕ, 1 ≤ i → i ≤ m → ∀ y, ‖iteratedFDeriv ℝ i (rfTr (N : ℝ) r) y‖ ≤ K * D :=
    fun i h1 h2 y => hK hr hD0 hN.2 hN.1 hD i h1 h2 y
  have := ld_L_commute hq hm hB hW ((hrN.of_le (by exact_mod_cast hm) : ContDiff ℝ 2 (rfTr (N : ℝ) r)))
    (M := max (2 * (N : ℝ)) (K * D)) (fun i hi y => by
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · subst h0
        rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
        exact (rf_tr_abs_le_two hN0 r y).trans (le_max_left _ _)
      · exact (hDN i h0 (by omega) y).trans (le_max_right _ _)) ht x
  exact this.symm

/-- joint continuity of `(t, x) ↦ P_{max t 0} r (x)` -/
theorem rf_joint_cont [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) {q Mb : ℝ}
    (hq : 0 < q) {m : ℕ} (hm : 2 ≤ m) {B : Euc d → Euc d} (hB : HasCbBound m Mb B) {r : Euc d → ℝ}
    (hr : ContDiff ℝ (m : WithTop ℕ∞) r) {D : ℝ}
    (hD : ∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ x, ‖iteratedFDeriv ℝ j r x‖ ≤ D) :
    Continuous (fun p : ℝ × Euc d => sg P W q B (max p.1 0) r p.2) := by
  have hr2 : ContDiff ℝ 2 r := hr.of_le (by exact_mod_cast hm)
  have hC := fun T (hT : 0 < T) => (pois_kolmogorov hq hm hB hW hr2 (rf_fderiv_bound (by omega) hD)
    (fun y => by have := hD 2 (by norm_num) hm y; exact this)).2.2.2 T hT
  refine continuous_iff_continuousAt.2 fun p => ?_
  set T : ℝ := |p.1| + 1 with hT
  have hT0 : 0 < T := by positivity
  have hcont := (hC T hT0).cont
  have hU : IsOpen {p' : ℝ × Euc d | p'.1 < T} := isOpen_lt continuous_fst continuous_const
  have hmem : p ∈ {p' : ℝ × Euc d | p'.1 < T} := by
    show p.1 < T
    have := le_abs_self p.1
    linarith
  have hmaps : MapsTo (fun p' : ℝ × Euc d => (max p'.1 0, p'.2)) {p' : ℝ × Euc d | p'.1 < T}
      (Icc 0 T ×ˢ univ) := fun p' hp' => ⟨⟨le_max_right _ _, max_le hp'.le hT0.le⟩, mem_univ _⟩
  have hc2 : ContinuousOn (fun p' : ℝ × Euc d => sg P W q B (max p'.1 0) r p'.2)
      {p' : ℝ × Euc d | p'.1 < T} :=
    hcont.comp ((continuous_fst.max continuous_const).prodMk continuous_snd).continuousOn hmaps
  exact hc2.continuousAt (hU.mem_nhds hmem)

/-- The resolvent integral `χ = ∫_0^∞ P_t r dt`: smoothness, derivative formula and bounds. -/
theorem rf_chi_smooth [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) {q Mb : ℝ}
    (hq : 0 < q) {m : ℕ} (hm : 2 ≤ m) {B : Euc d → Euc d} (hB : HasCbBound m Mb B)
    {r : Euc d → ℝ} (hr : ContDiff ℝ (m : WithTop ℕ∞) r) {D : ℝ}
    (hD : ∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ x, ‖iteratedFDeriv ℝ j r x‖ ≤ D) {Kd Ad s0 : ℝ}
    (hKd : ∀ t : ℝ, 0 ≤ t → ∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ x,
      ‖iteratedFDeriv ℝ j (sg P W q B t r) x‖ ≤ Kd * D * Real.exp (-(pm_c0 q Mb) * (t - 1)))
    (hdec : ∀ t : ℝ, 0 ≤ t → ∀ x, |sg P W q B t r x| ≤ Ad * Real.exp (-(pm_c0 q Mb) * t) *
      (‖x‖ + s0)) :
    ContDiff ℝ (m : WithTop ℕ∞) (fun x => ∫ t in Ioi (0 : ℝ), sg P W q B t r x) ∧
      (∀ j ≤ m, ∀ x, iteratedFDeriv ℝ j (fun x => ∫ t in Ioi (0 : ℝ), sg P W q B t r x) x =
        ∫ t in Ioi (0 : ℝ), iteratedFDeriv ℝ j (sg P W q B t r) x) ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ x, ‖iteratedFDeriv ℝ j
        (fun x => ∫ t in Ioi (0 : ℝ), sg P W q B t r x) x‖ ≤
          Kd * D * (Real.exp (pm_c0 q Mb) / pm_c0 q Mb)) ∧
      (∀ x, |∫ t in Ioi (0 : ℝ), sg P W q B t r x| ≤ Ad * (‖x‖ + s0) / pm_c0 q Mb) ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ x,
        Integrable (fun t => iteratedFDeriv ℝ j (sg P W q B t r) x) (volume.restrict (Ioi (0 : ℝ)))) := by
  have hc0 := rf_c0_pos q Mb hq
  set c0 := pm_c0 q Mb with hc0def
  have hD0 := rf_D_nonneg (by omega : 1 ≤ m) hD
  set G : ℝ → Euc d → ℝ := fun t x => sg P W q B (max t 0) r x with hG
  have hGcont : Continuous (fun p : ℝ × Euc d => G p.1 p.2) := rf_joint_cont hW hq hm hB hr hD
  have hGc : ∀ t, ContDiff ℝ (m : WithTop ℕ∞) (G t) := fun t =>
    (rf_sg_contDiff hW hq hm hB hr hD (le_max_right t 0)).1
  have hGeq : ∀ t, 0 < t → G t = sg P W q B t r := fun t ht => by
    simp only [hG, max_eq_left ht.le]
  set μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hμ
  have hexpi : Integrable (fun t : ℝ => Real.exp (-c0 * t)) μ :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hexpint : ∫ t in Ioi (0 : ℝ), Real.exp (-c0 * t) = 1 / c0 := by
    rw [integral_exp_mul_Ioi (by linarith) 0]
    simp
  have hbd : ∀ i, 1 ≤ i → i ≤ m → ∀ᵐ t ∂μ, ∀ x, ‖iteratedFDeriv ℝ i (G t) x‖ ≤
      Kd * D * Real.exp c0 * Real.exp (-c0 * t) := by
    intro i h1 h2
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht x
    rw [hGeq t ht]
    refine (hKd t (le_of_lt ht) i h1 h2 x).trans (le_of_eq ?_)
    rw [mul_assoc (Kd * D) (Real.exp c0), ← Real.exp_add]
    congr 2; ring
  have hmeas : ∀ i ≤ m, ∀ x, AEStronglyMeasurable (fun t => iteratedFDeriv ℝ i (G t) x) μ := by
    intro i hi x
    have := sg_stronglyMeasurable_iteratedFDeriv (Ω := ℝ) G hGcont.stronglyMeasurable i
      (fun t => (hGc t).of_le (by exact_mod_cast hi))
    exact (this.comp_measurable (measurable_id.prodMk (measurable_const (a := x)))).aestronglyMeasurable
  have hint0 : ∀ x, Integrable (fun t => G t x) μ := by
    intro x
    have hmeas0 : AEStronglyMeasurable (fun t => G t x) μ :=
      ((hGcont.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
    refine ((hexpi.const_mul (Ad * (‖x‖ + s0)))).mono' hmeas0 ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [hGeq t ht, Real.norm_eq_abs]
    refine (hdec t ht.le x).trans (le_of_eq ?_)
    ring
  obtain ⟨h1, h2⟩ := rf_iterated_integral (μ := μ) G m (by omega) hGc
    (fun i => fun t => Kd * D * Real.exp c0 * Real.exp (-c0 * t))
    (fun i _ _ => hexpi.const_mul _) hbd hint0 hmeas
  have hχ : (fun x => ∫ t in Ioi (0 : ℝ), sg P W q B t r x) = fun x => ∫ t, G t x ∂μ := by
    funext x
    exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => (congrFun (hGeq t ht) x).symm)
  have hder : ∀ j ≤ m, ∀ x, iteratedFDeriv ℝ j (fun x => ∫ t, G t x ∂μ) x =
      ∫ t in Ioi (0 : ℝ), iteratedFDeriv ℝ j (sg P W q B t r) x := by
    intro j hj x
    rw [h2 j hj x]
    exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => by rw [hGeq t ht])
  rw [hχ]
  refine ⟨h1, hder, fun j hj1 hjm x => ?_, fun x => ?_, fun j hj1 hjm x => ?_⟩
  · rw [h2 j hjm x]
    have := norm_integral_le_of_norm_le (μ := μ)
      (f := fun t => iteratedFDeriv ℝ j (G t) x)
      (g := fun t => Kd * D * Real.exp c0 * Real.exp (-c0 * t)) (hexpi.const_mul _)
      ((hbd j hj1 hjm).mono fun t ht => ht x)
    refine this.trans (le_of_eq ?_)
    rw [integral_const_mul]
    show Kd * D * Real.exp c0 * ∫ t in Ioi (0 : ℝ), Real.exp (-c0 * t) = _
    rw [hexpint]; field_simp
  · rw [congrFun hχ x]
    have hle := norm_integral_le_of_norm_le (μ := μ) (f := fun t => G t x)
      (g := fun t => Ad * (‖x‖ + s0) * Real.exp (-c0 * t)) (hexpi.const_mul _) (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [hGeq t ht, Real.norm_eq_abs]
        refine (hdec t ht.le x).trans (le_of_eq ?_)
        ring)
    rw [← Real.norm_eq_abs]
    refine hle.trans (le_of_eq ?_)
    rw [integral_const_mul]
    show Ad * (‖x‖ + s0) * ∫ t in Ioi (0 : ℝ), Real.exp (-c0 * t) = _
    rw [hexpint]; field_simp
  · have hi := (hexpi.const_mul (Kd * D * Real.exp c0)).mono' (hmeas j hjm x)
      ((hbd j hj1 hjm).mono fun t ht => ht x)
    refine hi.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [hGeq t ht]

/-- `L χ = - r` for the resolvent integral. -/
theorem rf_chi_eq [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) {q Mb : ℝ}
    (hq : 0 < q) {m : ℕ} (hm : 2 ≤ m) {B : Euc d → Euc d} (hB : HasCbBound m Mb B)
    {r : Euc d → ℝ} (hr : ContDiff ℝ (m : WithTop ℕ∞) r) {D : ℝ}
    (hD : ∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ x, ‖iteratedFDeriv ℝ j r x‖ ≤ D) {Kd Ad s0 : ℝ}
    (hKd : ∀ t : ℝ, 0 ≤ t → ∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ x,
      ‖iteratedFDeriv ℝ j (sg P W q B t r) x‖ ≤ Kd * D * Real.exp (-(pm_c0 q Mb) * (t - 1)))
    (hdec : ∀ t : ℝ, 0 ≤ t → ∀ x, |sg P W q B t r x| ≤ Ad * Real.exp (-(pm_c0 q Mb) * t) *
      (‖x‖ + s0)) (x : Euc d) :
    kolmL q B (fun x => ∫ t in Ioi (0 : ℝ), sg P W q B t r x) x = - r x := by
  have hc0 := rf_c0_pos q Mb hq
  obtain ⟨-, hder, -, -, hint⟩ := rf_chi_smooth hW hq hm hB hr hD hKd hdec
  have hr2 : ContDiff ℝ 2 r := hr.of_le (by exact_mod_cast hm)
  set μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hμ
  set v : Euc d := -q • x + B x with hv
  set L1 : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => Euc d) ℝ →L[ℝ] ℝ :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => Euc d) ℝ ![v] with hL1
  set L2 : Fin d → ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Euc d) ℝ →L[ℝ] ℝ := fun i =>
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Euc d) ℝ
      ![EuclideanSpace.single i 1, EuclideanSpace.single i 1] with hL2
  have hK : ∀ h : Euc d → ℝ, kolmL q B h x =
      (∑ i, L2 i (iteratedFDeriv ℝ 2 h x)) + L1 (iteratedFDeriv ℝ 1 h x) := by
    intro h; rw [rf_kolmL_iter]; rfl
  have hi1 := hint 1 le_rfl (by omega) x
  have hi2 := hint 2 (by norm_num) hm x
  have hfi : Integrable (fun t => kolmL q B (sg P W q B t r) x) μ := by
    simp_rw [hK]
    exact (integrable_finsetSum _ fun i _ => (L2 i).integrable_comp hi2).add (L1.integrable_comp hi1)
  have hchi : kolmL q B (fun x => ∫ t in Ioi (0 : ℝ), sg P W q B t r x) x =
      ∫ t in Ioi (0 : ℝ), kolmL q B (sg P W q B t r) x := by
    rw [hK, hder 1 (by omega) x, hder 2 hm x]
    simp_rw [hK]
    rw [integral_add (integrable_finsetSum _ fun i _ => (L2 i).integrable_comp hi2)
      (L1.integrable_comp hi1), integral_finsetSum _ fun i _ => (L2 i).integrable_comp hi2,
      L1.integral_comp_comm hi1]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (L2 i).integral_comp_comm hi2 |>.symm
  rw [hchi]
  -- the FTC part
  have hftc : ∀ T : ℝ, 0 ≤ T → ∫ s in (0 : ℝ)..T, kolmL q B (sg P W q B s r) x =
      sg P W q B T r x - r x := by
    intro T hT
    have hK1 := (pois_kolmogorov hq hm hB hW hr2 (rf_fderiv_bound (by omega) hD)
      (fun y => hD 2 (by norm_num) hm y)).1 T hT x
    have : ∫ s in (0 : ℝ)..T, kolmL q B (sg P W q B s r) x =
        ∫ s in (0 : ℝ)..T, sg P W q B s (kolmL q B r) x := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le hT] at hs
      exact (rf_commute hW hq hm hB hr hD hs.1 x).symm
    rw [this]; linarith
  have hlim := intervalIntegral_tendsto_integral_Ioi (0 : ℝ) hfi (tendsto_id (x := atTop (α := ℝ)))
  have hlim2 : Tendsto (fun T : ℝ => sg P W q B T r x - r x) atTop (𝓝 (- r x)) := by
    have h0 : Tendsto (fun T : ℝ => sg P W q B T r x) atTop (𝓝 0) := by
      have h1 : Tendsto (fun T : ℝ => Ad * Real.exp (-(pm_c0 q Mb) * T) * (‖x‖ + s0)) atTop (𝓝 0) := by
        have : Tendsto (fun T : ℝ => Real.exp (-(pm_c0 q Mb) * T)) atTop (𝓝 0) :=
          Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
        simpa using (this.const_mul Ad).mul_const (‖x‖ + s0)
      refine squeeze_zero_norm' ?_ h1
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
      rw [Real.norm_eq_abs]; exact hdec T hT x
    simpa using h0.sub_const (r x)
  refine tendsto_nhds_unique hlim ?_
  refine hlim2.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  exact (hftc T hT).symm

/-- `χ` is `μ`-integrable and centered. -/
theorem rf_chi_mean [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) {q Mb : ℝ}
    (hq : 0 < q) {m : ℕ} (hm : 2 ≤ m) {B : Euc d → Euc d} (hB : HasCbBound m Mb B)
    {μ : Measure (Euc d)} (hμ : IsInvariantMeasure (fun x => -q • x + B x) μ)
    (hμ2 : Integrable (fun y : Euc d => ‖y‖ ^ 2) μ) {m2 : ℝ} (hm2 : ∫ y, ‖y‖ ^ 2 ∂μ ≤ m2)
    {r : Euc d → ℝ} (hr : ContDiff ℝ (m : WithTop ℕ∞) r) {D : ℝ}
    (hD : ∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ x, ‖iteratedFDeriv ℝ j r x‖ ≤ D) (hcen : ∫ y, r y ∂μ = 0)
    {Kd Ad : ℝ}
    (hKd : ∀ t : ℝ, 0 ≤ t → ∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ x,
      ‖iteratedFDeriv ℝ j (sg P W q B t r) x‖ ≤ Kd * D * Real.exp (-(pm_c0 q Mb) * (t - 1)))
    (hdec : ∀ t : ℝ, 0 ≤ t → ∀ x, |sg P W q B t r x| ≤ Ad * Real.exp (-(pm_c0 q Mb) * t) *
      (‖x‖ + Real.sqrt m2)) :
    Integrable (fun x => ∫ t in Ioi (0 : ℝ), sg P W q B t r x) μ ∧
      ∫ x, (∫ t in Ioi (0 : ℝ), sg P W q B t r x) ∂μ = 0 := by
  haveI : IsProbabilityMeasure μ := hμ.1
  have hc0 := rf_c0_pos q Mb hq
  set c0 := pm_c0 q Mb with hc0def
  set s0 := Real.sqrt m2 with hs0
  obtain ⟨hsm, -, -, hbd, -⟩ := rf_chi_smooth hW hq hm hB hr hD hKd hdec
  obtain ⟨hi1, -⟩ := ld_first_moment hμ2 hm2
  have hr2 : ContDiff ℝ 2 r := hr.of_le (by exact_mod_cast hm)
  constructor
  · refine ((hi1.add (integrable_const s0)).const_mul (Ad / c0)).mono' hsm.continuous.aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    refine (hbd x).trans (le_of_eq ?_)
    simp only [Pi.add_apply, hc0def]
    ring
  · set G : ℝ → Euc d → ℝ := fun t x => sg P W q B (max t 0) r x with hG
    have hGcont : Continuous (fun p : ℝ × Euc d => G p.1 p.2) := rf_joint_cont hW hq hm hB hr hD
    have hGeq : ∀ t, 0 < t → G t = sg P W q B t r := fun t ht => by
      simp only [hG, max_eq_left ht.le]
    set μt : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hμt
    have hexpi : Integrable (fun t : ℝ => Real.exp (-c0 * t)) μt :=
      integrableOn_exp_mul_Ioi (by linarith) 0
    have hχ : ∀ x, ∫ t, sg P W q B t r x ∂μt = ∫ t, G t x ∂μt := fun x =>
      setIntegral_congr_fun measurableSet_Ioi (fun t ht => (congrFun (hGeq t ht) x).symm)
    simp_rw [hχ]
    have hprod : Integrable (Function.uncurry fun (x : Euc d) (t : ℝ) => G t x) (μ.prod μt) := by
      have hb : Integrable (fun p : Euc d × ℝ => (‖p.1‖ + s0) * (Ad * Real.exp (-c0 * p.2)))
          (μ.prod μt) :=
        Integrable.mul_prod (hi1.add (integrable_const s0)) (hexpi.const_mul Ad)
      refine hb.mono' ?_ ?_
      · exact (hGcont.comp (continuous_snd.prodMk continuous_fst)).aestronglyMeasurable
      · have hae : ∀ᵐ p ∂(μ.prod μt), p.2 ∈ Ioi (0 : ℝ) :=
          (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μt)).ae (ae_restrict_mem measurableSet_Ioi)
        filter_upwards [hae] with p hp
        show ‖G p.2 p.1‖ ≤ _
        rw [hGeq p.2 hp, Real.norm_eq_abs]
        refine (hdec p.2 (le_of_lt hp) p.1).trans (le_of_eq ?_)
        ring
    rw [integral_integral_swap hprod]
    have h0 : ∀ t ∈ Ioi (0 : ℝ), ∫ x, G t x ∂μ = 0 := by
      intro t ht
      rw [hGeq t ht]
      have := (HRS.MS.PoisInv.pois_inv hq hm hB hW hμ hμ2 hr2 (rf_fderiv_bound (by omega) hD)
        (fun y => hD 2 (by norm_num) hm y)).2 t (le_of_lt ht)
      rw [this.2.2, hcen]
    rw [setIntegral_congr_fun measurableSet_Ioi h0]
    simp

end Sg

/-- the logarithmic bound for the resolvent integral of a function with two-sided decay. -/
theorem rf_log_real (u : ℝ → ℝ) {c0 a Λ s0 nx : ℝ} (hc0 : 0 < c0) (ha : 0 < a) (hΛ : 0 ≤ Λ)
    (hs0 : 0 ≤ s0) (hnx : 0 ≤ nx)
    (hu : ∀ t : ℝ, 0 < t → |u t| ≤ a ∧ |u t| ≤ Λ * a * Real.exp (-(c0 * t)) * (nx + s0)) :
    |∫ t in Ioi (0 : ℝ), u t| ≤ a / c0 * (1 + Real.log (max 1 (Λ * max 1 s0))) *
      (1 + Real.log (2 + nx)) := by
  set A : ℝ := Λ * a * (nx + s0) with hA
  have hA0 : 0 ≤ A := by positivity
  obtain ⟨hi, hle⟩ := HRS.MS.PoisLip.pois_logbound ha hA0 hc0
  have h1 : |∫ t in Ioi (0 : ℝ), u t| ≤ ∫ t in Ioi (0 : ℝ), min a (A * Real.exp (-(c0 * t))) := by
    rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (0 : ℝ))) hi ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs]
    refine le_min (hu t ht).1 ?_
    refine (hu t ht).2.trans (le_of_eq ?_)
    simp only [hA]; ring
  refine h1.trans (hle.trans ?_)
  set Cz : ℝ := max 1 (Λ * max 1 s0) with hCz
  have hCz1 : 1 ≤ Cz := le_max_left _ _
  have hl2 : 0 < Real.log (2 + nx) := Real.log_pos (by linarith)
  have hlC : 0 ≤ Real.log Cz := Real.log_nonneg hCz1
  have hpl : Real.posLog (A / a) ≤ Real.log Cz + Real.log (2 + nx) := by
    have hAa : A / a = Λ * (nx + s0) := by simp only [hA]; field_simp
    rw [hAa, Real.posLog_eq_log_max_one (by positivity), ← Real.log_mul (by positivity) (by positivity)]
    refine Real.log_le_log (by positivity) ?_
    refine max_le ?_ ?_
    · nlinarith [mul_le_mul hCz1 (show (1:ℝ) ≤ 2 + nx by linarith) zero_le_one (by linarith)]
    · have h2 : Λ * (nx + s0) ≤ Λ * max 1 s0 * (2 + nx) := by
        have : nx + s0 ≤ max 1 s0 * (2 + nx) := by
          have hm1 : 1 ≤ max 1 s0 := le_max_left _ _
          have hm2 : s0 ≤ max 1 s0 := le_max_right _ _
          nlinarith [mul_nonneg (sub_nonneg.2 hm1) hnx]
        calc Λ * (nx + s0) ≤ Λ * (max 1 s0 * (2 + nx)) := mul_le_mul_of_nonneg_left this hΛ
          _ = _ := by ring
      refine h2.trans ?_
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
  have : a / c0 * (1 + Real.posLog (A / a)) ≤ a / c0 * ((1 + Real.log Cz) * (1 + Real.log (2 + nx))) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    nlinarith [mul_nonneg hlC hl2.le]
  calc _ ≤ _ := this
    _ = _ := by ring


section Master

open HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm
  HRS.MS.PoisHigh HRS.MS.PoisLip HRS.MS.PoisMax

variable {d : ℕ}

universe u

/-- The conclusions for one fixed Brownian filtration, given the derivative bound and the decay
estimate of `P_t r`. -/
theorem rf_core {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
    {W : ℝ≥0 → Ω → Fin d → ℝ} [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) {q Mb : ℝ}
    (hq : 0 < q) {m : ℕ} (hm : 2 ≤ m) {B : Euc d → Euc d} (hB : HasCbBound m Mb B)
    {μ : Measure (Euc d)} (hμ : IsInvariantMeasure (fun x => -q • x + B x) μ)
    (hμ2 : Integrable (fun y : Euc d => ‖y‖ ^ 2) μ) {m₂ : ℝ} (hm2 : ∫ y, ‖y‖ ^ 2 ∂μ ≤ m₂)
    {r : Euc d → ℝ} (hr : ContDiff ℝ (m : WithTop ℕ∞) r) {D : ℝ}
    (hD : ∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ x, ‖iteratedFDeriv ℝ j r x‖ ≤ D) (hcen : ∫ y, r y ∂μ = 0)
    {Kd K : ℝ}
    (hKd : ∀ t : ℝ, 0 ≤ t → ∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ x,
      ‖iteratedFDeriv ℝ j (sg P W q B t r) x‖ ≤ Kd * D * Real.exp (-(pm_c0 q Mb) * (t - 1)))
    (hdec : ∀ t : ℝ, 0 ≤ t → ∀ x, |sg P W q B t r x| ≤ (pm_kappa q Mb)⁻¹ * (K * D) *
      Real.exp (-(pm_c0 q Mb) * t) * (‖x‖ + Real.sqrt m₂)) :
    ContDiff ℝ (m : WithTop ℕ∞) (fun x => ∫ t in Ioi (0 : ℝ), sg P W q B t r x) ∧
      Integrable (fun x => ∫ t in Ioi (0 : ℝ), sg P W q B t r x) μ ∧
      ∫ x, (∫ t in Ioi (0 : ℝ), sg P W q B t r x) ∂μ = 0 ∧
      (∀ x, poissonOp (fun x => -q • x + B x) (fun x => ∫ t in Ioi (0 : ℝ), sg P W q B t r x) x =
        r x) ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ x, ‖iteratedFDeriv ℝ j
        (fun x => ∫ t in Ioi (0 : ℝ), sg P W q B t r x) x‖ ≤
          (Kd * (Real.exp (pm_c0 q Mb) / pm_c0 q Mb)) * D) ∧
      ∀ M0 : ℝ, (∀ x, ‖r x‖ ≤ M0) → ∀ x,
        |∫ t in Ioi (0 : ℝ), sg P W q B t r x| ≤
          (1 / pm_c0 q Mb * (1 + Real.log (max 1 ((pm_kappa q Mb)⁻¹ * max K 1 *
            max 1 (Real.sqrt m₂))))) * (M0 + D) * (1 + Real.log (2 + ‖x‖)) := by
  have hc0 := rf_c0_pos q Mb hq
  have hκ : 0 < pm_kappa q Mb := Real.exp_pos _
  have hD0 := rf_D_nonneg (by omega : 1 ≤ m) hD
  obtain ⟨hsm, hder, hbd, hlin, -⟩ := rf_chi_smooth hW hq hm hB hr hD hKd hdec
  obtain ⟨hint, hmean⟩ := rf_chi_mean hW hq hm hB hμ hμ2 hm2 hr hD hcen hKd hdec
  have heq := rf_chi_eq hW hq hm hB hr hD hKd hdec
  refine ⟨hsm, hint, hmean, fun x => ?_, fun j hj1 hjm x => ?_, fun M0 hM0 x => ?_⟩
  · have := heq x
    unfold poissonOp
    unfold kolmL at this
    linarith
  · refine (hbd j hj1 hjm x).trans (le_of_eq ?_)
    ring
  · have hM0nn : 0 ≤ M0 := (norm_nonneg _).trans (hM0 0)
    have hlog1 : 0 ≤ Real.log (2 + ‖x‖) := Real.log_nonneg (by linarith [norm_nonneg x])
    rcases (add_nonneg hM0nn hD0).eq_or_lt with ha | ha
    · have hM00 : M0 = 0 := by linarith
      have hz : ∀ t ∈ Ioi (0 : ℝ), sg P W q B t r x = 0 := by
        intro t ht
        have := ld_sg_bound (P := P) (W := W) (q := q) (B := B) (h := r) (M0 := M0) hM0 t x
        rw [hM00] at this
        exact norm_le_zero_iff.1 this
      rw [setIntegral_congr_fun measurableSet_Ioi hz]
      simp [← ha]
    · have hmain := rf_log_real (fun t => sg P W q B t r x) hc0 ha
        (Λ := (pm_kappa q Mb)⁻¹ * max K 1) (s0 := Real.sqrt m₂) (nx := ‖x‖)
        (by positivity) (Real.sqrt_nonneg _) (norm_nonneg _) (fun t ht => ⟨?_, ?_⟩)
      · refine hmain.trans (le_of_eq ?_)
        field_simp
      · have := ld_sg_bound (P := P) (W := W) (q := q) (B := B) (h := r) (M0 := M0) hM0 t x
        rw [Real.norm_eq_abs] at this
        linarith
      · refine (hdec t ht.le x).trans ?_
        have e : Real.exp (-(pm_c0 q Mb) * t) = Real.exp (-(pm_c0 q Mb * t)) := by rw [neg_mul]
        rw [e]
        have hK0 : K ≤ max K 1 := le_max_left K 1
        have hKD : K * D ≤ max K 1 * (M0 + D) := by
          have h2 := le_max_right K 1
          nlinarith [mul_nonneg (sub_nonneg.2 hK0) hD0, mul_nonneg (by linarith : (0:ℝ) ≤ max K 1) hM0nn]
        have hE := (Real.exp_pos (-(pm_c0 q Mb * t))).le
        have hw : 0 ≤ ‖x‖ + Real.sqrt m₂ := by positivity
        calc (pm_kappa q Mb)⁻¹ * (K * D) * Real.exp (-(pm_c0 q Mb * t)) * (‖x‖ + Real.sqrt m₂)
            ≤ (pm_kappa q Mb)⁻¹ * (max K 1 * (M0 + D)) * Real.exp (-(pm_c0 q Mb * t)) *
              (‖x‖ + Real.sqrt m₂) := by gcongr
          _ = _ := by ring

/-- **POIS-RESOLVENT (master theorem).**  For `q > 0`, `B ∈ C_b^m` (`m ≥ 2`, all derivatives of order
`≤ m` bounded by `Mb`), an invariant probability measure `μ` of `Δ + b·∇` (`b = -q x + B`) with second
moment `≤ m₂`, and `r ∈ C^m` with `‖D^j r‖_∞ ≤ D` for `1 ≤ j ≤ m` (no bound on `r` itself) and
`∫ r dμ = 0`: the function `χ = ∫_0^∞ P_t r dt` (with `P_t` the semigroup of a Brownian filtration
chosen by `exists_isBrownianFiltration_type`) is `C^m`, `μ`-integrable and centered, solves
`(-Δ - b·∇)χ = r`, has `‖D^jχ‖_∞ ≤ Cm D` for `1 ≤ j ≤ m`, and, if `‖r‖_∞ ≤ M0`,
`|χ x| ≤ Cl (M0 + D)(1 + log(2 + ‖x‖))`.  The same `χ` also satisfies the order-`≤ 2` versions with
any `D'` bounding only `‖D^j r‖` for `j ≤ 2` (constants `C2`, `Cl2`), which is what S4.2 needs.
The constants depend only on `(q, Mb, m₂, m)` (and `d`) and are quantified before `B, μ, r, D, D'`. -/
theorem pois_resolvent (q Mb m₂ : ℝ) (hq : 0 < q) (m : ℕ) (hm : 2 ≤ m) :
    ∃ Cm Cl C2 Cl2 : ℝ, ∀ B : Euc d → Euc d, HasCbBound m Mb B → ∀ μ : Measure (Euc d),
      IsInvariantMeasure (fun x => -q • x + B x) μ → Integrable (fun x => ‖x‖ ^ 2) μ →
      ∫ x, ‖x‖ ^ 2 ∂μ ≤ m₂ → ∀ r : Euc d → ℝ, ContDiff ℝ (m : WithTop ℕ∞) r → ∀ D : ℝ,
      (∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ x, ‖iteratedFDeriv ℝ j r x‖ ≤ D) → ∫ x, r x ∂μ = 0 →
      ∃ χ : Euc d → ℝ, ContDiff ℝ (m : WithTop ℕ∞) χ ∧ Integrable χ μ ∧ ∫ x, χ x ∂μ = 0 ∧
        (∀ x, poissonOp (fun x => -q • x + B x) χ x = r x) ∧
        (∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ x, ‖iteratedFDeriv ℝ j χ x‖ ≤ Cm * D) ∧
        (∀ M0 : ℝ, (∀ x, ‖r x‖ ≤ M0) → ∀ x,
          |χ x| ≤ Cl * (M0 + D) * (1 + Real.log (2 + ‖x‖))) ∧
        ∀ D' : ℝ, (∀ j : ℕ, 1 ≤ j → j ≤ 2 → ∀ x, ‖iteratedFDeriv ℝ j r x‖ ≤ D') →
          (∀ j : ℕ, 1 ≤ j → j ≤ 2 → ∀ x, ‖iteratedFDeriv ℝ j χ x‖ ≤ C2 * D') ∧
          ∀ M0 : ℝ, (∀ x, ‖r x‖ ≤ M0) → ∀ x,
            |χ x| ≤ Cl2 * (M0 + D') * (1 + Real.log (2 + ‖x‖)) := by
  by_cases hMb : 0 ≤ Mb
  swap
  · refine ⟨0, 0, 0, 0, fun B hB => ?_⟩
    exact absurd ((norm_nonneg _).trans (by simpa using hB.2 0 (Nat.zero_le _) 0)) hMb
  obtain ⟨Kd, hKd0, hKd⟩ := rf_deriv_bound.{0} (d := d) q Mb hq hMb m hm
  obtain ⟨K, hK0, hK⟩ := rf_decay.{0} (d := d) q Mb hq m hm
  obtain ⟨Kd2, hKd20, hKd2⟩ := rf_deriv_bound.{0} (d := d) q Mb hq hMb 2 le_rfl
  obtain ⟨K2, hK20, hK2⟩ := rf_decay.{0} (d := d) q Mb hq 2 le_rfl
  have hc0 := rf_c0_pos q Mb hq
  refine ⟨Kd * (Real.exp (pm_c0 q Mb) / pm_c0 q Mb),
    1 / pm_c0 q Mb * (1 + Real.log (max 1 ((pm_kappa q Mb)⁻¹ * max K 1 * max 1 (Real.sqrt m₂)))),
    Kd2 * (Real.exp (pm_c0 q Mb) / pm_c0 q Mb),
    1 / pm_c0 q Mb * (1 + Real.log (max 1 ((pm_kappa q Mb)⁻¹ * max K2 1 * max 1 (Real.sqrt m₂)))),
    fun B hB μ hμ hμ2 hm2 r hr D hD hcen => ?_⟩
  obtain ⟨Ω, mΩ, P, hP, ℱ, W, hW⟩ := exists_isBrownianFiltration_type (Fin d)
  have hKd' := fun t ht j hj1 hjm x => hKd P ℱ W hW B hB r hr D hD t ht j hj1 hjm x
  have hdec := fun t ht x => hK P ℱ W hW B hB μ hμ hμ2 m₂ hm2 r hr D hD hcen t ht x
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := rf_core hW hq hm hB hμ hμ2 hm2 hr hD hcen hKd' hdec
  refine ⟨_, h1, h2, h3, h4, h5, h6, fun D' hD' => ?_⟩
  have hB2 : HasCbBound 2 Mb B := ⟨hB.1.of_le (by exact_mod_cast hm), fun j hj x => hB.2 j (hj.trans hm) x⟩
  have hr2 : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) r := hr.of_le (by exact_mod_cast hm)
  have hKd2' := fun t ht j hj1 hjm x => hKd2 P ℱ W hW B hB2 r hr2 D' hD' t ht j hj1 hjm x
  have hdec2 := fun t ht x => hK2 P ℱ W hW B hB2 μ hμ hμ2 m₂ hm2 r hr2 D' hD' hcen t ht x
  obtain ⟨-, -, -, -, g5, g6⟩ := rf_core hW hq le_rfl hB2 hμ hμ2 hm2 hr2 hD' hcen hKd2' hdec2
  exact ⟨g5, g6⟩

end Master

end HRS.MS.PoisRes
