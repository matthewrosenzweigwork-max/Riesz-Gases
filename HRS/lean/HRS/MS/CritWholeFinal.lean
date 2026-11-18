import HRS.Whole.Critical
import HRS.MS.ShiftFldAux6
import HRS.MS.SharpBias
import HRS.MS.QsfStat1
import HRS.ME.BiasE

/-!
# S8.1 XE (conditional): final metric constants and smooth constant from the static and centered inputs

Worker S81, namespace `HRS.Whole.BreakdownS81`, helper prefix `s81bd_`.

Conditional reductions (the open frozen statements enter as explicit `type_of%` hypotheses):

* `s81bd_constants_of`: `critical_whole_marginal` and `critical_whole_W2` imply `critical_whole_constants`;
* `s81bd_smooth_of`: the same two imply `critical_whole_smooth`.

Route.  For a canonical realization `η_N^{u+·} = ζ_N^{u+·} + c_N` a.s. with the deterministic constant path
`c_N = √N (m_N - μ)` (`s81bd_decomp`); `‖c_N - r_N b‖_{B_m} ≤ K √(log N)/√N` from the static marginal expansion
and `s79_bias_vec_bound` (`s81bd_shift`); `‖ζ‖_𝒳` is bounded (`s81bd_zeta_bound`); then the abstract cores
`HRS.ME.Bias.core_wasserstein`, `core_smooth` (translation of a random path by a deterministic one) and the
scalar `div_bound` give the two statements.
-/

set_option autoImplicit false

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole

namespace HRS.Whole.BreakdownS81

/-- `‖μ - ν‖_{B_m}` is bounded for probability measures. -/
theorem s81bd_norm_ofMeasureDiff_le {d : ℕ} {m : ℝ} (hm : (d : ℝ) < m) :
    ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ (μ ν : Measure (Euc d)), IsProbabilityMeasure μ →
      IsProbabilityMeasure ν → ‖OscDual.ofMeasureDiff m μ ν‖ ≤ Kb := by
  obtain ⟨C0, hC0⟩ := hermiteFunD_uniform_bound (d := d)
  have hC0nn : 0 ≤ C0 := (abs_nonneg _).trans (hC0 0 0)
  refine ⟨2 * C0 * Real.sqrt (∑' α : MultiIndex d, oscEigenvalue d α ^ (-m)),
    by positivity, fun μ ν hμ hν => ?_⟩
  have hb : ∀ (ν0 : Measure (Euc d)), IsProbabilityMeasure ν0 → ∀ α : MultiIndex d,
      |measureHermiteCoeff ν0 α| ≤ C0 := by
    intro ν0 hν0 α
    unfold measureHermiteCoeff
    have := norm_integral_le_of_norm_le_const (μ := ν0) (f := hermiteFunD α) (C := C0)
      (Filter.Eventually.of_forall fun x => by simpa using hC0 α x)
    simpa using this
  have := S79.s79_norm_le_of_coeff hm (OscDual.ofMeasureDiff m μ ν) (2 * C0) (by positivity)
    (fun α => by
      rw [OscDual.hermiteCoeff_ofMeasureDiff hm]
      have h1 := hb μ hμ α
      have h2 := hb ν hν α
      calc |measureHermiteCoeff μ α - measureHermiteCoeff ν α|
          ≤ |measureHermiteCoeff μ α| + |measureHermiteCoeff ν α| := abs_sub _ _
        _ ≤ 2 * C0 := by linarith)
  exact this

/-- The constant shift `√N (m_N - μ_β)` is `r_N b_{β,μ}` up to `K √(log N)/√N` in `B_m`. -/
theorem s81bd_shift (hmarg : type_of% @HRS.Whole.critical_whole_marginal) {d : ℕ} (hd : 2 ≤ d)
    {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {m : ℝ} (hm : (d : ℝ) < m)
    (ρβ : Euc d → ℝ) (hρβ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) :
    ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ N : ℕ, 2 ≤ N →
      IsProbabilityMeasure (canonicalGibbs (rieszKernel d ((d : ℝ) / 2)) (confinement a) N β) ∧
      ‖Real.sqrt N • OscDual.ofMeasureDiff m
          (meanEmpirical (canonicalGibbs (rieszKernel d ((d : ℝ) / 2)) (confinement a) N β))
          (withDensityReal ρβ) -
        (Real.log N / Real.sqrt N) • critBiasField m d β ρβ‖ ≤
        Kc * (Real.sqrt (Real.log N) / Real.sqrt N) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : (0 : ℝ) < (d : ℝ) / 2 := by linarith
  have hsd : (d : ℝ) / 2 < d := by linarith
  have hρeq : ρβ = thermalDensity d ((d : ℝ) / 2) a β :=
    S78.s78_eq_thermalDensity hd hs0 hsd ha hβ hρβ
  subst hρeq
  have hth := S71.s71_thermal_equilibrium hd hs0 hsd a β ha hβ
  have hprob : IsProbDensity (thermalDensity d ((d : ℝ) / 2) a β) := hth.2.1
  obtain ⟨M, hM⟩ := S71.s71_thermal_bounded hd hs0 hsd a β ha hβ
  obtain ⟨Λ, hΛ⟩ := S71.s71_thermal_lipschitz hd hs0 hsd a β ha hβ
  obtain ⟨-, C, hC⟩ := hmarg hd _ hprob ⟨M, hM⟩ ⟨Λ, hΛ⟩ β β hβ le_rfl
  obtain ⟨Kv, hKv0, hKv⟩ := S79.s79_bias_vec_bound (d := d) hm
  obtain ⟨Cs, -, hS⟩ := S45.s45_static_all hd hs0.le hsd ha hβ
  have hint : ∀ x, Integrable (fun y => rieszKernel d ((d : ℝ) / 2) (x - y))
      (withDensityReal (thermalDensity d ((d : ℝ) / 2) a β)) :=
    fun x => (HRS.MS.Wr.wr13a_potential_bound (by omega) hs0 hsd hprob hM x).1
  have hcan : ∀ N, canonicalGibbs (rieszKernel d ((d : ℝ) / 2)) (confinement a) N β =
      modulatedGibbs (rieszKernel d ((d : ℝ) / 2)) N β
        (withDensityReal (thermalDensity d ((d : ℝ) / 2) a β)) := fun N =>
    HRS.MS.Canon.canonicalGibbs_eq_modulatedGibbs_proof (N := N) (rieszKernel d ((d : ℝ) / 2))
      (confinement a) β (thermalDensity d ((d : ℝ) / 2) a β) hth.2
      (fun x => rieszKernel_neg x) hint
  refine ⟨Kv * |C|, mul_nonneg hKv0 (abs_nonneg _), fun N hN => ?_⟩
  have hSN := hS N hN
  refine ⟨hSN.prob, ?_⟩
  haveI := hSN.prob
  have hN1 : 1 ≤ N := by omega
  haveI hμ : IsProbabilityMeasure (withDensityReal (thermalDensity d ((d : ℝ) / 2) a β)) :=
    Q34.isProbabilityMeasure_nu hprob
  obtain ⟨-, hMem, φ, hφm, hφ0, hφeq, hφL, hφn⟩ := hC β ⟨le_rfl, le_rfl⟩ N hN
  have hmean : meanEmpirical (canonicalGibbs (rieszKernel d ((d : ℝ) / 2)) (confinement a) N β) =
      (withDensityReal (thermalDensity d ((d : ℝ) / 2) a β)).withDensity
        (fun x => ENNReal.ofReal (φ x)) := by
    rw [meanEmpirical_eq_firstMarginal _ hSN.exch hN1, hcan N, hφeq]
  rw [hmean]
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by linarith
  have hsq0 : 0 < Real.sqrt N := Real.sqrt_pos.2 hn0
  have hbd := hKv (thermalDensity d ((d : ℝ) / 2) a β)
    (critBiasDensity d β (thermalDensity d ((d : ℝ) / 2) a β)) φ (Real.log N / N) hprob hφm hφ0
    hMem hφL
  have hfield : critBiasField m d β (thermalDensity d ((d : ℝ) / 2) a β) =
      OscDual.ofFun m (fun x => critBiasDensity d β (thermalDensity d ((d : ℝ) / 2) a β) x *
        thermalDensity d ((d : ℝ) / 2) a β x) := rfl
  have hrr : Real.log N / Real.sqrt N = Real.sqrt N * (Real.log N / N) := by
    have hsq : Real.sqrt N ^ 2 = N := Real.sq_sqrt hn0.le
    field_simp
    rw [hsq]
  have hcomb : Real.sqrt N • OscDual.ofMeasureDiff m
        ((withDensityReal (thermalDensity d ((d : ℝ) / 2) a β)).withDensity
          (fun x => ENNReal.ofReal (φ x))) (withDensityReal (thermalDensity d ((d : ℝ) / 2) a β)) -
      (Real.log N / Real.sqrt N) • critBiasField m d β (thermalDensity d ((d : ℝ) / 2) a β) =
      Real.sqrt N • (OscDual.ofMeasureDiff m
        ((withDensityReal (thermalDensity d ((d : ℝ) / 2) a β)).withDensity
          (fun x => ENNReal.ofReal (φ x))) (withDensityReal (thermalDensity d ((d : ℝ) / 2) a β)) -
      (Real.log N / N) • OscDual.ofFun m (fun x =>
        critBiasDensity d β (thermalDensity d ((d : ℝ) / 2) a β) x *
          thermalDensity d ((d : ℝ) / 2) a β x)) := by
    rw [hfield, hrr, smul_sub, smul_smul]
  rw [hcomb, norm_smul, Real.norm_eq_abs, abs_of_pos hsq0]
  calc Real.sqrt N * ‖OscDual.ofMeasureDiff m
        ((withDensityReal (thermalDensity d ((d : ℝ) / 2) a β)).withDensity
          (fun x => ENNReal.ofReal (φ x))) (withDensityReal (thermalDensity d ((d : ℝ) / 2) a β)) -
      (Real.log N / N) • OscDual.ofFun m (fun x =>
        critBiasDensity d β (thermalDensity d ((d : ℝ) / 2) a β) x *
          thermalDensity d ((d : ℝ) / 2) a β x)‖
      ≤ Real.sqrt N * (Kv * (C * Real.sqrt (Real.log N) / N)) := by
        refine mul_le_mul_of_nonneg_left (hbd.trans (mul_le_mul_of_nonneg_left hφn hKv0)) hsq0.le
    _ ≤ Real.sqrt N * (Kv * (|C| * Real.sqrt (Real.log N) / N)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hKv0) hsq0.le
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _)) hn0.le
    _ = Kv * |C| * Real.sqrt (Real.log N) * (Real.sqrt N / N) := by ring
    _ = Kv * |C| * Real.sqrt (Real.log N) * (1 / Real.sqrt N) := by
        have hq : Real.sqrt N / N = 1 / Real.sqrt N := by
          rw [div_eq_div_iff hn0.ne' hsq0.ne', one_mul]
          exact Real.mul_self_sqrt hn0.le
        rw [hq]
    _ = Kv * |C| * (Real.sqrt (Real.log N) / Real.sqrt N) := by ring

theorem s81bd_norm_windowPathOf_le {d : ℕ} (m T a : ℝ) (f : ℝ → OscDual d m) {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ t, ‖f t‖ ≤ B) : ‖windowPathOf m T a f‖ ≤ B := by
  by_cases h : Continuous fun t : Set.Icc (0 : ℝ) T => f (a + t)
  · have e : windowPathOf m T a f =
        (⟨fun t => f (a + t), h⟩ : C(Set.Icc (0 : ℝ) T, OscDual d m)) := by
      unfold windowPathOf; exact dif_pos h
    rw [e]
    exact (ContinuousMap.norm_le _ hB).2 fun t => hf _
  · have e : windowPathOf m T a f = 0 := by
      unfold windowPathOf; exact dif_neg h
    rw [e, norm_zero]
    exact hB

/-- The exactly centered window is bounded in `𝒳_T`. -/
theorem s81bd_zeta_bound {d : ℕ} {s a β : ℝ} {m : ℝ} (hmd : (d : ℝ) < m) (T u : ℝ) {N : ℕ}
    (hN : 1 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hR : IsCanonicalRealization d s a β N P X₀ W X)
    [hG : IsProbabilityMeasure (canonicalGibbs (rieszKernel d s) (confinement a) N β)] :
    ∃ Kz : ℝ, 0 ≤ Kz ∧ ∀ ω, ‖zetaPathW m T u P X ω‖ ≤ Kz := by
  obtain ⟨Kb, hKb0, hKb⟩ := s81bd_norm_ofMeasureDiff_le (d := d) hmd
  refine ⟨Real.sqrt N * Kb, by positivity, fun ω => ?_⟩
  unfold zetaPathW
  simp only [S79.s79_law_X_eq hR]
  refine s81bd_norm_windowPathOf_le _ _ _ _ (by positivity) fun t => ?_
  unfold zetaB
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  haveI : IsProbabilityMeasure (empirical (X (Real.toNNReal t) ω)) :=
    empirical_isProbabilityMeasure (by omega) _
  haveI : IsProbabilityMeasure (meanEmpirical (canonicalGibbs (rieszKernel d s) (confinement a) N β)) :=
    meanEmpirical_isProbabilityMeasure _ hN
  exact mul_le_mul_of_nonneg_left (hKb _ _ inferInstance inferInstance) (Real.sqrt_nonneg _)

/-- `η_N^{u+·} = ζ_N^{u+·} + (constant path)` almost surely. -/
theorem s81bd_decomp {d : ℕ} {s a β : ℝ} {m : ℝ} (hmd : (d : ℝ) < m) (T u : ℝ)
    (ρβ : Euc d → ℝ) [IsProbabilityMeasure (withDensityReal ρβ)] {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hR : IsCanonicalRealization d s a β N P X₀ W X)
    [hG : IsProbabilityMeasure (canonicalGibbs (rieszKernel d s) (confinement a) N β)] :
    flucPathW m T u (Real.sqrt N) X (fun _ => ρβ) =ᵐ[P] fun ω =>
      zetaPathW m T u P X ω + constPath m T (Real.sqrt N • OscDual.ofMeasureDiff m
        (meanEmpirical (canonicalGibbs (rieszKernel d s) (confinement a) N β)) (withDensityReal ρβ)) := by
  have hN1 : 1 ≤ N := by omega
  set G := canonicalGibbs (rieszKernel d s) (confinement a) N β with hGdef
  haveI : IsProbabilityMeasure (meanEmpirical G) := meanEmpirical_isProbabilityMeasure G hN1
  set μ := withDensityReal ρβ with hμdef
  set cc : OscDual d m := Real.sqrt N • OscDual.ofMeasureDiff m (meanEmpirical G) μ with hcc
  have hzeta_eq : ∀ ζ, zetaPathW m T u P X ζ =
      windowPathOf m T u (fun t => zetaB m G (X (Real.toNNReal t) ζ)) := by
    intro ζ
    unfold zetaPathW
    simp only [S79.s79_law_X_eq hR]
    rfl
  have hfl_eq : ∀ ζ, flucPathW m T u (Real.sqrt N) X (fun _ => ρβ) ζ =
      windowPathOf m T u (fun t => zetaB m G (X (Real.toNNReal t) ζ) + cc) := by
    intro ζ
    unfold flucPathW
    congr 1
    funext t
    exact eta_eq_zeta_add m hmd G μ (X (Real.toNNReal t) ζ) hN1
  filter_upwards [(hR.solution 0).cont] with ζ hζ
  rw [hfl_eq, hzeta_eq]
  apply S79.s79_windowPathOf_add_const
  exact (S79.s79_continuous_window (by omega) hmd (meanEmpirical G) u T (fun t => X t ζ)
    (continuous_pi hζ)).const_smul (Real.sqrt N)

theorem s81bd_smoothDist_le_one {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [MeasurableSpace B] [BorelSpace B] (P Q : Measure B) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {k : ℕ} (hk : 1 ≤ k) : smoothDist k P Q ≤ smoothDist 1 P Q := by
  induction k, hk using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact (smoothDist_succ_le n P Q).trans ih

/-- For `N ≥ N₀`, `C'/√(log N) ≤ ε`. -/
theorem s81bd_N0 (C' ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → 2 ≤ N → C' / Real.sqrt (Real.log N) ≤ ε := by
  refine ⟨⌈Real.exp ((C' / ε) ^ 2)⌉₊, fun N hN hN2 => ?_⟩
  have h2 : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hl : 0 < Real.log N := Real.log_pos (by linarith)
  have hsl : 0 < Real.sqrt (Real.log N) := Real.sqrt_pos.2 hl
  have hexp : Real.exp ((C' / ε) ^ 2) ≤ N :=
    (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hlog : (C' / ε) ^ 2 ≤ Real.log N := by
    rw [← Real.log_exp ((C' / ε) ^ 2)]
    exact Real.log_le_log (Real.exp_pos _) hexp
  have hsq : C' / ε ≤ Real.sqrt (Real.log N) := by
    calc C' / ε ≤ |C' / ε| := le_abs_self _
      _ = Real.sqrt ((C' / ε) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (Real.log N) := Real.sqrt_le_sqrt hlog
  rw [div_le_iff₀ hsl]
  rw [div_le_iff₀ hε] at hsq
  linarith

/-- The data feeding the abstract cores. -/
theorem s81bd_core_data (hmarg : type_of% @HRS.Whole.critical_whole_marginal)
    (hW2 : type_of% @HRS.Whole.critical_whole_W2) {d : ℕ} (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) {m : ℝ} (hm : (wholeSpaceIndex d : ℝ) ≤ m) {T : ℝ} (hT : 0 < T)
    (ρβ : Euc d → ℝ) (hρβ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) :
    ∃ A Bc : ℝ, 0 ≤ A ∧ 0 ≤ Bc ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
        IsCanonicalRealization d ((d : ℝ) / 2) a β N P X₀ W X →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z : ℝ → Ω' → OscDual d m),
        IsStationaryGaussianField d ((d : ℝ) / 2) a β m ρβ P' Z →
        AEMeasurable (processWindow m T 0 Z) P' ∧
        ∀ u : ℝ, 0 ≤ u →
          AEMeasurable (flucPathW m T u (Real.sqrt N) X (fun _ => ρβ)) P ∧
          (∀ p : ℝ, 1 ≤ p → p ≤ 2 →
            wassersteinE p (law P (flucPathW m T u (Real.sqrt N) X (fun _ => ρβ)))
                (law P' (processWindow m T 0 Z)) ≠ ⊤ ∧
            |(wassersteinE p (law P (flucPathW m T u (Real.sqrt N) X (fun _ => ρβ)))
                (law P' (processWindow m T 0 Z))).toReal / (Real.log N / Real.sqrt N) -
                ‖constPath m T (critBiasField m d β ρβ)‖| ≤
              (A * (N : ℝ) ^ (-(1 : ℝ) / 2) + Bc * (Real.sqrt (Real.log N) / Real.sqrt N)) /
                (Real.log N / Real.sqrt N)) ∧
          (∀ k : ℕ, 2 ≤ k →
            |smoothDist k (law P (flucPathW m T u (Real.sqrt N) X (fun _ => ρβ)))
                (law P' (processWindow m T 0 Z)) / (Real.log N / Real.sqrt N) -
                smoothConstant P' k (processWindow m T 0 Z)
                  (constPath m T (critBiasField m d β ρβ))| ≤
              (A * (N : ℝ) ^ (-(1 : ℝ) / 2) + Bc * (Real.sqrt (Real.log N) / Real.sqrt N) +
                (1 / 2) * (Real.log N / Real.sqrt N) ^ 2 *
                  ‖constPath m T (critBiasField m d β ρβ)‖ ^ 2) / (Real.log N / Real.sqrt N)) := by
  have hmd : (d : ℝ) < m := by
    refine lt_of_lt_of_le ?_ hm
    unfold wholeSpaceIndex
    push_cast
    linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  obtain ⟨CW, hCW⟩ := hW2 hd a β ha hβ m hm T hT
  obtain ⟨Kc, hKc0, hKc⟩ := s81bd_shift hmarg hd ha hβ hmd ρβ hρβ
  refine ⟨|CW|, Kc, abs_nonneg _, hKc0, ?_⟩
  intro N hN Ω _ P _ X₀ W X hR Ω' _ P' _ Z hZ
  have hN1 : 1 ≤ N := by omega
  obtain ⟨hGprob, hshift⟩ := hKc N hN
  haveI := hGprob
  haveI hμ : IsProbabilityMeasure (withDensityReal ρβ) := Q34.isProbabilityMeasure_nu hρβ.2.1
  obtain ⟨hZm, hu⟩ := hCW ρβ hρβ N hN P X₀ W X hR P' Z hZ
  refine ⟨hZm, fun u hu0 => ?_⟩
  obtain ⟨hζm, hW⟩ := hu u hu0
  obtain ⟨Kz, hKz0, hKz⟩ := s81bd_zeta_bound hmd T u hN1 P X₀ W X hR
  have hexp : (N : ℝ) ^ (-(1 : ℝ) / 2) = (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    congr 1; ring
  have hint : Integrable (fun w => ‖zetaPathW m T u P X w‖) P :=
    Integrable.of_bound hζm.norm.aestronglyMeasurable Kz
      (Filter.Eventually.of_forall fun w => by rw [norm_norm]; exact hKz w)
  have hdec := s81bd_decomp hmd T u ρβ hN P X₀ W X hR
  set cc : OscDual d m := Real.sqrt N • OscDual.ofMeasureDiff m
    (meanEmpirical (canonicalGibbs (rieszKernel d ((d : ℝ) / 2)) (confinement a) N β))
    (withDensityReal ρβ) with hcc
  have hflm : AEMeasurable (flucPathW m T u (Real.sqrt N) X (fun _ => ρβ)) P :=
    (hζm.add_const (constPath m T cc)).congr (hdec.mono fun w h => h.symm)
  refine ⟨hflm, ?_, ?_⟩
  all_goals
    have hshift' : ‖constPath m T cc -
        (Real.log N / Real.sqrt N) • constPath m T (critBiasField m d β ρβ)‖ ≤
        Kc * (Real.sqrt (Real.log N) / Real.sqrt N) := by
      refine le_trans ?_ hshift
      exact (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun t => le_rfl
    haveI : IsProbabilityMeasure (law P (zetaPathW m T u P X)) :=
      (Measure.isProbabilityMeasure_map_iff hζm).2 inferInstance
    haveI : IsProbabilityMeasure (law P' (processWindow m T 0 Z)) :=
      (Measure.isProbabilityMeasure_map_iff hZm).2 inferInstance
  · intro p hp1 hp2
    have hWp : wassersteinE p (law P (zetaPathW m T u P X)) (law P' (processWindow m T 0 Z)) ≤
        ENNReal.ofReal (|CW| * (N : ℝ) ^ (-(1 : ℝ) / 2)) := by
      refine (wassersteinE_mono p 2 hp1 hp2 _ _).trans (hW.trans ?_)
      rw [hexp]
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self _) ?_)
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    exact HRS.ME.Bias.core_wasserstein P P' (zetaPathW m T u P X)
      (flucPathW m T u (Real.sqrt N) X (fun _ => ρβ)) (processWindow m T 0 Z) hζm hZm hint
      (constPath m T cc) (constPath m T (critBiasField m d β ρβ)) hdec hN (abs_nonneg _) hshift'
      p hp1 hWp
  · intro k hk
    have hdist : smoothDist k (law P (zetaPathW m T u P X)) (law P' (processWindow m T 0 Z)) ≤
        |CW| * (N : ℝ) ^ (-(1 : ℝ) / 2) := by
      have h1 := s81bd_smoothDist_le_one (law P (zetaPathW m T u P X))
        (law P' (processWindow m T 0 Z)) (by omega : 1 ≤ k)
      have h2 := smoothDist_one_le_wasserstein (law P (zetaPathW m T u P X))
        (law P' (processWindow m T 0 Z))
      have h3 := wassersteinE_one_le_two (law P (zetaPathW m T u P X))
        (law P' (processWindow m T 0 Z))
      have h4 : ENNReal.ofReal (smoothDist 1 (law P (zetaPathW m T u P X))
          (law P' (processWindow m T 0 Z))) ≤ ENNReal.ofReal (|CW| * (N : ℝ) ^ (-(1 : ℝ) / 2)) := by
        refine h2.trans (h3.trans (hW.trans ?_))
        rw [hexp]
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self _) ?_)
        exact Real.rpow_nonneg (Nat.cast_nonneg _) _
      have h5 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h4
      exact h1.trans h5
    exact (HRS.ME.Bias.core_smooth P P' (zetaPathW m T u P X)
      (flucPathW m T u (Real.sqrt N) X (fun _ => ρβ)) (processWindow m T 0 Z) hζm hZm
      (constPath m T cc) (constPath m T (critBiasField m d β ρβ)) hdec hN k hk hshift' hdist).2

/-- Conditional reduction: `critical_whole_marginal` and `critical_whole_W2` give
`critical_whole_constants`. -/
theorem s81bd_constants_of (hmarg : type_of% @HRS.Whole.critical_whole_marginal)
    (hW2 : type_of% @HRS.Whole.critical_whole_W2) :
    type_of% @HRS.Whole.critical_whole_constants := by
  intro d hd a β ha hβ m hm T hT p hp1 hp2 ρβ hρβ ε hε
  obtain ⟨A, Bc, hA0, hBc0, hdata⟩ := s81bd_core_data hmarg hW2 hd ha hβ hm hT ρβ hρβ
  obtain ⟨C', -, hdiv⟩ := HRS.ME.Bias.div_bound A Bc 0 hA0 hBc0 le_rfl
  obtain ⟨N0, hN0⟩ := s81bd_N0 C' ε hε
  refine ⟨N0, fun N hN0' hN2 Ω _ P _ X₀ W X hR Ω' _ P' _ Z hZ => ?_⟩
  obtain ⟨hZm, hu⟩ := hdata N hN2 P X₀ W X hR P' Z hZ
  refine ⟨hZm, fun u hu0 => ?_⟩
  obtain ⟨hflm, hWp, -⟩ := hu u hu0
  refine ⟨hflm, ?_⟩
  obtain ⟨hne, hineq⟩ := hWp p hp1 hp2
  have hr : 0 < Real.log N / Real.sqrt N := HRS.ME.Bias.rate_pos hN2
  set r := Real.log N / Real.sqrt N with hrdef
  set b := ‖constPath m T (critBiasField m d β ρβ)‖ with hb
  set W := (wassersteinE p (law P (flucPathW m T u (Real.sqrt N) X (fun _ => ρβ)))
    (law P' (processWindow m T 0 Z))) with hWdef
  have h1 := hdiv N hN2
  have h2 : |W.toReal / r - b| ≤ ε := by
    refine hineq.trans ((le_of_eq ?_).trans (h1.trans (hN0 N hN0' hN2)))
    simp [hrdef]
  have h3 := abs_le.1 h2
  have h4 : r * (b - ε) ≤ W.toReal := by
    have : b - ε ≤ W.toReal / r := by linarith [h3.1]
    rw [le_div_iff₀ hr] at this
    linarith
  have h5 : W.toReal ≤ r * (b + ε) := by
    have : W.toReal / r ≤ b + ε := by linarith [h3.2]
    rw [div_le_iff₀ hr] at this
    linarith
  refine ⟨?_, ?_⟩
  · calc ENNReal.ofReal (r * (b - ε)) ≤ ENNReal.ofReal W.toReal := ENNReal.ofReal_le_ofReal h4
      _ = W := ENNReal.ofReal_toReal hne
  · calc W = ENNReal.ofReal W.toReal := (ENNReal.ofReal_toReal hne).symm
      _ ≤ ENNReal.ofReal (r * (b + ε)) := ENNReal.ofReal_le_ofReal h5

/-- Conditional reduction: `critical_whole_marginal` and `critical_whole_W2` give
`critical_whole_smooth`. -/
theorem s81bd_smooth_of (hmarg : type_of% @HRS.Whole.critical_whole_marginal)
    (hW2 : type_of% @HRS.Whole.critical_whole_W2) :
    type_of% @HRS.Whole.critical_whole_smooth := by
  intro d hd a β ha hβ m hm T hT k hk ρβ hρβ ε hε
  obtain ⟨A, Bc, hA0, hBc0, hdata⟩ := s81bd_core_data hmarg hW2 hd ha hβ hm hT ρβ hρβ
  obtain ⟨C', -, hdiv⟩ := HRS.ME.Bias.div_bound A Bc
    (‖constPath m T (critBiasField m d β ρβ)‖ ^ 2) hA0 hBc0 (sq_nonneg _)
  obtain ⟨N0, hN0⟩ := s81bd_N0 C' ε hε
  refine ⟨N0, fun N hN0' hN2 Ω _ P _ X₀ W X hR Ω' _ P' _ Z hZ => ?_⟩
  obtain ⟨hZm, hu⟩ := hdata N hN2 P X₀ W X hR P' Z hZ
  refine ⟨hZm, fun u hu0 => ?_⟩
  obtain ⟨hflm, -, hsm⟩ := hu u hu0
  refine ⟨hflm, ?_⟩
  have h1 := hdiv N hN2
  have h2 := hsm k hk
  rw [inv_mul_eq_div]
  exact h2.trans (h1.trans (hN0 N hN0' hN2))

end HRS.Whole.BreakdownS81
