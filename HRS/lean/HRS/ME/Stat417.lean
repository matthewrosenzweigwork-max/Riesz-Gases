import HRS.Stochastic.LyonsZhengSpec
import HRS.MD.Stat

/-!
# Chunk E, row 4.17, packet M4c: proof of `stationary_weighted_integral`

The statement is copied verbatim from `HRS/ME/Spec417Est.lean`.  Helper lemmas carry the prefix `stat4`.

Route: stationarity of the one-time marginals (`md_stat_gibbs_flow_stationary_proof`), the pointwise bound
`|∫_0^{a+t} c(a+t-r) H(X^r) dr| ≤ Γ ∫_0^{a+T} k(r) |H(X^r)| dr` with the envelope `k(r) = e^{-c₀ (a-r)⁺}`,
Cauchy-Schwarz with the weight `k`, and Tonelli.  All integrals are lintegrals in `ℝ≥0∞`; the joint measurability
of `(r, ω) ↦ X^r(ω)` is obtained by modifying the path on a null set (`Nn`), where it is constant in `r`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.ME

variable {d : ℕ}

open HRS HRS.LZ

/-- The envelope `k(r) = e^{-c₀ (a - r)⁺}` as an `ℝ≥0∞` function. -/
noncomputable def stat4_K (c₀ a r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-c₀ * max (a - r) 0))

theorem stat4_K_meas (c₀ a : ℝ) : Measurable (stat4_K c₀ a) := by
  unfold stat4_K
  have hkc : Continuous fun r : ℝ => Real.exp (-c₀ * max (a - r) 0) := by fun_prop
  exact hkc.measurable.ennreal_ofReal

/-- `∫_0^a e^{-c w} dw ≤ 1/c`. -/
theorem stat4_int_exp (c : ℝ) (hc : 0 < c) (a : ℝ) (ha : 0 ≤ a) :
    ∫ w in (0:ℝ)..a, Real.exp (-c * w) ≤ 1 / c := by
  have hc0 : c ≠ 0 := hc.ne'
  have hd : ∀ w ∈ Set.uIcc (0:ℝ) a,
      HasDerivAt (fun w : ℝ => -Real.exp (-c * w) / c) (Real.exp (-c * w)) w := by
    intro w _
    have h1 : HasDerivAt (fun w : ℝ => -c * w) (-c) w := by
      simpa using (hasDerivAt_id' w).const_mul (-c)
    have h2 := ((h1.exp).neg).div_const c
    convert h2 using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp only [mul_zero, neg_zero, Real.exp_zero]
  have he : 0 ≤ Real.exp (-c * a) / c := div_nonneg (Real.exp_pos _).le hc.le
  have key : -Real.exp (-c * a) / c - -1 / c = -(Real.exp (-c * a) / c) + 1 / c := by ring
  rw [key]
  linarith

/-- `∫_0^a e^{-c(a-r)} dr ≤ 1/c`. -/
theorem stat4_int_g (c : ℝ) (hc : 0 < c) (a : ℝ) (ha : 0 ≤ a) :
    ∫ r in (0:ℝ)..a, Real.exp (-c * (a - r)) ≤ 1 / c := by
  have h := intervalIntegral.integral_comp_sub_left (fun w : ℝ => Real.exp (-c * w)) a
    (a := 0) (b := a)
  simp only [sub_self, sub_zero] at h
  rw [h]
  exact stat4_int_exp c hc a ha

/-- The total envelope mass: `∫_0^{a+T} k ≤ 1/c₀ + T`. -/
theorem stat4_k_int (c₀ a T : ℝ) (hc₀ : 0 < c₀) (ha : 0 ≤ a) (hT : 0 ≤ T) :
    ∫⁻ r in Set.Ioc (0:ℝ) (a + T), stat4_K c₀ a r ≤ ENNReal.ofReal (1 / c₀ + T) := by
  have hkc : Continuous fun r : ℝ => Real.exp (-c₀ * max (a - r) 0) := by fun_prop
  have hIoc : MeasureTheory.IntegrableOn (fun r : ℝ => Real.exp (-c₀ * max (a - r) 0))
      (Set.Ioc (0:ℝ) (a + T)) :=
    (hkc.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hnn : (0 : ℝ → ℝ) ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) (a + T))]
      fun r : ℝ => Real.exp (-c₀ * max (a - r) 0) :=
    MeasureTheory.ae_of_all _ (fun r => (Real.exp_pos _).le)
  have hlin : ∫⁻ r in Set.Ioc (0:ℝ) (a + T), stat4_K c₀ a r =
      ENNReal.ofReal (∫ r in Set.Ioc (0:ℝ) (a + T), Real.exp (-c₀ * max (a - r) 0)) := by
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIoc hnn]
    rfl
  rw [hlin, ← intervalIntegral.integral_of_le (by linarith)]
  apply ENNReal.ofReal_le_ofReal
  rw [← intervalIntegral.integral_add_adjacent_intervals (hkc.intervalIntegrable 0 a)
    (hkc.intervalIntegrable a (a + T))]
  have h1 : ∫ r in (0:ℝ)..a, Real.exp (-c₀ * max (a - r) 0) ≤ 1 / c₀ := by
    have e : ∫ r in (0:ℝ)..a, Real.exp (-c₀ * max (a - r) 0) =
        ∫ r in (0:ℝ)..a, Real.exp (-c₀ * (a - r)) := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [Set.uIcc_of_le ha] at hr
      simp only
      rw [max_eq_left (by linarith [hr.2])]
    rw [e]
    exact stat4_int_g c₀ hc₀ a ha
  have h2 : ∫ r in a..(a + T), Real.exp (-c₀ * max (a - r) 0) = T := by
    have e : ∫ r in a..(a + T), Real.exp (-c₀ * max (a - r) 0) = ∫ r in a..(a + T), (1:ℝ) := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [Set.uIcc_of_le (by linarith)] at hr
      simp only
      rw [max_eq_right (by linarith [hr.1])]
      simp
    rw [e]
    simp
  linarith

/-- Pointwise bound on one window: for `0 ≤ t ≤ T`, the modulus of the weighted integral is at most
`Γ ∫_0^{a+T} k(r) |h(r)| dr` (no measurability needed). -/
theorem stat4_pointwise (c : ℝ → ℝ) (c₀ Γ a T t : ℝ) (hc₀ : 0 < c₀) (hΓ : 0 ≤ Γ) (ha : 0 ≤ a)
    (hc : ∀ v, 0 ≤ v → |c v| ≤ Γ * Real.exp (-c₀ * v)) (ht0 : 0 ≤ t) (htT : t ≤ T) (h : ℝ → ℝ) :
    ENNReal.ofReal |∫ r in (0:ℝ)..(a + t), c (a + t - r) * h r| ≤
      ENNReal.ofReal Γ * ∫⁻ r in Set.Ioc (0:ℝ) (a + T), stat4_K c₀ a r * ENNReal.ofReal |h r| := by
  have hle : (0:ℝ) ≤ a + t := by linarith
  rw [intervalIntegral.integral_of_le hle, ← Real.enorm_eq_ofReal_abs]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  calc ∫⁻ r in Set.Ioc (0:ℝ) (a + t), ‖c (a + t - r) * h r‖ₑ
      ≤ ∫⁻ r in Set.Ioc (0:ℝ) (a + t), ENNReal.ofReal Γ * (stat4_K c₀ a r * ENNReal.ofReal |h r|) := by
        refine setLIntegral_mono' measurableSet_Ioc (fun r hr => ?_)
        rw [Real.enorm_eq_ofReal_abs, abs_mul, ENNReal.ofReal_mul (abs_nonneg _), ← mul_assoc]
        refine mul_le_mul' ?_ le_rfl
        have hv : 0 ≤ a + t - r := by linarith [hr.2]
        have hmax : max (a - r) 0 ≤ a + t - r := max_le (by linarith) hv
        have hexp : Real.exp (-c₀ * (a + t - r)) ≤ Real.exp (-c₀ * max (a - r) 0) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hmax (by linarith))
        unfold stat4_K
        rw [← ENNReal.ofReal_mul hΓ]
        apply ENNReal.ofReal_le_ofReal
        exact (hc _ hv).trans (mul_le_mul_of_nonneg_left hexp hΓ)
    _ ≤ ∫⁻ r in Set.Ioc (0:ℝ) (a + T), ENNReal.ofReal Γ * (stat4_K c₀ a r * ENNReal.ofReal |h r|) :=
        lintegral_mono_set (Set.Ioc_subset_Ioc_right (by linarith))
    _ = ENNReal.ofReal Γ * ∫⁻ r in Set.Ioc (0:ℝ) (a + T), stat4_K c₀ a r * ENNReal.ofReal |h r| :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Cauchy-Schwarz with an `ℝ≥0∞` weight: `(∫ K g)² ≤ (∫ K)(∫ K g²)`. -/
theorem stat4_cs {α : Type*} [MeasurableSpace α] (μ : Measure α) (K g : α → ℝ≥0∞)
    (hK : AEMeasurable K μ) (hg : AEMeasurable g μ) :
    (∫⁻ a, K a * g a ∂μ) ^ 2 ≤ (∫⁻ a, K a ∂μ) * ∫⁻ a, K a * g a ^ 2 ∂μ := by
  have hKK : ∀ a, K a ^ (1 / 2 : ℝ) * K a ^ (1 / 2 : ℝ) = K a := by
    intro a
    rw [← ENNReal.rpow_add_of_nonneg (x := K a) (1 / 2) (1 / 2) (by norm_num) (by norm_num)]
    norm_num
  have hsq : ∀ a, (K a ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = K a := by
    intro a
    rw [← ENNReal.rpow_mul]
    norm_num
  have hf : AEMeasurable (fun a => K a ^ (1 / 2 : ℝ)) μ := hK.pow_const _
  have hh : AEMeasurable (fun a => K a ^ (1 / 2 : ℝ) * g a) μ := (hK.pow_const _).mul hg
  have e2 : ∫⁻ a, (K a ^ (1 / 2 : ℝ)) ^ (2 : ℝ) ∂μ = ∫⁻ a, K a ∂μ := lintegral_congr hsq
  have e3 : ∫⁻ a, (K a ^ (1 / 2 : ℝ) * g a) ^ (2 : ℝ) ∂μ = ∫⁻ a, K a * g a ^ 2 ∂μ := by
    refine lintegral_congr (fun a => ?_)
    rw [ENNReal.mul_rpow_of_nonneg (K a ^ (1 / 2 : ℝ)) (g a) (by norm_num : (0:ℝ) ≤ 2), hsq,
      show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]
  have key : ∫⁻ a, K a * g a ∂μ ≤
      (∫⁻ a, K a ∂μ) ^ (1 / (2:ℝ)) * (∫⁻ a, K a * g a ^ 2 ∂μ) ^ (1 / (2:ℝ)) := by
    calc ∫⁻ a, K a * g a ∂μ
        = ∫⁻ a, (K a ^ (1 / 2 : ℝ)) * (K a ^ (1 / 2 : ℝ) * g a) ∂μ :=
          lintegral_congr (fun a => by rw [← mul_assoc, hKK])
      _ ≤ (∫⁻ a, (K a ^ (1 / 2 : ℝ)) ^ (2 : ℝ) ∂μ) ^ (1 / (2:ℝ)) *
            (∫⁻ a, (K a ^ (1 / 2 : ℝ) * g a) ^ (2 : ℝ) ∂μ) ^ (1 / (2:ℝ)) :=
          ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf hh
      _ = (∫⁻ a, K a ∂μ) ^ (1 / (2:ℝ)) * (∫⁻ a, K a * g a ^ 2 ∂μ) ^ (1 / (2:ℝ)) := by
          rw [e2, e3]
  set A := ∫⁻ a, K a ∂μ with hAdef
  set B := ∫⁻ a, K a * g a ^ 2 ∂μ with hBdef
  have hA : (A ^ (1 / (2:ℝ))) ^ 2 = A := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hB : (B ^ (1 / (2:ℝ))) ^ 2 = B := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  calc (∫⁻ a, K a * g a ∂μ) ^ 2 ≤ ((A ^ (1 / (2:ℝ))) * (B ^ (1 / (2:ℝ)))) ^ 2 := by gcongr
    _ = A * B := by rw [mul_pow, hA, hB]

/-- The real-valued form of the weighted Cauchy-Schwarz inequality. -/
theorem stat4_cs_real (μ : Measure ℝ) (K : ℝ → ℝ≥0∞) (h : ℝ → ℝ) (hK : AEMeasurable K μ)
    (hh : AEMeasurable (fun r => ENNReal.ofReal |h r|) μ) :
    (∫⁻ r, K r * ENNReal.ofReal |h r| ∂μ) ^ 2 ≤
      (∫⁻ r, K r ∂μ) * ∫⁻ r, K r * ENNReal.ofReal (h r ^ 2) ∂μ := by
  have := stat4_cs μ K (fun r => ENNReal.ofReal |h r|) hK hh
  have e : ∫⁻ r, K r * ENNReal.ofReal (h r ^ 2) ∂μ = ∫⁻ r, K r * (ENNReal.ofReal |h r|) ^ 2 ∂μ := by
    refine lintegral_congr (fun r => ?_)
    rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  rw [e]
  exact this

/-- M4c.  For a stationary Gibbs flow and a square integrable `H` (under `μ = canonicalGibbs`), a weight `c`
with `|c(v)| ≤ Γ e^{-c₀ v}`, and a window `[a, a+T] ⊆ [0,H₀]`:
`E sup_{t ∈ ℚ∩[0,T]} |∫_0^{a+t} c(a+t-r) H(X^r) dr|² ≤ Γ² (1/c₀ + T)² ∫ H² dμ`
(Minkowski with the envelope `e^{-c₀ (a-r)_+}` and stationarity of the one-time marginals). -/
theorem stationary_weighted_integral_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N) (H₀ : ℝ)
    (hflow : IsStationaryGibbsFlow P s hs0 hsd V β hβ H₀ X₀ W X)
    (Hf : Config d N → ℝ) (hHm : Measurable Hf)
    (c : ℝ → ℝ) (hcm : Measurable c) (c₀ Γ : ℝ) (hc₀ : 0 < c₀) (hΓ : 0 ≤ Γ)
    (hc : ∀ v, 0 ≤ v → |c v| ≤ Γ * Real.exp (-c₀ * v))
    (a T : ℝ) (ha : 0 ≤ a) (hT : 0 ≤ T) (haT : a + T ≤ H₀) :
    ∫⁻ ω, ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal
        ((∫ r in (0 : ℝ)..(a + t), c (a + t - r) * Hf (X r.toNNReal ω)) ^ 2) ∂P ≤
      ENNReal.ofReal (Γ ^ 2 * (1 / c₀ + T) ^ 2) *
        ∫⁻ Y, ENNReal.ofReal (Hf Y ^ 2) ∂(canonicalGibbs (periodicRiesz d s) V N β) := by
  classical
  haveI : BorelSpace (Torus d) := Pi.borelSpace
  haveI : BorelSpace (Config d N) := Pi.borelSpace
  -- (1) stationarity of the one-time marginals
  have hstat : ∀ t : ℝ≥0, (t : ℝ) ≤ H₀ → P.map (X t) = canonicalGibbs (periodicRiesz d s) V N β :=
    HRS.MD.Stat.md_stat_gibbs_flow_stationary_proof hd hs0 hsd V hV β hβ H₀ hN P X₀ W X hflow
  -- path regularity and adaptedness from the strong solution
  have hcont : ∀ᵐ ω ∂P, ∀ i, Continuous fun t : ℝ≥0 => X t ω i := by
    rcases hflow.flow.flow with hh | ⟨hd1, -⟩
    · exact hh.1.cont
    · omega
  have hadapt : ∀ t : ℝ≥0, Measurable (X t) := by
    rcases hflow.flow.flow with hh | ⟨hd1, -⟩
    · exact hh.1.adapted
    · omega
  obtain ⟨Nn, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hcont)
  have hcont_bad : ∀ ω, ω ∉ Nn → ∀ i, Continuous fun t : ℝ≥0 => X t ω i := by
    intro ω hω
    by_contra hne
    exact hω (hNsub hne)
  have hNae : ∀ᵐ ω ∂P, ω ∉ Nn := by
    rw [ae_iff]
    exact measure_mono_null (fun ω hω => not_not.mp hω) hN0
  -- a jointly measurable modification of the path, equal to `X` off `Nn`
  obtain ⟨Xs, hXs_good, hXs_meas⟩ : ∃ Xs : ℝ → Ω → Config d N,
      (∀ ω, ω ∉ Nn → ∀ r : ℝ, Xs r ω = X r.toNNReal ω) ∧
        Measurable (fun p : ℝ × Ω => Xs p.1 p.2) := by
    refine ⟨fun r ω => if ω ∈ Nn then X 0 ω else X r.toNNReal ω, fun ω hω r => if_neg hω, ?_⟩
    refine measurable_uncurry_of_continuous_of_measurable (u := fun (r : ℝ) (ω : Ω) =>
      if ω ∈ Nn then X 0 ω else X r.toNNReal ω) (fun ω => ?_) (fun r => ?_)
    · by_cases hω : ω ∈ Nn
      · simp only [if_pos hω]
        exact continuous_const
      · simp only [if_neg hω]
        exact continuous_pi fun i => (hcont_bad ω hω i).comp continuous_real_toNNReal
    · exact Measurable.ite hNm (hadapt 0) (hadapt r.toNNReal)
  have hXs_sec : ∀ ω, Measurable (fun r : ℝ => Xs r ω) := fun ω =>
    hXs_meas.comp (measurable_id.prodMk measurable_const)
  have hHXs : Measurable (fun p : ℝ × Ω => Hf (Xs p.1 p.2)) := hHm.comp hXs_meas
  -- the constants
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ≥0∞, A = ∫⁻ r in Set.Ioc (0:ℝ) (a + T), stat4_K c₀ a r := ⟨_, rfl⟩
  have hA_le : A ≤ ENNReal.ofReal (1 / c₀ + T) := by
    rw [hAdef]
    exact stat4_k_int c₀ a T hc₀ ha hT
  have hA_ne : A ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hA_le
  obtain ⟨B0, hB0⟩ : ∃ B0 : ℝ≥0∞,
      B0 = ∫⁻ Y, ENNReal.ofReal (Hf Y ^ 2) ∂(canonicalGibbs (periodicRiesz d s) V N β) := ⟨_, rfl⟩
  rw [← hB0]
  have hHsq : Measurable (fun Y : Config d N => ENNReal.ofReal (Hf Y ^ 2)) :=
    (hHm.pow_const 2).ennreal_ofReal
  -- one-time identity: `∫ dP ofReal(H(X^r)²) = B0` for `r ∈ (0, a+T]`
  have hBint : ∀ r ∈ Set.Ioc (0:ℝ) (a + T), ∫⁻ ω, ENNReal.ofReal (Hf (Xs r ω) ^ 2) ∂P = B0 := by
    intro r hr
    have hr0 : (0:ℝ) ≤ r := hr.1.le
    have hrH : ((r.toNNReal : ℝ≥0) : ℝ) ≤ H₀ := by
      rw [Real.coe_toNNReal r hr0]
      linarith [hr.2]
    calc ∫⁻ ω, ENNReal.ofReal (Hf (Xs r ω) ^ 2) ∂P
        = ∫⁻ ω, ENNReal.ofReal (Hf (X r.toNNReal ω) ^ 2) ∂P :=
          lintegral_congr_ae (hNae.mono fun ω hω => by simp only [hXs_good ω hω r])
      _ = ∫⁻ Y, ENNReal.ofReal (Hf Y ^ 2) ∂(P.map (X r.toNNReal)) :=
          (lintegral_map hHsq (hadapt _)).symm
      _ = B0 := by rw [hstat r.toNNReal hrH, hB0]
  -- the random variables
  obtain ⟨Zs, hZs⟩ : ∃ Zs : Ω → ℝ≥0∞, ∀ ω, Zs ω =
      ∫⁻ r in Set.Ioc (0:ℝ) (a + T), stat4_K c₀ a r * ENNReal.ofReal |Hf (Xs r ω)| :=
    ⟨_, fun ω => rfl⟩
  obtain ⟨Bs, hBs⟩ : ∃ Bs : Ω → ℝ≥0∞, ∀ ω, Bs ω =
      ∫⁻ r in Set.Ioc (0:ℝ) (a + T), stat4_K c₀ a r * ENNReal.ofReal (Hf (Xs r ω) ^ 2) :=
    ⟨_, fun ω => rfl⟩
  -- (2) pointwise sup bound, off the null set
  have hsup : ∀ ω, ω ∉ Nn →
      (⨆ t ∈ ratTimes 0 T, ENNReal.ofReal
        ((∫ r in (0 : ℝ)..(a + t), c (a + t - r) * Hf (X r.toNNReal ω)) ^ 2)) ≤
        (ENNReal.ofReal Γ * Zs ω) ^ 2 := by
    intro ω hω
    rw [hZs ω]
    simp only [hXs_good ω hω]
    refine iSup₂_le (fun t ht => ?_)
    have ht' : t ∈ Set.Icc (0:ℝ) (0 + T) ∧ ∃ q : ℚ, (q:ℝ) = t := ht
    have h1 := stat4_pointwise c c₀ Γ a T t hc₀ hΓ ha hc (by linarith [ht'.1.1])
      (by linarith [ht'.1.2]) (fun r => Hf (X r.toNNReal ω))
    have h2 : ENNReal.ofReal ((∫ r in (0 : ℝ)..(a + t), c (a + t - r) * Hf (X r.toNNReal ω)) ^ 2) =
        ENNReal.ofReal |∫ r in (0 : ℝ)..(a + t), c (a + t - r) * Hf (X r.toNNReal ω)| ^ 2 := by
      rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    rw [h2]
    exact pow_le_pow_left₀ (by positivity) h1 2
  have hstep1 : ∫⁻ ω, (⨆ t ∈ ratTimes 0 T, ENNReal.ofReal
        ((∫ r in (0 : ℝ)..(a + t), c (a + t - r) * Hf (X r.toNNReal ω)) ^ 2)) ∂P ≤
      ∫⁻ ω, (ENNReal.ofReal Γ * Zs ω) ^ 2 ∂P :=
    lintegral_mono_ae (hNae.mono fun ω hω => hsup ω hω)
  -- (3) Cauchy-Schwarz off the null set
  have hCS : ∀ ω, ω ∉ Nn → Zs ω ^ 2 ≤ A * Bs ω := by
    intro ω _
    rw [hZs ω, hBs ω, hAdef]
    have hK : AEMeasurable (stat4_K c₀ a) (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) (a + T))) :=
      (stat4_K_meas c₀ a).aemeasurable
    have hh : AEMeasurable (fun r => ENNReal.ofReal |Hf (Xs r ω)|)
        (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) (a + T))) :=
      ((hHm.comp (hXs_sec ω)).abs.ennreal_ofReal).aemeasurable
    exact stat4_cs_real _ (stat4_K c₀ a) (fun r => Hf (Xs r ω)) hK hh
  -- (4) Tonelli: `∫ dP Bs = A * B0`
  have hFm : Measurable (fun p : ℝ × Ω => stat4_K c₀ a p.1 * ENNReal.ofReal (Hf (Xs p.1 p.2) ^ 2)) :=
    ((stat4_K_meas c₀ a).comp measurable_fst).mul ((hHXs.pow_const 2).ennreal_ofReal)
  have hTon : ∫⁻ ω, Bs ω ∂P = A * B0 := by
    calc ∫⁻ ω, Bs ω ∂P
        = ∫⁻ ω, (∫⁻ r in Set.Ioc (0:ℝ) (a + T), stat4_K c₀ a r * ENNReal.ofReal (Hf (Xs r ω) ^ 2)) ∂P :=
          lintegral_congr (fun ω => by rw [hBs ω])
      _ = ∫⁻ r in Set.Ioc (0:ℝ) (a + T), (∫⁻ ω, stat4_K c₀ a r * ENNReal.ofReal (Hf (Xs r ω) ^ 2) ∂P) :=
          lintegral_lintegral_swap (f := fun ω r => stat4_K c₀ a r * ENNReal.ofReal (Hf (Xs r ω) ^ 2))
            (μ := P) (ν := MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) (a + T)))
            (hFm.comp measurable_swap).aemeasurable
      _ = ∫⁻ r in Set.Ioc (0:ℝ) (a + T), stat4_K c₀ a r * B0 := by
          refine setLIntegral_congr_fun measurableSet_Ioc (fun r hr => ?_)
          have hKne : stat4_K c₀ a r ≠ ⊤ := by
            unfold stat4_K
            exact ENNReal.ofReal_ne_top
          rw [lintegral_const_mul' _ _ hKne, hBint r hr]
      _ = A * B0 := by
          rw [hAdef]
          exact lintegral_mul_const B0 (stat4_K_meas c₀ a)
  -- (5) assembly
  have hL : 0 ≤ 1 / c₀ + T := add_nonneg (div_nonneg zero_le_one hc₀.le) hT
  calc ∫⁻ ω, ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal
          ((∫ r in (0 : ℝ)..(a + t), c (a + t - r) * Hf (X r.toNNReal ω)) ^ 2) ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal Γ * Zs ω) ^ 2 ∂P := hstep1
    _ = ENNReal.ofReal Γ ^ 2 * ∫⁻ ω, Zs ω ^ 2 ∂P := by
        simp_rw [mul_pow]
        exact lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    _ ≤ ENNReal.ofReal Γ ^ 2 * (A * ∫⁻ ω, Bs ω ∂P) := by
        refine mul_le_mul' le_rfl ?_
        calc ∫⁻ ω, Zs ω ^ 2 ∂P ≤ ∫⁻ ω, A * Bs ω ∂P :=
              lintegral_mono_ae (hNae.mono fun ω hω => hCS ω hω)
          _ = A * ∫⁻ ω, Bs ω ∂P := lintegral_const_mul' _ _ hA_ne
    _ = ENNReal.ofReal Γ ^ 2 * (A * (A * B0)) := by rw [hTon]
    _ ≤ ENNReal.ofReal Γ ^ 2 * (ENNReal.ofReal (1 / c₀ + T) * (ENNReal.ofReal (1 / c₀ + T) * B0)) :=
        mul_le_mul' le_rfl (mul_le_mul' hA_le (mul_le_mul' hA_le le_rfl))
    _ = ENNReal.ofReal (Γ ^ 2 * (1 / c₀ + T) ^ 2) * B0 := by
        rw [ENNReal.ofReal_mul (sq_nonneg Γ), ENNReal.ofReal_pow hΓ, ENNReal.ofReal_pow hL]
        ring

end HRS.ME

end
