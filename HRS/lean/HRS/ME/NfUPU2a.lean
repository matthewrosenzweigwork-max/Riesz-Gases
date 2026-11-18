import HRS.Equilibrium.Q32cAux1

/-!
# Packet PU2 (uniform-in-`β` split parameters, smallness and domination constants)

Each `_unif` lemma copies an original statement (cited in its docstring) and moves its constants
before `∀ β ∈ Icc βm βp` and before `ρ`. Density hypotheses are `IsProbDensity ρ` and `∀ x, ρ x ≤ Λ`
with `Λ` a fixed parameter; the split data `τ, L, Ψ` are fixed.

* `klDiv_R0small_weakSplit_le_unif` (original `RefSmall.klDiv_R0small_weakSplit_le`, ReferenceSmallness:929):
  `C, N₀` are chosen before `β`; `0 ≤ β` stays as a hypothesis of the bound.
* `tv_R0small_unif` (route: `Q32c.q32c_tv_uniform`): `ε₀ N = sqrt(max (βp * (C * aN N)) 0 / 2)`, `N₃ = N₀`;
  `β ≤ βp` enters through `β * (C * aN) ≤ βp * (C * aN)` (`aN ≥ 0` for `N ≥ 1`).
* `sup_calibration_field_unif` (route: `Q32c.q32c_sup_calibration`, `Q32c.q32c_eventually_hsmall`): the
  `hsmall` hypothesis of `core_unif_unif` for every `ε > 0`; `‖t_N‖ ≤ β ‖meanFeature‖ ≤ βp ‖meanFeature‖`
  and the uniform total-variation bound of `tv_R0small_unif`.
* `eventually_hsmall_unif` (original `Glue.eventually_hsmall`, ReferenceGlue:102): the case `ε = 1`.
  `1 ≤ Λ` is a hypothesis (the original derived it from `ρ`).
* `riesz_Q_le_smul_RN_crude_unif` (original `riesz_Q_le_smul_RN_crude`, QuadraticVariance:2006): the
  constant `K N = exp (8 βp N gL(0))` of `Q32c.q32c_Q_le_smul_RN_crude`, with `β ≤ βp`.
* `riesz_Q_le_smul_RN_eventually_unif` (original `Glue.riesz_Q_le_smul_RN_eventually`, ReferenceGlue:141):
  `hκ` becomes `∀ β ∈ Icc βm βp, KappaSmall β (Λ c)`; the conclusion keeps `exp (4 β gL(0))`.
* `exists_split_params_unif` (original `PairMom.exists_split_params'`, PairMomentsSetting:26): the
  smallness is chosen at `β := βp` with `Λ₀' = max Λ₀ 1`; `β ≤ βp` gives `KappaSmall β (Λ₀' c)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.ME.NfU

open HRS HRS.External HRS.External.HeatSplit InformationTheory

variable {d : ℕ}

/-- Uniform version of `RefSmall.klDiv_R0small_weakSplit_le` (`HRS/Equilibrium/ReferenceSmallness.lean:929`).
The constants `C, N₀` are chosen before `β`; the hypothesis `0 ≤ β` stays. -/
theorem klDiv_R0small_weakSplit_le_unif (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ}
    (hτ : 0 < τ) (L : ℕ) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ β : ℝ, 0 ≤ β → ∀ ρ : Torus d → ℝ, IsProbDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ N : ℕ, N₀ ≤ N →
        klDiv (RefSmall.R0small (weakSplit d s τ L).q β (withDensityReal ρ) N)
            (Measure.pi fun _ : Fin N => withDensityReal ρ) ≤
          ENNReal.ofReal (β * N * (C * aN d s N)) := by
  obtain ⟨C, hC, N₀, hN₀, h⟩ := RefSmall.modulatedEnergy_weakSplit_ge hd hs0 hsd hτ L hΛ1
  refine ⟨C, hC, N₀, hN₀, fun β hβ ρ hρ hΛ N hN => ?_⟩
  exact RefSmall.klDiv_R0small_le (by omega) (RefSmall.smallKernel_weakSplit hd hs0 hsd hτ L) hρ hΛ hβ
    (by omega) (A := C * aN d s N) (fun X hX => h ρ hρ hΛ N hN X hX)

/-- `aN d s N ≥ 0` for `N ≥ 1`. -/
theorem aN_nonneg_unif {s : ℝ} {N : ℕ} (hN : 1 ≤ N) : 0 ≤ aN d s N := by
  unfold aN
  have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  refine mul_nonneg ?_ (Real.rpow_nonneg (by linarith) _)
  split_ifs
  · linarith [Real.log_nonneg h1]
  · norm_num

/-- Uniform version of `Q32c.q32c_tv_uniform` (the total-variation bound of the weak reference
marginal): `ε₀` and `N₃` are chosen before `β ∈ [βm, βp]` and before `ρ`. This is the `hTV0`
hypothesis of `core_unif_unif`. -/
theorem tv_R0small_unif (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ)
    (L : ℕ) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) {βm βp : ℝ} (hβm : 0 < βm) (hββ : βm ≤ βp) :
    ∃ ε₀ : ℕ → ℝ, Tendsto ε₀ atTop (𝓝 0) ∧ ∃ N₃ : ℕ, ∀ β ∈ Set.Icc βm βp,
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
        ∀ n : ℕ, N₃ ≤ n + 1 → 1 ≤ n →
          HRS.External.Entropy.tvDist ((Calib.R0 (weakSplit d s τ L).q (withDensityReal ρ) β (n + 1)).map
            (fun X => X ⟨0, Nat.succ_pos n⟩)) (withDensityReal ρ) ≤ ε₀ (n + 1) := by
  obtain ⟨C, hC, N₀, -, h⟩ := klDiv_R0small_weakSplit_le_unif hd hs0 hsd hτ L hΛ1
  have h1 : Tendsto (fun N : ℕ => aN d s N) atTop (𝓝 0) := RefSmall.tendsto_aN (by omega) hs0 hsd
  have hlim : Tendsto (fun N : ℕ => βp * (C * aN d s N)) atTop (𝓝 0) := by
    simpa using (h1.const_mul C).const_mul βp
  refine ⟨fun N => Real.sqrt (max (βp * (C * aN d s N)) 0 / 2), ?_, N₀, ?_⟩
  · have h0 : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
    have h2 : Tendsto (fun N : ℕ => max (βp * (C * aN d s N)) 0) atTop (𝓝 0) := by
      simpa using hlim.max h0
    have h2' : Tendsto (fun N : ℕ => max (βp * (C * aN d s N)) 0 / 2) atTop (𝓝 0) := by
      simpa using h2.div_const 2
    have h3 := (Real.continuous_sqrt.tendsto 0).comp h2'
    simpa [Function.comp_def] using h3
  · intro β hβ ρ hρ hΛρ n hn _hn1
    have hβ0 : 0 ≤ β := le_trans hβm.le hβ.1
    have hβpβ : β ≤ βp := hβ.2
    haveI := isProb_withDensityReal hρ
    have hq := RefSmall.smallKernel_weakSplit hd hs0 hsd hτ L
    haveI : IsProbabilityMeasure (RefSmall.R0small (weakSplit d s τ L).q β (withDensityReal ρ) (n + 1)) :=
      hq.isProb_R0small hρ hΛρ hβ0 (n + 1)
    have hN1 := h β hβ0 ρ hρ hΛρ (n + 1) hn
    have hex := (RefSmall.R0small_isExchangeable hq.meas hq.even β (withDensityReal ρ) (n + 1)).mul_klDiv_marginal_le
      (withDensityReal ρ) (⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) _
    have e : ENNReal.ofReal (β * ((n + 1 : ℕ) : ℝ) * (C * aN d s (n + 1))) =
        ((n + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (β * (C * aN d s (n + 1))) := by
      have : β * ((n + 1 : ℕ) : ℝ) * (C * aN d s (n + 1)) =
          ((n + 1 : ℕ) : ℝ) * (β * (C * aN d s (n + 1))) := by ring
      rw [this, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    rw [e] at hN1
    have hk := (ENNReal.mul_le_mul_iff_right (by simp) (by simp)).1 (hex.trans hN1)
    rw [Glue.R0_eq_R0small hq.meas hq.even β (withDensityReal ρ) (n + 1)]
    have hCa : 0 ≤ C * aN d s (n + 1) := mul_nonneg hC (aN_nonneg_unif (by omega))
    have hk' := hk.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hβpβ hCa))
    have hne := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hk'
    have htoR := ENNReal.toReal_mono ENNReal.ofReal_ne_top hk'
    rw [ENNReal.toReal_ofReal'] at htoR
    refine (HRS.External.Entropy.tvDist_le_sqrt_klDiv _ _ hne).trans ?_
    exact Real.sqrt_le_sqrt (by linarith)

/-- Uniform eventual smallness of the calibration field (the `hsmall` hypothesis of `core_unif_unif`)
for every `ε > 0`. Original fixed-`β` route: `Q32c.q32c_sup_calibration`, `Q32c.q32c_eventually_hsmall`
(`ε = 1`). The threshold `N₀` depends on `(ε, τ, L, Λ, βm, βp, Ψ)` only. -/
theorem sup_calibration_field_unif (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ}
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (L : ℕ) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) {βm βp : ℝ} (hβm : 0 < βm)
    (hββ : βm ≤ βp) {M : ℕ} (Ψ : Torus d → EuclideanSpace ℝ (Fin M))
    (hΨ : ∀ x y, (weakSplit d s τ L).gL (x - y) = inner ℝ (Ψ x) (Ψ y)) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, IsProbDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ N : ℕ, N₀ ≤ N → ∀ x : Torus d,
        |inner ℝ (Calib.tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N)
          (Calib.Xi (withDensityReal ρ) Ψ x)| ≤ ε := by
  intro ε hε
  obtain ⟨ε₀, hε₀, N₃, hTV⟩ := tv_R0small_unif hd hs0 hsd hτ L hΛ1 hβm hββ
  have hβp0 : 0 ≤ βp := by linarith
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = 2 * Real.sqrt ((weakSplit d s τ L).gL 0) := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hlim : Tendsto (fun N : ℕ => 2 * βp * B ^ 2 * ε₀ N) atTop (𝓝 0) := by
    simpa using hε₀.const_mul (2 * βp * B ^ 2)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds hε))
  refine ⟨max N₃ (max N₁ 2), fun β hβ ρ hρ hΛρ N hN x => ?_⟩
  have hN2 : 2 ≤ N := le_trans (le_max_right N₁ 2) (le_trans (le_max_right N₃ _) hN)
  have hN1 : N₁ ≤ N := le_trans (le_max_left N₁ 2) (le_trans (le_max_right N₃ _) hN)
  have hN3 : N₃ ≤ N := le_trans (le_max_left N₃ _) hN
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  have hβpos : 0 < β := lt_of_lt_of_le hβm hβ.1
  have hβ0 : 0 ≤ β := hβpos.le
  have hβpβ : β ≤ βp := hβ.2
  haveI := isProb_withDensityReal hρ
  have hRH := Calib.refHyp_weakSplit hd hs0 hsd hτ hτ1 L hρ hΛρ Ψ hΨ
  have hq := RefSmall.smallKernel_weakSplit hd hs0 hsd hτ L
  have hΞm : Measurable (Calib.Xi (withDensityReal ρ) Ψ) := hRH.measurable_Xi
  have hBx : ∀ x, ‖Calib.Xi (withDensityReal ρ) Ψ x‖ ≤ B := fun x => by
    rw [hBdef]; exact hRH.norm_Xi_le x
  have hΞ0 : ∫ x, Calib.Xi (withDensityReal ρ) Ψ x ∂(withDensityReal ρ) = 0 := hRH.integral_Xi
  haveI : IsProbabilityMeasure (RefSmall.R0small (weakSplit d s τ L).q β (withDensityReal ρ) (n + 1)) :=
    hq.isProb_R0small hρ hΛρ hβ0 (n + 1)
  have ht : ‖Calib.tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (n + 1)‖ ≤
      β * ‖RefSmall.meanFeature (Calib.Xi (withDensityReal ρ) Ψ)
        (RefSmall.R0small (weakSplit d s τ L).q β (withDensityReal ρ) (n + 1))‖ := by
    have hnpos : 0 < n + 1 := Nat.succ_pos n
    rw [Glue.meanFeature_Xi_eq hΞm hnpos,
      ← Glue.R0_eq_R0small hq.meas hq.even β (withDensityReal ρ) (n + 1)]
    exact hRH.tN_norm_le hβpos hnpos
  have hmean : RefSmall.meanFeature (Calib.Xi (withDensityReal ρ) Ψ)
      (RefSmall.R0small (weakSplit d s τ L).q β (withDensityReal ρ) (n + 1)) =
      ∫ x, Calib.Xi (withDensityReal ρ) Ψ x ∂((RefSmall.R0small (weakSplit d s τ L).q β
        (withDensityReal ρ) (n + 1)).map fun X => X ⟨0, Nat.succ_pos n⟩) :=
    RefSmall.meanFeature_eq_firstMarginal _
      (RefSmall.R0small_isExchangeable hq.meas hq.even β _ (n + 1)) hΞm hBx
  have hnorm := RefSmall.norm_integral_sub_le_two_mul_tvDist
    ((RefSmall.R0small (weakSplit d s τ L).q β (withDensityReal ρ) (n + 1)).map
      fun X => X ⟨0, Nat.succ_pos n⟩) (withDensityReal ρ) hΞm hB0 hBx
  rw [hΞ0, sub_zero, ← hmean] at hnorm
  have hT : HRS.External.Entropy.tvDist ((Calib.R0 (weakSplit d s τ L).q (withDensityReal ρ) β (n + 1)).map
      (fun X => X ⟨0, Nat.succ_pos n⟩)) (withDensityReal ρ) ≤ ε₀ (n + 1) :=
    hTV β hβ ρ hρ hΛρ n hN3 hn
  rw [Glue.R0_eq_R0small hq.meas hq.even β (withDensityReal ρ) (n + 1)] at hT
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = HRS.External.Entropy.tvDist
      ((RefSmall.R0small (weakSplit d s τ L).q β (withDensityReal ρ) (n + 1)).map
        (fun X => X ⟨0, Nat.succ_pos n⟩)) (withDensityReal ρ) := ⟨_, rfl⟩
  rw [← hTdef] at hnorm hT
  have hT0 : 0 ≤ T := by rw [hTdef]; exact HRS.External.Entropy.tvDist_nonneg _ _
  have h2 : ‖Calib.tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (n + 1)‖ ≤ β * (2 * B * T) :=
    ht.trans (mul_le_mul_of_nonneg_left hnorm hβ0)
  have hTε : 2 * β * B ^ 2 * T ≤ 2 * βp * B ^ 2 * ε₀ (n + 1) := by
    have e1 : 2 * β * B ^ 2 * T ≤ 2 * βp * B ^ 2 * T := by
      have h := mul_le_mul_of_nonneg_right hβpβ (mul_nonneg (mul_nonneg zero_le_two (sq_nonneg B)) hT0)
      calc 2 * β * B ^ 2 * T = β * (2 * B ^ 2 * T) := by ring
        _ ≤ βp * (2 * B ^ 2 * T) := h
        _ = 2 * βp * B ^ 2 * T := by ring
    have e2 : 2 * βp * B ^ 2 * T ≤ 2 * βp * B ^ 2 * ε₀ (n + 1) :=
      mul_le_mul_of_nonneg_left hT (mul_nonneg (mul_nonneg zero_le_two hβp0) (sq_nonneg B))
    exact e1.trans e2
  have hKε : 2 * βp * B ^ 2 * ε₀ (n + 1) < ε := hN₁ (n + 1) hN1
  calc |inner ℝ (Calib.tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (n + 1))
        (Calib.Xi (withDensityReal ρ) Ψ x)|
      ≤ ‖Calib.tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (n + 1)‖ *
          ‖Calib.Xi (withDensityReal ρ) Ψ x‖ := abs_real_inner_le_norm _ _
    _ ≤ (β * (2 * B * T)) * B :=
        mul_le_mul h2 (hBx x) (norm_nonneg _)
          (mul_nonneg hβ0 (mul_nonneg (mul_nonneg zero_le_two hB0) hT0))
    _ = 2 * β * B ^ 2 * T := by ring
    _ ≤ 2 * βp * B ^ 2 * ε₀ (n + 1) := hTε
    _ ≤ ε := hKε.le

/-- Uniform version of `Glue.eventually_hsmall` (`HRS/Equilibrium/ReferenceGlue.lean:102`): the case
`ε = 1`, in the form of the original conclusion (sum form of `⟨t_N, Ξ(x)⟩`). The threshold `N₀` is
chosen before `β ∈ [βm, βp]` and before `ρ`. -/
theorem eventually_hsmall_unif (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ}
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (L : ℕ) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) {βm βp : ℝ} (hβm : 0 < βm)
    (hββ : βm ≤ βp) {M : ℕ} (Ψ : Torus d → EuclideanSpace ℝ (Fin M))
    (hΨ : ∀ x y, (weakSplit d s τ L).gL (x - y) = inner ℝ (Ψ x) (Ψ y)) :
    ∃ N₀ : ℕ, ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, IsProbDensity ρ →
      (∀ y, ρ y ≤ Λ) → ∀ N : ℕ, N₀ ≤ N → ∀ x : Torus d,
        |∑ m, (Calib.tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N).ofLp m *
          (Calib.Xi (withDensityReal ρ) Ψ x).ofLp m| ≤ 1 := by
  obtain ⟨N₀, hN₀⟩ := sup_calibration_field_unif hd hs0 hsd hτ hτ1 L hΛ1 hβm hββ Ψ hΨ 1 one_pos
  refine ⟨N₀, fun β hβ ρ hρ hΛρ N hN x => ?_⟩
  rw [← Calib.inner_eq_sum]
  exact hN₀ β hβ ρ hρ hΛρ N hN x

/-- Uniform version of `riesz_Q_le_smul_RN_crude` (`HRS/Equilibrium/QuadraticVariance.lean:2006`):
`K N = exp (8 βp N gL(0))` is chosen before `β ∈ [βm, βp]` and `ρ`. -/
theorem riesz_Q_le_smul_RN_crude_unif (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ}
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (L : ℕ) {Λ : ℝ} {M : ℕ} (Ψ : Torus d → EuclideanSpace ℝ (Fin M))
    (hΨ : ∀ x y, (weakSplit d s τ L).gL (x - y) = inner ℝ (Ψ x) (Ψ y)) {βm βp : ℝ} (hβm : 0 < βm)
    (hββ : βm ≤ βp) :
    ∃ K : ℕ → ℝ, (∀ N, 0 < K N) ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, IsProbDensity ρ →
      (∀ y, ρ y ≤ Λ) → ∀ N : ℕ, 0 < N →
        modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ) ≤
          ENNReal.ofReal (K N) • Calib.RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N := by
  have hg0 : 0 ≤ (weakSplit d s τ L).gL 0 := by
    have h := hΨ 0 0
    rw [sub_self] at h
    rw [h]
    exact real_inner_self_nonneg
  refine ⟨fun N => Real.exp (8 * βp * N * (weakSplit d s τ L).gL 0), fun N => Real.exp_pos _, ?_⟩
  intro β hβ ρ hρ hΛρ N hN
  have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ.1
  have hQ := HRS.Q32c.q32c_Q_le_smul_RN_crude hd hs0 hsd hτ hτ1 L hρ hΛρ Ψ hΨ hβ0 hN
  refine hQ.trans ?_
  show _ ≤ ENNReal.ofReal (Real.exp (8 * βp * N * (weakSplit d s τ L).gL 0)) • _
  rw [Measure.le_iff']
  intro A
  rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
  have h1 : β * (N : ℝ) * (weakSplit d s τ L).gL 0 ≤ βp * (N : ℝ) * (weakSplit d s τ L).gL 0 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hβ.2 (Nat.cast_nonneg N)) hg0
  have h2 : 8 * β * (N : ℝ) * (weakSplit d s τ L).gL 0 ≤
      8 * βp * (N : ℝ) * (weakSplit d s τ L).gL 0 := by
    linarith [h1]
  exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 h2)) zero_le

/-- Uniform version of `Glue.riesz_Q_le_smul_RN_eventually` (`HRS/Equilibrium/ReferenceGlue.lean:141`):
`N₀` is chosen before `β ∈ [βm, βp]` and `ρ`; the hypothesis `KappaSmall` holds for all `β ∈ [βm, βp]`. -/
theorem riesz_Q_le_smul_RN_eventually_unif (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (L : ℕ) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) {βm βp : ℝ}
    (hβm : 0 < βm) (hββ : βm ≤ βp) {M : ℕ} (Ψ : Torus d → EuclideanSpace ℝ (Fin M))
    (hΨ : ∀ x y, (weakSplit d s τ L).gL (x - y) = inner ℝ (Ψ x) (Ψ y))
    (hκ : ∀ β ∈ Set.Icc βm βp, Calib.KappaSmall β (Λ * (weakSplit d s τ L).c)) :
    ∃ N₀ : ℕ, ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, IsProbDensity ρ →
      (∀ y, ρ y ≤ Λ) → ∀ N : ℕ, N₀ ≤ N →
        modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ) ≤
          ENNReal.ofReal (Real.exp (4 * β * (weakSplit d s τ L).gL 0)) •
            Calib.RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N := by
  obtain ⟨N₀, hN₀⟩ := eventually_hsmall_unif hd hs0 hsd hτ hτ1 L hΛ1 hβm hββ Ψ hΨ
  refine ⟨max N₀ 1, fun β hβ ρ hρ hΛρ N hN => ?_⟩
  have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ.1
  exact Calib.riesz_Q_le_smul_RN hd hs0 hsd hτ hτ1 L hρ hΛρ Ψ hΨ hβ0 (by omega) (hκ β hβ)
    (fun x => hN₀ β hβ ρ hρ hΛρ N (by omega) x)

/-- Uniform version of `PairMom.exists_split_params'` (`HRS/Equilibrium/PairMomentsSetting.lean:26`)
for the fixed density bound `Λ₀' = max Λ₀ 1`, without a density: the split parameters are chosen
with smallness at `β := βp`, and `KappaSmall β (Λ₀' c)` then holds for all `β ∈ [βm, βp]`. -/
theorem exists_split_params_unif (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {βm βp : ℝ}
    (hβm : 0 < βm) (hββ : βm ≤ βp) {Λ₀ γ₀ : ℝ} (hγ₀ : 0 < γ₀) :
    ∃ (τ : ℝ) (L : ℕ) (M : ℕ) (Ψ : Torus d → EuclideanSpace ℝ (Fin M)),
      0 < τ ∧ τ ≤ 1 ∧ (∀ x y, (weakSplit d s τ L).gL (x - y) = inner ℝ (Ψ x) (Ψ y)) ∧
      (∀ β ∈ Set.Icc βm βp, Calib.KappaSmall β (max Λ₀ 1 * (weakSplit d s τ L).c)) ∧
      max Λ₀ 1 * (weakSplit d s τ L).c ≤ γ₀ := by
  have hΛpos : 0 < max Λ₀ 1 := lt_max_of_lt_right one_pos
  have hβp : 0 < βp := lt_of_lt_of_le hβm hββ
  have hβne : βp ≠ 0 := hβp.ne'
  have hΛne : max Λ₀ 1 ≠ 0 := hΛpos.ne'
  have hu0 : (0 : ℝ) < 1 / (16 * Real.exp 3) := by positivity
  obtain ⟨τ, hτ, hτ1, L₀, hL₀⟩ := weakSplit_small hd hs0 hsd
    (ε := min (1 / (16 * Real.exp 3) / (βp * max Λ₀ 1)) (γ₀ / max Λ₀ 1))
    (lt_min (div_pos hu0 (mul_pos hβp hΛpos)) (div_pos hγ₀ hΛpos))
  obtain ⟨M, Ψ, -, hΨ, -⟩ := RefSmall.exists_continuous_features_weakSplit hd hs0 hsd hτ L₀
  refine ⟨τ, L₀, M, Ψ, hτ, hτ1, hΨ, ?_, ?_⟩
  · intro β hβ
    obtain ⟨-, -, -, -, -, -, -, -, -, hc0, -⟩ := weakSplit_spec hd hs0 hsd hτ hτ1 L₀
    have hc : (weakSplit d s τ L₀).c ≤ 1 / (16 * Real.exp 3) / (βp * max Λ₀ 1) :=
      (hL₀ L₀ le_rfl).trans (min_le_left _ _)
    have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ.1
    refine PoleVar.kappaSmall_of_le hβ0 (mul_nonneg hΛpos.le hc0) ?_
    calc β * (max Λ₀ 1 * (weakSplit d s τ L₀).c)
        ≤ βp * (max Λ₀ 1 * (weakSplit d s τ L₀).c) :=
          mul_le_mul_of_nonneg_right hβ.2 (mul_nonneg hΛpos.le hc0)
      _ ≤ βp * (max Λ₀ 1 * (1 / (16 * Real.exp 3) / (βp * max Λ₀ 1))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc hΛpos.le) hβp.le
      _ = 1 / (16 * Real.exp 3) := by field_simp
  · have hc : (weakSplit d s τ L₀).c ≤ γ₀ / max Λ₀ 1 :=
      (hL₀ L₀ le_rfl).trans (min_le_right _ _)
    calc max Λ₀ 1 * (weakSplit d s τ L₀).c ≤ max Λ₀ 1 * (γ₀ / max Λ₀ 1) :=
          mul_le_mul_of_nonneg_left hc hΛpos.le
      _ = γ₀ := by field_simp

end HRS.ME.NfU

end
