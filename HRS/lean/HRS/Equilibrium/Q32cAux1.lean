/-
# HRS.Equilibrium.Q32cAux1 -- uniform-in-`rho` constants for the linear variance bound (packet Q32c)
-/
import HRS.Equilibrium.Q32aAux1
import HRS.Equilibrium.Q32bAux1

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Q32c

variable {d : ℕ} {s : ℝ}

open HRS

/-- **Explicit thermal upper bound** (uniform in the potential): `ρ ≤ exp(β(M+A) + β(M+K))` with
`A, K` depending only on the kernel, `|V| ≤ M`. -/
theorem q32c_thermal_upper (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ A K : ℝ, ∀ {V : Torus d → ℝ}, Continuous V → ∀ {M : ℝ}, (∀ x, |V x| ≤ M) → ∀ {β : ℝ},
      0 ≤ β → ∀ {ρ : Torus d → ℝ}, IsThermalDensity (periodicRiesz d s) V β ρ →
        ∀ x, ρ x ≤ Real.exp (β * (M + A) + β * (M + K)) := by
  obtain ⟨B, hB⟩ := periodicRiesz_ge (d := d) hd hs0 hsd
  refine ⟨max B 0, |∫ x, periodicRiesz d s x|, ?_⟩
  intro V hVc M hVM β hβ ρ hρ
  obtain ⟨hprob, hth⟩ := hρ
  have hgi : Integrable (periodicRiesz d s) := KernelAux.integrable_periodicRiesz hd hs0 hsd
  have hB1nn : 0 ≤ max B 0 := le_max_right _ _
  have hB1le : ∀ x, -max B 0 ≤ periodicRiesz d s x :=
    fun x => (neg_le_neg (le_max_left _ _)).trans (hB x)
  have hρi := q32a_integrable_of_isProb hprob
  obtain ⟨hui, huI⟩ := q32a_convFun_integrable_integral hgi hprob
  -- lower bound `u ≥ -B₁` pointwise
  have hu_lb : ∀ x, -max B 0 ≤ convFun (periodicRiesz d s) ρ x := by
    intro x
    by_cases hint : Integrable (fun y => periodicRiesz d s (x - y) * ρ y)
    · have h1 : ∫ y, -max B 0 * ρ y = -max B 0 := by
        rw [integral_const_mul, hprob.integral_one, mul_one]
      calc -max B 0 = ∫ y, -max B 0 * ρ y := h1.symm
        _ ≤ ∫ y, periodicRiesz d s (x - y) * ρ y :=
          integral_mono (hρi.const_mul _) hint
            (fun y => mul_le_mul_of_nonneg_right (hB1le (x - y)) (hprob.nonneg y))
        _ = convFun (periodicRiesz d s) ρ x := rfl
    · have h0 : convFun (periodicRiesz d s) ρ x = 0 := by
        unfold convFun
        exact integral_undef hint
      rw [h0]
      linarith
  -- the partition function
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = ∫ y, Real.exp (-β * (V y + convFun (periodicRiesz d s) ρ y)) :=
    ⟨_, rfl⟩
  have hth' : ∀ x, ρ x = Real.exp (-β * (V x + convFun (periodicRiesz d s) ρ x)) / Z := by
    intro x
    rw [hZ]
    exact hth x
  have hZnn : 0 ≤ Z := by
    rw [hZ]
    exact integral_nonneg fun y => (Real.exp_pos _).le
  have hZne : Z ≠ 0 := by
    intro h0
    have h1 : ∀ x, ρ x = 0 := fun x => by rw [hth' x, h0, div_zero]
    have h2 := hprob.integral_one
    simp only [h1, integral_zero] at h2
    norm_num at h2
  have hZpos : 0 < Z := lt_of_le_of_ne hZnn (Ne.symm hZne)
  -- integrability of the exponent and of its exponential
  have hΦi : Integrable (fun x => -β * (V x + convFun (periodicRiesz d s) ρ x)) :=
    ((q32a_integrable_of_continuous hVc).add hui).const_mul _
  have hEi : Integrable (fun x => Real.exp (-β * (V x + convFun (periodicRiesz d s) ρ x))) := by
    have e : (fun x => Real.exp (-β * (V x + convFun (periodicRiesz d s) ρ x)))
        = fun x => ρ x * Z := by
      funext x
      rw [hth' x, div_mul_cancel₀ _ hZne]
    rw [e]
    exact hρi.mul_const Z
  -- Jensen: `exp (∫ Φ) ≤ ∫ exp Φ = Z`
  have hJ : Real.exp (∫ x, -β * (V x + convFun (periodicRiesz d s) ρ x))
      ≤ ∫ x, Real.exp (-β * (V x + convFun (periodicRiesz d s) ρ x)) :=
    ConvexOn.map_integral_le (convexOn_exp) Real.continuous_exp.continuousOn isClosed_univ
      (Filter.Eventually.of_forall fun x => Set.mem_univ _) hΦi hEi
  -- the integral of the exponent
  have hIV : ∫ x, V x ≤ M := by
    have := integral_mono (q32a_integrable_of_continuous hVc) (integrable_const M)
      (fun x => (abs_le.mp (hVM x)).2)
    simpa using this
  have hΦint : ∫ x, -β * (V x + convFun (periodicRiesz d s) ρ x)
      = -β * ((∫ x, V x) + ∫ x, periodicRiesz d s x) := by
    rw [integral_const_mul, integral_add (q32a_integrable_of_continuous hVc) hui, huI]
  have hlow : -(β * (M + |∫ x, periodicRiesz d s x|))
      ≤ ∫ x, -β * (V x + convFun (periodicRiesz d s) ρ x) := by
    rw [hΦint]
    have hsum : (∫ x, V x) + (∫ x, periodicRiesz d s x)
        ≤ M + |∫ x, periodicRiesz d s x| := by
      linarith [le_abs_self (∫ x, periodicRiesz d s x)]
    have := mul_le_mul_of_nonneg_left hsum hβ
    linarith
  set K : ℝ := β * (M + |∫ x, periodicRiesz d s x|) with hK
  have hZlow : Real.exp (-K) ≤ Z := by
    have h1 : Real.exp (-K) ≤ Real.exp (∫ x, -β * (V x + convFun (periodicRiesz d s) ρ x)) :=
      Real.exp_le_exp.mpr hlow
    rw [hZ]
    exact h1.trans hJ
  -- pointwise upper bound of the exponent
  intro x
  have hup : -β * (V x + convFun (periodicRiesz d s) ρ x) ≤ β * (M + max B 0) := by
    have hv := (abs_le.mp (hVM x)).1
    have hu := hu_lb x
    have h2 : -(M + max B 0) ≤ V x + convFun (periodicRiesz d s) ρ x := by linarith
    have := mul_le_mul_of_nonneg_left h2 hβ
    linarith
  rw [hth' x, div_le_iff₀ hZpos]
  calc Real.exp (-β * (V x + convFun (periodicRiesz d s) ρ x))
      ≤ Real.exp (β * (M + max B 0)) := Real.exp_le_exp.mpr hup
    _ = Real.exp (β * (M + max B 0) + β * (M + |∫ x, periodicRiesz d s x|)) * Real.exp (-K) := by
        rw [← Real.exp_add]
        congr 1
        ring
    _ ≤ Real.exp (β * (M + max B 0) + β * (M + |∫ x, periodicRiesz d s x|)) * Z :=
        mul_le_mul_of_nonneg_left hZlow (Real.exp_pos _).le


section Params

open HRS.External HRS.External.HeatSplit

/-- Choice of the weak split depending only on `(β, Λ)` (not on `ρ`). -/
theorem q32c_split_params (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β) {Λ : ℝ}
    (hΛ1 : 1 ≤ Λ) :
    ∃ (τ : ℝ) (L : ℕ) (M : ℕ) (Ψ : Torus d → EuclideanSpace ℝ (Fin M)),
      0 < τ ∧ τ ≤ 1 ∧
      (∀ x y, (weakSplit d s τ L).gL (x - y) = inner ℝ (Ψ x) (Ψ y)) ∧
      Calib.KappaSmall β (Λ * (weakSplit d s τ L).c) := by
  have hΛpos : 0 < Λ := lt_of_lt_of_le one_pos hΛ1
  set u : ℝ := 1 / (16 * Real.exp 3) with hu
  have hu0 : 0 < u := by positivity
  obtain ⟨τ, hτ, hτ1, L₀, hL₀⟩ := weakSplit_small hd hs0 hsd (ε := u / (β * Λ)) (by positivity)
  obtain ⟨M, Ψ, -, hΨ, -⟩ := RefSmall.exists_continuous_features_weakSplit hd hs0 hsd hτ L₀
  refine ⟨τ, L₀, M, Ψ, hτ, hτ1, hΨ, ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, hc0, -⟩ := weakSplit_spec hd hs0 hsd hτ hτ1 L₀
  have hc := hL₀ L₀ le_rfl
  refine PoleVar.kappaSmall_of_le hβ (mul_nonneg hΛpos.le hc0) ?_
  calc β * (Λ * (weakSplit d s τ L₀).c) ≤ β * (Λ * (u / (β * Λ))) := by gcongr
    _ = u := by field_simp

end Params

section Hsmall

open HRS.External HRS.External.HeatSplit HRS.External.Entropy HRS.External.RefSmall InformationTheory

/-- Uniform (in `ρ ≤ Λ`) total-variation closeness of the first marginal of the weak reference. -/
theorem q32c_tv_uniform (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ) (L : ℕ)
    {Λ : ℝ} (hΛ1 : 1 ≤ Λ) {β : ℝ} (hβ : 0 ≤ β) {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) → ∀ N : ℕ, n₀ ≤ N →
      tvDist ((R0small (weakSplit d s τ L).q β (withDensityReal ρ) (N + 1)).map fun X => X 0)
        (withDensityReal ρ) ≤ ε := by
  obtain ⟨C, hC, N₀, hN₀, h⟩ := klDiv_R0small_weakSplit_le hd hs0 hsd hτ L hΛ1 hβ
  have h1 : Tendsto (fun N : ℕ => aN d s (N + 1)) atTop (𝓝 0) :=
    (tendsto_aN (by omega) hs0 hsd).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun N : ℕ => β * (C * aN d s (N + 1))) atTop (𝓝 0) := by
    simpa using (h1.const_mul C).const_mul β
  have hg : Continuous (fun x : ℝ => Real.sqrt (max x 0 / 2)) := by fun_prop
  have h3 : Tendsto (fun N : ℕ => Real.sqrt (max (β * (C * aN d s (N + 1))) 0 / 2)) atTop (𝓝 0) := by
    have := (hg.tendsto 0).comp h2
    simpa [Function.comp_def] using this
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (h3.eventually (gt_mem_nhds hε))
  refine ⟨max N₁ N₀, fun ρ hρ hΛ N hN => ?_⟩
  haveI := isProb_withDensityReal hρ
  have hq := smallKernel_weakSplit hd hs0 hsd hτ L
  haveI : IsProbabilityMeasure (R0small (weakSplit d s τ L).q β (withDensityReal ρ) (N + 1)) :=
    hq.isProb_R0small hρ hΛ hβ (N + 1)
  have hN1 := h ρ hρ hΛ (N + 1) (by omega)
  have hex := (R0small_isExchangeable hq.meas hq.even β (withDensityReal ρ) (N + 1)).mul_klDiv_marginal_le
    (withDensityReal ρ) (0 : Fin (N + 1)) _
  have e : ENNReal.ofReal (β * ((N + 1 : ℕ) : ℝ) * (C * aN d s (N + 1))) =
      ((N + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (β * (C * aN d s (N + 1))) := by
    have : β * ((N + 1 : ℕ) : ℝ) * (C * aN d s (N + 1)) =
        ((N + 1 : ℕ) : ℝ) * (β * (C * aN d s (N + 1))) := by ring
    rw [this, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  rw [e] at hN1
  have hk : klDiv ((R0small (weakSplit d s τ L).q β (withDensityReal ρ) (N + 1)).map fun X => X 0)
      (withDensityReal ρ) ≤ ENNReal.ofReal (β * (C * aN d s (N + 1))) := by
    have := hex.trans hN1
    exact (ENNReal.mul_le_mul_iff_right (by simp) (by simp)).1 this
  have hne : klDiv ((R0small (weakSplit d s τ L).q β (withDensityReal ρ) (N + 1)).map fun X => X 0)
      (withDensityReal ρ) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hk
  refine ((tvDist_le_sqrt_klDiv _ _ hne).trans ?_).trans (hN₁ N (by omega)).le
  gcongr
  calc (klDiv ((R0small (weakSplit d s τ L).q β (withDensityReal ρ) (N + 1)).map fun X => X 0)
        (withDensityReal ρ)).toReal ≤ (ENNReal.ofReal (β * (C * aN d s (N + 1)))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hk
    _ = max (β * (C * aN d s (N + 1))) 0 := ENNReal.toReal_ofReal'

/-- Uniform version of `RefSmall.sup_calibration_field_le_one`: the threshold depends only on
`(τ, L, Λ, β, B)`, not on the density `ρ ≤ Λ`. -/
theorem q32c_sup_calibration (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ) (L : ℕ)
    {Λ : ℝ} (hΛ1 : 1 ≤ Λ) {β : ℝ} (hβ : 0 ≤ β) {B : ℝ} (hB0 : 0 ≤ B) :
    ∃ n₀ : ℕ, ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ {M : ℕ} (Ξ : Torus d → EuclideanSpace ℝ (Fin M)), Measurable Ξ → (∀ x, ‖Ξ x‖ ≤ B) →
      ∫ x, Ξ x ∂(withDensityReal ρ) = 0 → ∀ (t : ℕ → EuclideanSpace ℝ (Fin M)),
      (∀ n : ℕ, 1 ≤ n →
        ‖t n‖ ≤ β * ‖meanFeature Ξ (R0small (weakSplit d s τ L).q β (withDensityReal ρ) n)‖) →
      ∀ n ≥ n₀, ∀ x : Torus d, |inner ℝ (t n) (Ξ x)| ≤ 1 := by
  have hpos : 0 < 2 * β * B ^ 2 + 1 := by positivity
  obtain ⟨n₀, hn₀⟩ := q32c_tv_uniform hd hs0 hsd hτ L hΛ1 hβ (ε := 1 / (2 * β * B ^ 2 + 1)) (by positivity)
  refine ⟨n₀ + 1, fun ρ hρ hΛ M Ξ hΞm hB hΞ0 t ht n hn x => ?_⟩
  haveI := isProb_withDensityReal hρ
  have hq := smallKernel_weakSplit hd hs0 hsd hτ L
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have hNN : n₀ ≤ N := by omega
  haveI : IsProbabilityMeasure (R0small (weakSplit d s τ L).q β (withDensityReal ρ) (N + 1)) :=
    hq.isProb_R0small hρ hΛ hβ (N + 1)
  have hmean := meanFeature_eq_firstMarginal
    (R0small (weakSplit d s τ L).q β (withDensityReal ρ) (N + 1))
    (R0small_isExchangeable hq.meas hq.even β _ (N + 1)) hΞm hB
  have hnorm := norm_integral_sub_le_two_mul_tvDist
    ((R0small (weakSplit d s τ L).q β (withDensityReal ρ) (N + 1)).map fun X => X 0)
    (withDensityReal ρ) hΞm hB0 hB
  rw [hΞ0, sub_zero] at hnorm
  rw [← hmean] at hnorm
  have h1 := ht (N + 1) (by omega)
  have h2 : ‖t (N + 1)‖ ≤ β * (2 * B * tvDist
      ((R0small (weakSplit d s τ L).q β (withDensityReal ρ) (N + 1)).map fun X => X 0)
      (withDensityReal ρ)) := h1.trans (mul_le_mul_of_nonneg_left hnorm hβ)
  have h3 := hn₀ ρ hρ hΛ N hNN
  have htv := tvDist_nonneg
    ((R0small (weakSplit d s τ L).q β (withDensityReal ρ) (N + 1)).map fun X => X 0)
    (withDensityReal ρ)
  set T := tvDist ((R0small (weakSplit d s τ L).q β (withDensityReal ρ) (N + 1)).map fun X => X 0)
    (withDensityReal ρ) with hT
  have h4 : 2 * β * B ^ 2 * T ≤ 1 := by
    have h5 : (2 * β * B ^ 2 + 1) * T ≤ 1 := by
      have := mul_le_mul_of_nonneg_left h3 hpos.le
      rwa [mul_one_div_cancel hpos.ne'] at this
    nlinarith
  calc |inner ℝ (t (N + 1)) (Ξ x)| ≤ ‖t (N + 1)‖ * ‖Ξ x‖ := abs_real_inner_le_norm _ _
    _ ≤ (β * (2 * B * T)) * B := mul_le_mul h2 (hB x) (norm_nonneg _) (by positivity)
    _ = 2 * β * B ^ 2 * T := by ring
    _ ≤ 1 := h4

/-- Uniform eventual smallness of the calibration field `‖t_N·Ξ‖_∞ ≤ 1` over all probability
densities `ρ ≤ Λ`. -/
theorem q32c_eventually_hsmall (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (L : ℕ) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) {M : ℕ}
    (Ψ : Torus d → EuclideanSpace ℝ (Fin M))
    (hΨ : ∀ x y, (weakSplit d s τ L).gL (x - y) = inner ℝ (Ψ x) (Ψ y)) {β : ℝ} (hβ : 0 < β) :
    ∃ N₀ : ℕ, ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ y, ρ y ≤ Λ) → ∀ N : ℕ, N₀ ≤ N →
      ∀ x : Torus d,
      |∑ m, (Calib.tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N).ofLp m *
        (Calib.Xi (withDensityReal ρ) Ψ x).ofLp m| ≤ 1 := by
  have hB0 : 0 ≤ 2 * Real.sqrt ((weakSplit d s τ L).gL 0) := by positivity
  obtain ⟨n₀, hn₀⟩ := q32c_sup_calibration hd hs0 hsd hτ L hΛ1 hβ.le hB0
  refine ⟨n₀, fun ρ hρ hρΛ N hN x => ?_⟩
  haveI := isProb_withDensityReal hρ
  have hRH := Calib.refHyp_weakSplit hd hs0 hsd hτ hτ1 L hρ hρΛ Ψ hΨ
  have hΞm : Measurable (Calib.Xi (withDensityReal ρ) Ψ) := hRH.measurable_Xi
  have hB : ∀ x, ‖Calib.Xi (withDensityReal ρ) Ψ x‖ ≤ 2 * Real.sqrt ((weakSplit d s τ L).gL 0) :=
    hRH.norm_Xi_le
  have hΞ0 : ∫ x, Calib.Xi (withDensityReal ρ) Ψ x ∂(withDensityReal ρ) = 0 := hRH.integral_Xi
  have ht : ∀ n : ℕ, 1 ≤ n →
      ‖Calib.tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β n‖ ≤
        β * ‖RefSmall.meanFeature (Calib.Xi (withDensityReal ρ) Ψ)
          (RefSmall.R0small (weakSplit d s τ L).q β (withDensityReal ρ) n)‖ := by
    intro n hn
    have hnpos : 0 < n := by omega
    rw [Glue.meanFeature_Xi_eq hΞm hnpos, ← Glue.R0_eq_R0small hRH.q_meas hRH.q_even β (withDensityReal ρ) n]
    exact hRH.tN_norm_le hβ hnpos
  have h := hn₀ ρ hρ hρΛ (Calib.Xi (withDensityReal ρ) Ψ) hΞm hB hΞ0
    (fun n => Calib.tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β n) ht N hN x
  rw [← Calib.inner_eq_sum]
  exact h

end Hsmall

section Crude

open Function

open HRS HRS.External HRS.External.RefMarg HRS.External.PoleVar HRS.External.HeatSplit HRS.Quad

/-- Explicit `Q_N ≤ e^{8βN g_L(0)} R_N` for every `N ≥ 1` (the denominator `∫ e^{logW} dR_N`
is at least `e^{-8βN g_L(0)}` since `|logW| ≤ 8βN g_L(0)` pointwise). -/
theorem q32c_Q_le_smul_RN_crude (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (L : ℕ) {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) {Λ : ℝ} (hρΛ : ∀ y, ρ y ≤ Λ)
    {M : ℕ} (Ψ : Torus d → EuclideanSpace ℝ (Fin M))
    (hΨ : ∀ x y, (weakSplit d s τ L).gL (x - y) = inner ℝ (Ψ x) (Ψ y)) {β : ℝ} (hβ : 0 < β)
    {N : ℕ} (hN : 0 < N) :
    modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ) ≤
      ENNReal.ofReal (Real.exp (8 * β * N * (weakSplit d s τ L).gL 0)) •
        Calib.RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N := by
  haveI := isProb_withDensityReal hρ
  have hRH := Calib.refHyp_weakSplit hd hs0 hsd hτ hτ1 L hρ hρΛ Ψ hΨ
  haveI := hRH.isProb_RN (N := N) hβ.le
  set P := Calib.RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N with hP
  set gL0 : ℝ := (weakSplit d s τ L).gL 0 with hgL0
  have hg0 : 0 ≤ gL0 := hRH.gL_zero_nonneg
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set Z : ℝ := ∫ Y, Real.exp (Calib.logW (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N Y) ∂P with hZ
  have hZpos : 0 < Z := integral_exp_pos (hRH.integrable_exp_logW hβ (P := P))
  -- bound on `Xibar`
  have hXb : ‖Calib.Xibar (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N‖ ≤ 2 * Real.sqrt gL0 := by
    have := norm_integral_le_of_norm_le_const (μ := P) (f := Calib.empXi (withDensityReal ρ) Ψ)
      (C := 2 * Real.sqrt gL0) (Filter.Eventually.of_forall (hRH.norm_empXi_le hN))
    simpa [Calib.Xibar] using this
  have hlow : ∀ Y, -(8 * β * N * gL0) ≤
      Calib.logW (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N Y := by
    intro Y
    have h1 := hRH.norm_Dv_le hN (Calib.Xibar (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N) Y
    have h2 : ‖Calib.Sstat (withDensityReal ρ) Ψ Y - Real.sqrt N •
        Calib.Xibar (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N‖ ≤
        Real.sqrt N * (4 * Real.sqrt gL0) :=
      h1.trans (mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _))
    have h3 : ‖Calib.Sstat (withDensityReal ρ) Ψ Y - Real.sqrt N •
        Calib.Xibar (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N‖ ^ 2 ≤ 16 * N * gL0 := by
      calc _ ≤ (Real.sqrt N * (4 * Real.sqrt gL0)) ^ 2 := by gcongr
        _ = 16 * N * gL0 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt hNR.le, Real.sq_sqrt hg0]; ring
    unfold Calib.logW
    nlinarith [mul_le_mul_of_nonneg_left h3 (show 0 ≤ β / 2 by positivity)]
  have hZge : Real.exp (-(8 * β * N * gL0)) ≤ Z := by
    have h1 : ∫ _Y, Real.exp (-(8 * β * N * gL0)) ∂P ≤ Z :=
      integral_mono (integrable_const _) (hRH.integrable_exp_logW hβ (P := P))
        (fun Y => Real.exp_le_exp.2 (hlow Y))
    simpa using h1
  rw [Calib.modulatedGibbs_riesz_eq_split hd hs0 hsd hτ hτ1 L hρ,
    hRH.Q_eq_RN_withDensity hβ hN (weakSplit d s τ L).c]
  intro A
  rw [withDensity_apply' _ A, Measure.smul_apply, smul_eq_mul]
  calc ∫⁻ x in A, ENNReal.ofReal (Real.exp (Calib.logW (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N x) / Z) ∂P
      ≤ ∫⁻ _x in A, ENNReal.ofReal (Real.exp (8 * β * N * gL0)) ∂P := by
        refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
        rw [div_le_iff₀ hZpos]
        calc Real.exp (Calib.logW (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N x) ≤ 1 :=
              Real.exp_le_one_iff.2 (Calib.RefHyp.logW_nonpos hβ x)
          _ = Real.exp (8 * β * N * gL0) * Real.exp (-(8 * β * N * gL0)) := by
              rw [← Real.exp_add]; simp
          _ ≤ _ := mul_le_mul_of_nonneg_left hZge (Real.exp_pos _).le
    _ = _ := by rw [setLIntegral_const]

/-- **Crude bound for a fixed `N`, uniform in `ρ ≤ Λ`.** -/
theorem q32c_crude (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β) {Λ : ℝ}
    (hΛ1 : 1 ≤ Λ) {N : ℕ} (hN : 2 ≤ N) :
    ∃ C : ℝ, ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ y, ρ y ≤ Λ) →
      ∀ f : Torus d → ℝ, Measurable f → MemLp f 2 (withDensityReal ρ) →
      (N : ℝ≥0∞) * evariance (fun X : Config d N => (1 / (N : ℝ)) * ∑ i, f (X i))
          (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
        ENNReal.ofReal (C * ∫ x, f x ^ 2 ∂(withDensityReal ρ)) := by
  have hN0 : 0 < N := by omega
  obtain ⟨τ, L, M, Ψ, hτ, hτ1, hΨ, hκ⟩ := q32c_split_params hd hs0 hsd hβ hΛ1
  set γ : ℝ := Λ * (weakSplit d s τ L).c with hγ
  set K0 : ℝ := max 1 (4 * β * (weakSplit d s τ L).gL 0) with hK0
  set K' : ℝ := Real.exp (8 * β * N * (weakSplit d s τ L).gL 0) with hK'
  set Ep : ℝ := Real.exp ((β * γ + K0) + 0 + β * γ) with hEp
  refine ⟨N * (K' * Ep), fun ρ hρ hρΛ f hf hf2 => ?_⟩
  haveI hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ
  have hRH := Calib.refHyp_weakSplit hd hs0 hsd hτ hτ1 L hρ hρΛ Ψ hΨ
  have ht0 : ∀ x, |inner ℝ (Calib.tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N)
      (Calib.Xi (withDensityReal ρ) Ψ x)| ≤ K0 :=
    fun x => (abs_tN_inner_le hRH hβ hN0 x).trans (le_max_right _ _)
  set V := weakPotK hRH hβ.le (Calib.tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N) ht0 with hV
  have hRN : Calib.RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N =
      pinnedLaw V (β / ((N : ℕ) : ℝ)) N (fun e : Empty => e.elim) := by
    rw [RN_eq_fieldLawK hRH hβ.le ht0, pinnedLaw_empty]
  have hQK := q32c_Q_le_smul_RN_crude hd hs0 hsd hτ hτ1 L hρ hρΛ Ψ hΨ hβ hN0
  haveI hQp := riesz_Q_isProb hd hs0 hsd hτ hτ1 L hρ hρΛ Ψ hΨ hβ hN0
  have hK'0 : 0 < K' := Real.exp_pos _
  have hm : ∀ i : Fin N, (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)).map (fun X => X i) ≤
      ENNReal.ofReal (K' * Ep) • withDensityReal ρ := by
    intro i
    have h1 : (pinnedLaw V (β / ((N : ℕ) : ℝ)) N (fun e : Empty => e.elim)).map (fun y => y i) ≤
        ENNReal.ofReal Ep • withDensityReal ρ :=
      marginal_le_smul (B := Empty) V hβ.le hN0 (n := N) (by simp) (fun e => e.elim) i
    rw [← hRN] at h1
    refine (Measure.map_mono hQK (measurable_pi_apply i)).trans ?_
    rw [Measure.map_smul _ (measurable_pi_apply i).aemeasurable]
    refine Measure.le_iff'.2 fun A => ?_
    have h2 := h1 A
    rw [Measure.smul_apply, smul_eq_mul] at h2
    rw [Measure.smul_apply, smul_eq_mul, Measure.smul_apply, smul_eq_mul]
    calc ENNReal.ofReal K' * (Calib.RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N).map (fun X => X i) A
        ≤ ENNReal.ofReal K' * (ENNReal.ofReal Ep * withDensityReal ρ A) := mul_le_mul' le_rfl h2
      _ = _ := by rw [← mul_assoc, ENNReal.ofReal_mul hK'0.le]
  exact HRS.Q32b.q32b_marg_bound hN0 (mul_nonneg hK'0.le (Real.exp_pos _).le) hm hf hf2

end Crude

section Large

open Function

open HRS HRS.External HRS.External.RefMarg HRS.External.PoleVar HRS.External.HeatSplit HRS.Quad

/-- **Large `N`, uniform in `ρ ≤ Λ`.** -/
theorem q32c_large (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β) {Λ : ℝ}
    (hΛ1 : 1 ≤ Λ) :
    ∃ (C : ℝ) (N₁ : ℕ), ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ y, ρ y ≤ Λ) →
      ∀ N : ℕ, N₁ ≤ N → 2 ≤ N → ∀ f : Torus d → ℝ, Measurable f →
      MemLp f 2 (withDensityReal ρ) →
      (N : ℝ≥0∞) * evariance (fun X : Config d N => (1 / (N : ℝ)) * ∑ i, f (X i))
          (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
        ENNReal.ofReal (C * ∫ x, f x ^ 2 ∂(withDensityReal ρ)) := by
  obtain ⟨τ, L, M, Ψ, hτ, hτ1, hΨ, hκ⟩ := q32c_split_params hd hs0 hsd hβ hΛ1
  set γ : ℝ := Λ * (weakSplit d s τ L).c with hγ
  set gL0 : ℝ := (weakSplit d s τ L).gL 0 with hgL0
  obtain ⟨N₀, hN₀⟩ := q32c_eventually_hsmall hd hs0 hsd hτ hτ1 L hΛ1 Ψ hΨ hβ
  set KQ : ℝ := Real.exp (4 * β * gL0) with hKQ
  have hKQ0 : 0 < KQ := Real.exp_pos _
  set E : ℝ := Real.exp ((β * γ + 1) + 0 + β * γ) with hE
  have hE0 : 0 < E := Real.exp_pos _
  refine ⟨2 * KQ * E, max N₀ 2, fun ρ hρ hρΛ N hN hN2 f hf hf2 => ?_⟩
  haveI hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ
  have hRH := Calib.refHyp_weakSplit hd hs0 hsd hτ hτ1 L hρ hρΛ Ψ hΨ
  have hNN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hNn : 0 < n + 1 := Nat.succ_pos n
  have hsmall := hN₀ ρ hρ hρΛ (n + 1) hNN₀
  have ht : ∀ x, |inner ℝ (Calib.tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (n + 1))
      (Calib.Xi (withDensityReal ρ) Ψ x)| ≤ 1 := fun x => by
    have := hsmall x
    rwa [← Calib.inner_eq_sum] at this
  set V := weakPotK hRH hβ.le (Calib.tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (n + 1)) ht with hV
  have hRN : Calib.RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (n + 1) =
      pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim) := by
    rw [RN_eq_fieldLawK hRH hβ.le ht, pinnedLaw_empty]
  have hκV : weakKappa V β ≤ 1 / 2 := weakKappa_weakPotK_le hRH hβ.le ht hκ
  haveI hQp := riesz_Q_isProb hd hs0 hsd hτ hτ1 L hρ hρΛ Ψ hΨ hβ hNn
  have hQK := Calib.riesz_Q_le_smul_RN hd hs0 hsd hτ hτ1 L hρ hρΛ Ψ hΨ hβ hNn hκ hsmall
  rw [hRN] at hQK
  set R0 := pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim) with hR0
  haveI hRp : IsProbabilityMeasure (Calib.RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (n + 1)) :=
    hRH.isProb_RN hβ.le
  haveI hR0p : IsProbabilityMeasure R0 := by rw [← hRN]; exact hRp
  set π0 : Measure (Torus d) := R0.map (fun X => X 0) with hπ0
  haveI hπ0p : IsProbabilityMeasure π0 := inferInstance
  have hπ0le : π0 ≤ ENNReal.ofReal E • withDensityReal ρ :=
    marginal_le_smul (B := Empty) V hβ.le hNn (n := n + 1) (by simp) (fun e => e.elim) ⟨0, hNn⟩
  have hS : Measurable fun X : Config d (n + 1) => ∑ i, f (X i) :=
    Finset.measurable_sum _ fun i _ => hf.comp (measurable_pi_apply i)
  have hI : ∫⁻ z, ‖f z‖ₑ ^ 2 ∂(withDensityReal ρ) = ENNReal.ofReal (∫ z, f z ^ 2 ∂(withDensityReal ρ)) :=
    lintegral_enorm_sq_eq_ofReal hf2
  have hπ2 : evariance f π0 ≤ ENNReal.ofReal E * ENNReal.ofReal (∫ z, f z ^ 2 ∂(withDensityReal ρ)) := by
    refine (HRS.External.evariance_le_lintegral_sub π0 hf.aestronglyMeasurable 0).trans ?_
    simp only [sub_zero]
    calc ∫⁻ z, ‖f z‖ₑ ^ 2 ∂π0 ≤ ∫⁻ z, ‖f z‖ₑ ^ 2 ∂(ENNReal.ofReal E • withDensityReal ρ) :=
          lintegral_mono' hπ0le le_rfl
      _ = _ := by rw [lintegral_smul_measure, smul_eq_mul, hI]
  have hlin := weak_linear_variance_symm (B := Empty) V hβ.le hNn (n := n + 1) (by simp)
    (fun e : Empty => e.elim) hκV f hf
  have hQR := evariance_le_of_le_smul hQK hS
  have hc : evariance (fun X : Config d (n + 1) => (1 / ((n + 1 : ℕ) : ℝ)) * ∑ i, f (X i))
      (modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ)) =
      ENNReal.ofReal ((1 / ((n + 1 : ℕ) : ℝ)) ^ 2) * evariance (fun X : Config d (n + 1) => ∑ i, f (X i))
        (modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ)) := evariance_mul _ _ _
  rw [hc]
  have hNR : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hNn
  calc ((n + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal ((1 / ((n + 1 : ℕ) : ℝ)) ^ 2) *
        evariance (fun X : Config d (n + 1) => ∑ i, f (X i))
          (modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ)))
      ≤ ((n + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal ((1 / ((n + 1 : ℕ) : ℝ)) ^ 2) *
          (ENNReal.ofReal KQ * (2 * ((n + 1 : ℕ) : ℝ≥0∞) *
            (ENNReal.ofReal E * ENNReal.ofReal (∫ z, f z ^ 2 ∂(withDensityReal ρ)))))) := by
        gcongr
        refine hQR.trans ?_
        gcongr
        exact hlin.trans (by gcongr)
    _ = ENNReal.ofReal (2 * KQ * E * ∫ x, f x ^ 2 ∂(withDensityReal ρ)) := by
        have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
        rw [h2, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp

end Large

section Main

open HRS HRS.Quad

/-- **`q32c_main`**: the linear variance bound with a constant depending only on `(d, s, β, Λ)`:
uniform over all probability densities `ρ ≤ Λ`. -/
theorem q32c_main (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β) (Λ : ℝ)
    (hΛ1 : 1 ≤ Λ) :
    ∃ C : ℝ, ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ y, ρ y ≤ Λ) →
      ∀ N : ℕ, 2 ≤ N → ∀ f : Torus d → ℝ, Measurable f →
      MemLp f 2 (withDensityReal ρ) →
        (N : ℝ≥0∞) * evariance (fun X : Config d N => (1 / (N : ℝ)) * ∑ i, f (X i))
            (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
          ENNReal.ofReal (C * ∫ x, f x ^ 2 ∂(withDensityReal ρ)) := by
  obtain ⟨C₁, N₁, h1⟩ := q32c_large hd hs0 hsd hβ hΛ1
  have hc : ∀ N : ℕ, ∃ C : ℝ, 2 ≤ N → ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ y, ρ y ≤ Λ) →
      ∀ f : Torus d → ℝ, Measurable f →
      MemLp f 2 (withDensityReal ρ) →
        (N : ℝ≥0∞) * evariance (fun X : Config d N => (1 / (N : ℝ)) * ∑ i, f (X i))
            (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
          ENNReal.ofReal (C * ∫ x, f x ^ 2 ∂(withDensityReal ρ)) := by
    intro N
    by_cases hN : 2 ≤ N
    · obtain ⟨C, hC⟩ := q32c_crude hd hs0 hsd hβ hΛ1 hN
      exact ⟨C, fun _ => hC⟩
    · exact ⟨0, fun h => absurd h hN⟩
  choose Cs hCs using hc
  refine ⟨|C₁| + ∑ N ∈ Finset.range N₁, |Cs N|, ?_⟩
  intro ρ hρ hρΛ N hN f hf hf2
  have hI : 0 ≤ ∫ x, f x ^ 2 ∂(withDensityReal ρ) := integral_nonneg fun _ => sq_nonneg _
  by_cases hNN : N₁ ≤ N
  · refine (h1 ρ hρ hρΛ N hNN hN f hf hf2).trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 : C₁ ≤ |C₁| + ∑ N ∈ Finset.range N₁, |Cs N| := by
      have := le_abs_self C₁
      have : 0 ≤ ∑ N ∈ Finset.range N₁, |Cs N| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      linarith
    exact mul_le_mul_of_nonneg_right h2 hI
  · have hlt : N < N₁ := not_le.1 hNN
    refine (hCs N hN ρ hρ hρΛ f hf hf2).trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 : Cs N ≤ |C₁| + ∑ N ∈ Finset.range N₁, |Cs N| := by
      have h3 : |Cs N| ≤ ∑ N ∈ Finset.range N₁, |Cs N| :=
        Finset.single_le_sum (f := fun N => |Cs N|) (fun M _ => abs_nonneg (Cs M)) (Finset.mem_range.2 hlt)
      have := le_abs_self (Cs N)
      have := abs_nonneg C₁
      linarith
    exact mul_le_mul_of_nonneg_right h2 hI

end Main

end HRS.Q32c

end
