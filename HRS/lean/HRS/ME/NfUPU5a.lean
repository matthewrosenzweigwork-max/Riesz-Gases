import HRS.Equilibrium.ReferenceMarginal

/-!
# Packet PU5a (uniform-in-`β` versions of `cavD_torus` and `core_L2`)

* `cavD_torus_unif` is `HRS.External.RefMarg.cavD_torus` with the constant `(CD, N₁)` chosen for all
  `β ∈ [βm, βp]` at once. `Cν` is a fixed parameter (chosen before `β`); the hypothesis
  `exp (V.M + V.M' + β V.γ) ≤ Cν` and `weakKappa V β ≤ 1/2` are kept per `β`.
  Changes against the original proof: `N₁ = ⌈βp⌉₊ + 1`; `CD` is bounded by its value at `β := βp`
  (exp, `β²`, `β^(p-1)` are monotone in `β`); `gFun (N/β) ≤ c' gFun N` is obtained from
  `gFun_mul_le` at `c = 1/βm` and the monotonicity `gFun_mono_aux`.
* `core_L2_unif` is `HRS.External.RefMarg.core_L2` with `(C, N₁)` chosen before `β ∈ [βm, βp]`; the
  hypothesis `KappaSmall β (Λ c)` becomes `∀ β ∈ [βm, βp], KappaSmall β (Λ c)`. It uses `cavD_torus_unif`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.ME.NfU

open HRS HRS.External HRS.External.Calib HeatSplit HRS.External.RefMarg

variable {d M : ℕ}

/-- `gFun d s` is nondecreasing on `[1, ∞)` (used to pass from `N/β` to `N/βm`). -/
theorem gFun_mono_aux {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {K K' : ℝ} (hK : 1 ≤ K)
    (hKK : K ≤ K') : gFun d s K ≤ gFun d s K' := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  unfold gFun
  by_cases h1 : s < (d : ℝ) / 2
  · simp [h1]
  · have hs_pos : 0 < s := by linarith [not_lt.1 h1]
    by_cases h2 : s = (d : ℝ) / 2
    · rw [if_neg h1, if_neg h1, if_pos h2, if_pos h2]
      exact Real.log_le_log (mul_pos (Real.exp_pos 1) (by linarith))
        (mul_le_mul_of_nonneg_left hKK (Real.exp_pos 1).le)
    · rw [if_neg h1, if_neg h1, if_neg h2, if_neg h2]
      have hds : (d : ℝ) / s ≤ 2 := by
        rw [div_le_iff₀ hs_pos]
        have h3 : (d : ℝ) / 2 < s := lt_of_le_of_ne (not_lt.1 h1) (Ne.symm h2)
        linarith
      exact Real.rpow_le_rpow (by linarith) hKK (by linarith)

/-- Uniform-in-`β` version of `cavD_torus` (`HRS/Equilibrium/ReferenceMarginal.lean:1496`). -/
theorem cavD_torus_unif (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    {Λ : ℝ} (hΛ1 : 1 ≤ Λ)
    {q : Torus d → ℝ} (hqm : Measurable q) (hq0 : ∀ z, 0 ≤ q z) (hqe : ∀ z, q (-z) = q z)
    {c : ℝ} (hc0 : 0 ≤ c) (hqc : ∫⁻ z, ENNReal.ofReal (q z) ≤ ENNReal.ofReal c)
    {K0 : ℝ} (hK0 : 0 < K0)
    (hw : ∀ r : ℝ, 0 < r → (volume : Measure (Torus d)) {z : Torus d | r < q z} ≤
      ENNReal.ofReal (K0 * r ^ (-(pOf d s))))
    {βm βp : ℝ} (hβm : 0 < βm) (hββ : βm ≤ βp) {Cν : ℝ} (hCν : 1 ≤ Cν) :
    ∃ (CD : ℝ) (N₁ : ℕ), 0 ≤ CD ∧ ∀ β ∈ Set.Icc βm βp, ∀ (ρ : Torus d → ℝ), IsProbDensity ρ →
      (∀ x, ρ x ≤ Λ) →
      ∀ (V : WeakPotential (withDensityReal ρ)),
      (∀ x y, V.q x y = q (x - y)) → Real.exp (V.M + V.M' + β * V.γ) ≤ Cν → weakKappa V β ≤ 1 / 2 →
      ∀ (N n : ℕ) [NeZero n], N₁ ≤ N → n ≤ N → ∀ x : Torus d,
        0 ≤ Real.log (cavU V (β / N) n (fun e : Empty => e.elim) x) +
          β / N * n * ∫ y, V.q y x ∂(cavMarg V (β / N) n) ∧
        Real.log (cavU V (β / N) n (fun e : Empty => e.elim) x) +
          β / N * n * ∫ y, V.q y x ∂(cavMarg V (β / N) n) ≤ CD * deltaN d s N := by
  have hp := one_lt_pOf hd hs0 hsd
  set p := pOf d s with hpdef
  have hpp : 0 < p - 1 := by linarith
  have hQ0 : 0 ≤ p / (p - 1) := div_nonneg (by linarith) hpp.le
  obtain ⟨c₁, hc₁, hR2⟩ := second_moment_gFun hd hs0 hsd hK0
  obtain ⟨c', hc', hscale⟩ := gFun_mul_le hd hs0 hsd (c := 1 / βm) (by positivity)
  have hΛ0 : 0 ≤ Λ := by linarith
  have hCν0 : 0 ≤ Cν := by linarith
  have hβp0 : 0 < βp := lt_of_lt_of_le hβm hββ
  have hmax0 : 0 ≤ Cν * (Λ * c) := mul_nonneg hCν0 (mul_nonneg hΛ0 hc0)
  set CDu : ℝ := Real.exp (βp * (Cν * (Λ * c))) * βp ^ 2 * Cν * Λ * c₁ * c' +
      βp * Cν * Λ * (K0 * (p / (p - 1))) * βp ^ (p - 1) with hCDu
  have hCD0 : 0 ≤ CDu := by
    rw [hCDu]
    positivity
  refine ⟨CDu, ⌈βp⌉₊ + 1, hCD0, ?_⟩
  intro β hβI ρ hρ hΛ V hVq hVC hκ N n _ hN hn x
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hβpβ : β ≤ βp := hβI.2
  haveI := isProb_withDensityReal hρ
  have hNβ : β ≤ N := by
    have : (⌈βp⌉₊ : ℝ) + 1 ≤ N := by exact_mod_cast hN
    linarith [Nat.le_ceil βp]
  have hN1 : 1 ≤ N := by omega
  have hN0 : 0 < N := hN1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  set lam : ℝ := β / N with hlam
  have hlampos : 0 < lam := by positivity
  have hVqx : ∀ y, V.q y x = q (x - y) := fun y => by rw [hVq, ← hqe, neg_sub]
  have hν : cavMarg V lam n ≤ ENNReal.ofReal Cν • withDensityReal ρ := by
    have h1 := marginal_le_smul (B := Empty) V hβ.le hN0 (n := n) (by simpa using hn)
      (fun e : Empty => e.elim) 0
    refine h1.trans ?_
    intro A
    simp only [Measure.smul_apply, smul_eq_mul]
    gcongr
  have hI1 : ∫ y, V.q y x ∂(cavMarg V lam n) ≤ Cν * (Λ * c) := by
    simp_rw [hVqx]
    exact integral_kernel_le hΛ hΛ0 hν hCν0 hqm hq0 hc0 hqc x
  have hI0 : 0 ≤ ∫ y, V.q y x ∂(cavMarg V lam n) := integral_nonneg fun y => V.q_nonneg _ _
  have hlamn : lam * n ≤ β := by
    have : (n : ℝ) ≤ N := by exact_mod_cast hn
    calc lam * n ≤ lam * N := by gcongr
      _ = β := by rw [hlam]; field_simp
  have hlamn' : (n : ℝ) * lam ≤ β := by linarith [hlamn, mul_comm (n : ℝ) lam]
  set mb : ℝ := β * (Cν * (Λ * c)) with hmb
  have hm : lam * n * ∫ y, V.q y x ∂(cavMarg V lam n) ≤ mb := by
    calc lam * n * ∫ y, V.q y x ∂(cavMarg V lam n) ≤ β * ∫ y, V.q y x ∂(cavMarg V lam n) := by gcongr
      _ ≤ β * (Cν * (Λ * c)) := by gcongr
  obtain ⟨h1, h2⟩ := cavD_bounds V hβ.le hN0 hn hκ x hm
  refine ⟨h1, h2.trans ?_⟩
  set ν := cavMarg V lam n with hνdef
  set K : ℝ := N / β with hK
  have hKpos : 0 < K := by positivity
  have hK1 : 1 ≤ K := by rw [hK, le_div_iff₀ hβ]; linarith
  have hKlam : lam * K = 1 := by rw [hlam, hK]; field_simp
  -- the second-moment term
  have hA : ∫ y, (min (lam * V.q y x) 1) ^ 2 ∂ν ≤ Cν * (Λ * (lam ^ 2 * (c₁ * gFun d s K))) := by
    simp_rw [hVqx]
    refine integral_kernel_le (h := fun z => (min (lam * q z) 1) ^ 2) hΛ hΛ0 hν hCν0
      ((hqm.const_mul lam).min measurable_const |>.pow_const 2) (fun z => sq_nonneg _)
      (by have := hR2 K hK1; have := one_le_gFun hd hs0 hsd hK1; positivity) ?_ x
    have e : ∀ z, ENNReal.ofReal ((min (lam * q z) 1) ^ 2) =
        ENNReal.ofReal (lam ^ 2) * ENNReal.ofReal (min (q z) K ^ 2) := by
      intro z
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have : min (lam * q z) 1 = lam * min (q z) K := by
        rw [mul_min_of_nonneg _ _ hlampos.le, hKlam]
      rw [this]; ring
    simp_rw [e]
    rw [lintegral_const_mul (ENNReal.ofReal (lam ^ 2)) (f := fun z => ENNReal.ofReal (min (q z) K ^ 2))
      (ENNReal.measurable_ofReal.comp ((hqm.min measurable_const).pow_const 2))]
    calc ENNReal.ofReal (lam ^ 2) * ∫⁻ z, ENNReal.ofReal (min (q z) K ^ 2)
        ≤ ENNReal.ofReal (lam ^ 2) * ENNReal.ofReal (1 + 2 * K0 * ∫ t in (1 : ℝ)..K, t ^ (1 - p)) := by
          gcongr
          exact lintegral_minsq_le hqm hq0 hK1 hp hK0 hw
      _ ≤ ENNReal.ofReal (lam ^ 2) * ENNReal.ofReal (c₁ * gFun d s K) := by
          gcongr
          exact hR2 K hK1
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]
  -- the tail term
  set T : ℝ := K0 * K ^ (1 - p) * (p / (p - 1)) with hT
  have hT0 : 0 ≤ T := by
    have : 0 < p - 1 := by linarith
    positivity
  have hB : ∫ y, max (lam * V.q y x - 1) 0 ∂ν ≤ Cν * (Λ * (lam * T)) := by
    simp_rw [hVqx]
    refine integral_kernel_le (h := fun z => max (lam * q z - 1) 0) hΛ hΛ0 hν hCν0
      (((hqm.const_mul lam).sub_const 1).max measurable_const) (fun z => le_max_right _ _)
      (by positivity) ?_ x
    have e : ∀ z, ENNReal.ofReal (max (lam * q z - 1) 0) = ENNReal.ofReal lam * ENNReal.ofReal (q z - K) := by
      intro z
      rw [← ENNReal.ofReal_mul hlampos.le, ENNReal.ofReal_max]
      simp only [ENNReal.ofReal_zero]
      rw [max_eq_left (by simp)]
      congr 1
      rw [mul_sub, hKlam]
    simp_rw [e]
    rw [lintegral_const_mul (ENNReal.ofReal lam) (f := fun z => ENNReal.ofReal (q z - K))
      (ENNReal.measurable_ofReal.comp (hqm.sub_const K))]
    calc ENNReal.ofReal lam * ∫⁻ z, ENNReal.ofReal (q z - K)
        ≤ ENNReal.ofReal lam * ENNReal.ofReal T := by
          gcongr
          exact lintegral_tail_le hqm hq0 hKpos hp hK0 hw
      _ = _ := by rw [← ENNReal.ofReal_mul hlampos.le]
  -- assemble
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hG := deltaN_eq_gFun hd hs0 hsd hN1
  have hgK : gFun d s K ≤ c' * gFun d s N := by
    have hKle : K ≤ 1 / βm * (N : ℝ) := by
      calc K = (N : ℝ) / β := hK
        _ ≤ (N : ℝ) / βm := div_le_div_of_nonneg_left hNpos.le hβm hβI.1
        _ = 1 / βm * (N : ℝ) := by ring
    exact (gFun_mono_aux hd hs0 hsd hK1 hKle).trans (hscale (N : ℝ) hN1' (hK1.trans hKle))
  have hKr : K ^ (1 - p) ≤ β ^ (p - 1) * ((N : ℝ)⁻¹ * gFun d s N) := by
    have h1 := rpow_one_sub_le_gFun hd hs0 hsd hN1'
    have e : K ^ (1 - p) = (N : ℝ) ^ (1 - p) * β ^ (p - 1) := by
      rw [hK, Real.div_rpow hNpos.le hβ.le, div_eq_mul_inv, ← Real.rpow_neg hβ.le]
      congr 2; ring
    rw [e, mul_comm]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have hgK0 : 0 ≤ gFun d s K := by have := one_le_gFun hd hs0 hsd hK1; linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hE1' : (n : ℝ) * ∫ y, (min (lam * V.q y x) 1) ^ 2 ∂ν ≤ β * lam * Cν * Λ * c₁ * gFun d s K := by
    have h0 : (0 : ℝ) ≤ lam * Cν * Λ * c₁ * gFun d s K := by positivity
    calc (n : ℝ) * ∫ y, (min (lam * V.q y x) 1) ^ 2 ∂ν
        ≤ n * (Cν * (Λ * (lam ^ 2 * (c₁ * gFun d s K)))) := mul_le_mul_of_nonneg_left hA hn0
      _ = (n * lam) * (lam * Cν * Λ * c₁ * gFun d s K) := by ring
      _ ≤ β * (lam * Cν * Λ * c₁ * gFun d s K) := mul_le_mul_of_nonneg_right hlamn' h0
      _ = _ := by ring
  have hE1 : Real.exp mb * (n * ∫ y, (min (lam * V.q y x) 1) ^ 2 ∂ν) ≤
      Real.exp mb * (β * lam * Cν * Λ * c₁ * gFun d s K) :=
    mul_le_mul_of_nonneg_left hE1' (Real.exp_pos _).le
  have hE2 : (n : ℝ) * ∫ y, max (lam * V.q y x - 1) 0 ∂ν ≤ β * Cν * Λ * T := by
    have h0 : (0 : ℝ) ≤ Cν * Λ * T := by positivity
    calc (n : ℝ) * ∫ y, max (lam * V.q y x - 1) 0 ∂ν ≤ n * (Cν * (Λ * (lam * T))) :=
          mul_le_mul_of_nonneg_left hB hn0
      _ = (n * lam) * (Cν * Λ * T) := by ring
      _ ≤ β * (Cν * Λ * T) := mul_le_mul_of_nonneg_right hlamn' h0
      _ = _ := by ring
  have hNi : (0 : ℝ) < (N : ℝ)⁻¹ := by positivity
  have hlam' : lam = β * (N : ℝ)⁻¹ := by rw [hlam]; ring
  calc Real.exp mb * (n * ∫ y, (min (lam * V.q y x) 1) ^ 2 ∂ν) + n * ∫ y, max (lam * V.q y x - 1) 0 ∂ν
      ≤ Real.exp mb * (β * lam * Cν * Λ * c₁ * gFun d s K) + β * Cν * Λ * T := add_le_add hE1 hE2
    _ ≤ Real.exp mb * (β * lam * Cν * Λ * c₁ * (c' * gFun d s N)) +
          β * Cν * Λ * (K0 * (β ^ (p - 1) * ((N : ℝ)⁻¹ * gFun d s N)) * (p / (p - 1))) := by
        have hp1 : 0 < p - 1 := by linarith
        have hexpp : 0 < Real.exp mb := Real.exp_pos _
        have h1 : Real.exp mb * (β * lam * Cν * Λ * c₁ * gFun d s K) ≤
            Real.exp mb * (β * lam * Cν * Λ * c₁ * (c' * gFun d s N)) := by
          refine mul_le_mul_of_nonneg_left ?_ hexpp.le
          have : 0 ≤ β * lam * Cν * Λ * c₁ := by positivity
          exact mul_le_mul_of_nonneg_left hgK this
        have h2 : β * Cν * Λ * T ≤
            β * Cν * Λ * (K0 * (β ^ (p - 1) * ((N : ℝ)⁻¹ * gFun d s N)) * (p / (p - 1))) := by
          have : 0 ≤ β * Cν * Λ := by positivity
          refine mul_le_mul_of_nonneg_left ?_ this
          simp only [hT]
          have : 0 ≤ p / (p - 1) := by positivity
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKr hK0.le) this
        exact add_le_add h1 h2
    _ ≤ CDu * deltaN d s N := by
        rw [hG, hlam']
        have hI0' : 0 ≤ (N : ℝ)⁻¹ * gFun d s N := mul_nonneg hNi.le (by linarith [one_le_gFun hd hs0 hsd hN1'])
        have hA' : Real.exp mb ≤ Real.exp (βp * (Cν * (Λ * c))) :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hβpβ hmax0)
        have hB2 : β ^ 2 ≤ βp ^ 2 := by gcongr
        have hBp : β ^ (p - 1) ≤ βp ^ (p - 1) := Real.rpow_le_rpow hβ.le hβpβ (by linarith)
        have hCDle : Real.exp mb * β ^ 2 * Cν * Λ * c₁ * c' +
            β * Cν * Λ * (K0 * (p / (p - 1))) * β ^ (p - 1) ≤ CDu := by
          rw [hCDu]
          have t1 : Real.exp mb * β ^ 2 * Cν * Λ * c₁ * c' ≤
              Real.exp (βp * (Cν * (Λ * c))) * βp ^ 2 * Cν * Λ * c₁ * c' := by
            gcongr
          have t2 : β * Cν * Λ * (K0 * (p / (p - 1))) * β ^ (p - 1) ≤
              βp * Cν * Λ * (K0 * (p / (p - 1))) * βp ^ (p - 1) := by
            gcongr
          linarith
        calc _ = (Real.exp mb * β ^ 2 * Cν * Λ * c₁ * c' +
              β * Cν * Λ * (K0 * (p / (p - 1))) * β ^ (p - 1)) * ((N : ℝ)⁻¹ * gFun d s N) := by ring
          _ ≤ CDu * ((N : ℝ)⁻¹ * gFun d s N) := mul_le_mul_of_nonneg_right hCDle hI0'

set_option maxHeartbeats 1600000 in
/-- Uniform-in-`β` version of `core_L2` (`HRS/Equilibrium/ReferenceMarginal.lean:2353`). -/
theorem core_L2_unif (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {Λ : ℝ} (hΛ1 : 1 ≤ Λ)
    {βm βp : ℝ} (hβm : 0 < βm) (hββ : βm ≤ βp)
    {q gL : Torus d → ℝ} {Ψ : Torus d → EuclideanSpace ℝ (Fin M)} {c : ℝ} (hc0 : 0 ≤ c)
    (hRef : ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      RefHyp (withDensityReal ρ) q gL Ψ (Λ * c))
    (hqm : Measurable q) (hq0 : ∀ z, 0 ≤ q z) (hqe : ∀ z, q (-z) = q z) (hqi : Integrable q)
    (hqc : ∫⁻ z, ENNReal.ofReal (q z) ≤ ENNReal.ofReal c)
    {K0 : ℝ} (hK0 : 0 < K0)
    (hw : ∀ r : ℝ, 0 < r → (volume : Measure (Torus d)) {z : Torus d | r < q z} ≤
      ENNReal.ofReal (K0 * r ^ (-(pOf d s))))
    (hkm : Measurable (fun w => gL w + q w)) (hki : Integrable (fun w => gL w + q w))
    (ĝ : Lattice d → ℝ) (hĝ : ∀ n, 0 ≤ ĝ n)
    (hcoef : ∀ n, ∫ x, Torus.mode (-n) x * (((gL x + q x : ℝ)) : ℂ) = (ĝ n : ℂ))
    (hκ : ∀ β ∈ Set.Icc βm βp, KappaSmall β (Λ * c)) :
    ∃ (C : ℝ) (N₁ : ℕ), ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, IsProbDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ N : ℕ, N₁ ≤ N →
      ∀ (ht : ∀ x, |inner ℝ (tN q (withDensityReal ρ) Ψ β N) (Xi (withDensityReal ρ) Ψ x)| ≤ 1),
      firstMarginal (RN q (withDensityReal ρ) Ψ β N) ≪ withDensityReal ρ ∧
        eLpNorm (fun y => ((firstMarginal (RN q (withDensityReal ρ) Ψ β N)).rnDeriv
          (withDensityReal ρ) y).toReal - 1) 2 (withDensityReal ρ) ≤
          ENNReal.ofReal (C * deltaN d s N) := by
  set γ : ℝ := Λ * c with hγ
  have hΛ0 : 0 ≤ Λ := by linarith
  have hγ0 : 0 ≤ γ := mul_nonneg hΛ0 hc0
  have hβp0 : 0 < βp := lt_of_lt_of_le hβm hββ
  set Cνu : ℝ := Real.exp ((βp * γ + 1) + 0 + βp * γ) with hCνu
  have hCνu1 : 1 ≤ Cνu := Real.one_le_exp (by positivity)
  have hCνu0 : 0 ≤ Cνu := by linarith
  obtain ⟨CD, ND, hCD0, hD⟩ := cavD_torus_unif hd hs0 hsd hΛ1 hqm hq0 hqe hc0 hqc hK0 hw hβm hββ hCνu1
  obtain ⟨T₀, c₁, hT₀, hc₁, hconv⟩ := cv_L2_rate hd hs0 hsd hqm hq0 hK0 hw
  set κu : ℝ := 4 * Cνu * (βp * γ) with hκu
  set Eu : ℝ := Λ * (2 * (T₀ ^ 2 * (Λ * Cνu * (2 * κu)) + (2 * κu) ^ 2 * c₁)) with hEu
  have hEu0 : 0 ≤ Eu := by positivity
  set Ccvu : ℝ := Real.sqrt Eu with hCcvu
  set Cphiu : ℝ := CD + βp * Ccvu + βp * (Cνu * (Λ * c)) with hCphiu
  have hCphiu0 : 0 ≤ Cphiu := by positivity
  refine ⟨Cνu * Cphiu, max ND 2, ?_⟩
  intro β hβI ρ hρ hΛρ N hN ht
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hβpβ : β ≤ βp := hβI.2
  have hκβ : KappaSmall β γ := hκ β hβI
  set Cν : ℝ := Real.exp ((β * γ + 1) + 0 + β * γ) with hCν
  have hCν1 : 1 ≤ Cν := Real.one_le_exp (by positivity)
  have hCν0 : 0 ≤ Cν := by linarith
  set κ₀ : ℝ := 4 * Cν * (β * γ) with hκ₀
  set E : ℝ := Λ * (2 * (T₀ ^ 2 * (Λ * Cν * (2 * κ₀)) + (2 * κ₀) ^ 2 * c₁)) with hE
  have hE0 : 0 ≤ E := by positivity
  set Ccv : ℝ := Real.sqrt E with hCcv
  set Cphi : ℝ := CD + β * Ccv + β * (Cν * (Λ * c)) with hCphi
  have hCphi0 : 0 ≤ Cphi := by positivity
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  haveI : NeZero n := ⟨by omega⟩
  haveI := isProb_withDensityReal hρ
  set μ := withDensityReal ρ with hμ
  have h := hRef ρ hρ hΛρ
  set V := weakPotK h hβ.le (tN q μ Ψ β (n + 1)) ht with hV
  set lam : ℝ := β / ((n + 1 : ℕ) : ℝ) with hlam
  have hlam0 : 0 ≤ lam := div_nonneg hβ.le (Nat.cast_nonneg _)
  set θ := theta V lam n with hθdef
  have hθ0 : ∀ x, 0 < θ x := theta_pos V hlam0 n
  have hθm : Measurable θ := measurable_theta V hlam0 n
  have hθ1 : ∫ x, θ x ∂μ = 1 := integral_theta V hlam0 n
  have hθi : Integrable θ μ := integrable_theta V hlam0 n
  have hVq : ∀ x y, V.q x y = q (x - y) := fun _ _ => rfl
  have hVC : Real.exp (V.M + V.M' + β * V.γ) ≤ Cν := le_of_eq rfl
  have hVCu : Real.exp (V.M + V.M' + β * V.γ) ≤ Cνu := by
    show Real.exp ((β * γ + 1) + 0 + β * γ) ≤ Cνu
    rw [hCνu]
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_right hβpβ hγ0
    linarith
  have hκV : weakKappa V β ≤ 1 / 2 := weakKappa_weakPotK_le h hβ.le ht hκβ
  have hN0 : 0 < n + 1 := Nat.succ_pos n
  set ν := cavMarg V lam n with hν
  haveI hνp : IsProbabilityMeasure ν := by
    haveI := isProb_pinnedLaw V hlam0 n (fun e : Empty => e.elim)
    have : IsProbabilityMeasure (cavMarg V lam n) := by unfold cavMarg; infer_instance
    exact this
  have hπle : firstMarginal (RN q μ Ψ β (n + 1)) ≤ ENNReal.ofReal Cν • μ :=
    firstMarginal_RN_leK h hβ hN0 ht
  have hπeq := firstMarginal_RN_eq h hβ ht (n := n)
  rw [← hV] at hπeq
  have hνle : ν ≤ ENNReal.ofReal Cν • μ := by
    have := marginal_le_smul (B := Empty) V hβ.le hN0 (n := n) (by simp) (fun e : Empty => e.elim) 0
    exact this
  haveI : IsFiniteMeasure (firstMarginal (RN q μ Ψ β (n + 1))) :=
    ⟨lt_of_le_of_lt (hπle Set.univ) (by simp [Measure.smul_apply])⟩
  have hπ_ac := PoleCavityAux.rnDeriv_le_of_le_withDensity μ (firstMarginal (RN q μ Ψ β (n + 1)))
    (fun _ => ENNReal.ofReal Cν) (by rw [withDensity_const]; exact hπle)
  have hrn : (firstMarginal (RN q μ Ψ β (n + 1))).rnDeriv μ =ᵐ[μ] fun y => ENNReal.ofReal (θ y) := by
    rw [hπeq]; exact Measure.rnDeriv_withDensity μ (ENNReal.measurable_ofReal.comp hθm)
  have hθC : ∀ᵐ y ∂μ, θ y ≤ Cν := by
    filter_upwards [hrn, hπ_ac.2] with y h1 h2
    rw [h1] at h2
    exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 h2
  refine ⟨hπ_ac.1, ?_⟩
  have hfin : (fun y => ((firstMarginal (RN q μ Ψ β (n + 1))).rnDeriv μ y).toReal - 1) =ᵐ[μ]
      fun y => θ y - 1 := by
    filter_upwards [hrn] with y h1
    rw [h1, ENNReal.toReal_ofReal (hθ0 y).le]
  rw [eLpNorm_congr_ae hfin]
  have hCz : ∀ᵐ y ∂μ, |θ y - 1| ≤ Cν := hθC.mono fun y hy => by
    rw [abs_le]; constructor <;> linarith [hθ0 y]
  obtain ⟨c', hc'⟩ := cavity_equation h hβ ht (n := n) (Cz := Cν) hCz
  -- clipped densities
  have hCν0' : 0 ≤ Cν := hCν0
  set θc : Torus d → ℝ := fun y => min (θ y) Cν with hθc
  have hθcm : Measurable θc := hθm.min measurable_const
  have hθc0 : ∀ y, 0 ≤ θc y := fun y => le_min (hθ0 y).le hCν0
  have hθcb : ∀ y, θc y ≤ Cν := fun y => min_le_right _ _
  have hθc_ae : ∀ᵐ y ∂μ, θc y = θ y := hθC.mono fun y hy => min_eq_left hy
  have hνac : ν ≪ μ := Measure.absolutelyContinuous_of_le_smul hνle
  haveI : IsFiniteMeasure ν := inferInstance
  have hν_rn := PoleCavityAux.rnDeriv_le_of_le_withDensity μ ν (fun _ => ENNReal.ofReal Cν)
    (by rw [withDensity_const]; exact hνle)
  set θ' : Torus d → ℝ := fun y => (ν.rnDeriv μ y).toReal with hθ'
  set θ'c : Torus d → ℝ := fun y => min (θ' y) Cν with hθ'c
  have hθ'm : Measurable θ' := (Measure.measurable_rnDeriv ν μ).ennreal_toReal
  have hθ'cm : Measurable θ'c := hθ'm.min measurable_const
  have hθ'c0 : ∀ y, 0 ≤ θ'c y := fun y => le_min ENNReal.toReal_nonneg hCν0
  have hθ'cb : ∀ y, θ'c y ≤ Cν := fun y => min_le_right _ _
  have hνeq : ν = μ.withDensity (fun y => ENNReal.ofReal (θ'c y)) := by
    calc ν = μ.withDensity (ν.rnDeriv μ) := (Measure.withDensity_rnDeriv_eq ν μ hνac).symm
      _ = _ := by
        refine withDensity_congr_ae ?_
        filter_upwards [Measure.rnDeriv_lt_top ν μ, hν_rn.2] with y h1 h2
        have h3 : (ν.rnDeriv μ y).toReal ≤ Cν := ENNReal.toReal_le_of_le_ofReal hCν0 h2
        simp only [hθ'c, hθ', min_eq_left h3, ENNReal.ofReal_toReal h1.ne]
  have hπeq' : firstMarginal (RN q μ Ψ β (n + 1)) = μ.withDensity (fun y => ENNReal.ofReal (θc y)) := by
    rw [hπeq]
    refine withDensity_congr_ae ?_
    filter_upwards [hθc_ae] with y hy
    rw [hy]
  have hθci : Integrable θc μ := Integrable.of_bound hθcm.aestronglyMeasurable Cν
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (hθc0 y)]; exact hθcb y)
  have hθ'ci : Integrable θ'c μ := Integrable.of_bound hθ'cm.aestronglyMeasurable Cν
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (hθ'c0 y)]; exact hθ'cb y)
  have hTV : ∫ y, |θc y - θ'c y| ∂μ ≤ 2 * (weakKappa V β / ((n + 1 : ℕ) : ℝ)) := by
    refine integral_abs_sub_le hθcm hθ'cm hθc0 hθ'c0 hθci hθ'ci (fun A hA => ?_)
    rw [← hπeq', ← hνeq]
    exact event_pi_nu h hβ ht hκV hA
  -- the convolution term
  set w : Torus d → ℝ := fun y => ρ y * (θc y - θ'c y) with hw
  have hcvid : ∀ x, (∫ y, q (x - y) * θ y ∂μ) - ∫ y, q (x - y) ∂ν = ResponseAux.cv q w x := by
    intro x
    have e1 : ∫ y, q (x - y) * θ y ∂μ = ∫ y, q (x - y) * θc y ∂μ :=
      integral_congr_ae (hθc_ae.mono fun y hy => by show q (x - y) * θ y = q (x - y) * θc y; rw [hy])
    rw [e1]
    have := cv_identity hρ hΛρ hqm hq0 hqi hθcm hθ'cm hθc0 hθ'c0 hθcb hθ'cb x
    rw [← hνeq] at this
    exact this
  set Dfun : Torus d → ℝ := fun x => Real.log (cavU V lam n (fun e : Empty => e.elim) x) +
    lam * n * ∫ y, V.q y x ∂ν with hDfun
  set Qν : Torus d → ℝ := fun x => ∫ y, q (x - y) ∂ν with hQν
  set Φ : Torus d → ℝ := fun x => Dfun x + β * ResponseAux.cv q w x + lam * Qν x with hΦ
  have heq : ∀ x, Real.log (θ x) + β * ResponseAux.Kt (fun w => gL w + q w) μ (fun y => θ y - 1) x =
      Φ x + c' := by
    intro x
    rw [hc' x]
    simp only [hΦ, hDfun, hQν]
    rw [← hcvid x]
  -- the rate `δ = N⁻¹ g(N)`
  set N : ℝ := ((n + 1 : ℕ) : ℝ) with hNdef
  have hN2 : (2 : ℝ) ≤ N := by
    have : 2 ≤ n + 1 := by omega
    show (2 : ℝ) ≤ ((n + 1 : ℕ) : ℝ)
    exact_mod_cast this
  have hNpos : 0 < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hδ : deltaN d s (n + 1) = N⁻¹ * gFun d s N := deltaN_eq_gFun hd hs0 hsd (by omega)
  have hg1 : 1 ≤ gFun d s N := one_le_gFun hd hs0 hsd hN1
  set δ : ℝ := deltaN d s (n + 1) with hδdef
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hδ1 : N⁻¹ ≤ δ := by
    rw [hδ]
    calc N⁻¹ = N⁻¹ * 1 := (mul_one _).symm
      _ ≤ N⁻¹ * gFun d s N := by gcongr
  have hlam_le : lam ≤ β * δ := by
    have : lam = β * N⁻¹ := by rw [hlam]; ring
    rw [this]; gcongr
  -- the cavity correction `D`
  have hDb : ∀ x, 0 ≤ Dfun x ∧ Dfun x ≤ CD * δ := fun x =>
    hD β hβI ρ hρ hΛρ V hVq hVCu hκV (n + 1) n (by omega) (Nat.le_succ n) x
  have hDm : Measurable Dfun := by
    refine ((Real.measurable_log.comp (measurable_cavU V hlam0 n _)).add (measurable_const.mul ?_))
    exact measurable_integral_kernel (F := fun p : Torus d × Torus d => V.q p.2 p.1)
      (V.measurable_q.comp (measurable_snd.prodMk measurable_fst))
  have hDL2 : eLpNorm Dfun 2 μ ≤ ENNReal.ofReal (CD * δ) :=
    eLpNorm_two_le_const hDm.aestronglyMeasurable fun x => by
      rw [abs_of_nonneg (hDb x).1]; exact (hDb x).2
  -- the convolution term
  have hwm : Measurable w := hρ.measurable.mul (hθcm.sub hθ'cm)
  have hcvm : Measurable (ResponseAux.cv q w) := by
    unfold ResponseAux.cv
    exact measurable_integral_kernel (F := fun p : Torus d × Torus d => q (p.1 - p.2) * w p.2)
      ((hqm.comp (measurable_fst.sub measurable_snd)).mul (hwm.comp measurable_snd))
  have hκ0 : 0 ≤ weakKappa V β := weakKappa_nonneg V hβ.le
  have hκeq : weakKappa V β = κ₀ := rfl
  set η : ℝ := 2 * (weakKappa V β / N) with hη
  have hη0 : 0 ≤ η := by positivity
  have hb : ∀ y, |θc y - θ'c y| ≤ Cν := fun y => by
    rw [abs_le]; constructor <;> linarith [hθc0 y, hθ'c0 y, hθcb y, hθ'cb y]
  have h1 := hconv ρ hρ hΛρ hΛ0 hθcm hθ'cm hCν0 hb hη0 hTV (N := n + 1) (by omega)
  have hE' : Λ * (2 * ((T₀ * (N⁻¹ * gFun d s N)) ^ 2 * (Λ * Cν * η) + η ^ 2 * (c₁ * gFun d s N))) ≤
      E * δ ^ 2 := by
    have ha0 : 0 < N⁻¹ := inv_pos.2 hNpos
    have ha1 : N⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN1
    set a : ℝ := N⁻¹ with ha
    set g : ℝ := gFun d s N with hg
    have hηa : η = 2 * κ₀ * a := by rw [hη, hκeq, div_eq_mul_inv]; ring
    have hX : δ ^ 2 = (a * g) ^ 2 := by rw [hδ]
    have hX0 : 0 ≤ (a * g) ^ 2 := sq_nonneg _
    have t1 : (T₀ * (a * g)) ^ 2 * (Λ * Cν * η) ≤ T₀ ^ 2 * (Λ * Cν * (2 * κ₀)) * (a * g) ^ 2 := by
      rw [hηa]
      have : (T₀ * (a * g)) ^ 2 * (Λ * Cν * (2 * κ₀ * a)) =
          (T₀ ^ 2 * (Λ * Cν * (2 * κ₀)) * (a * g) ^ 2) * a := by ring
      rw [this]
      have hnn : 0 ≤ T₀ ^ 2 * (Λ * Cν * (2 * κ₀)) * (a * g) ^ 2 := by positivity
      calc (T₀ ^ 2 * (Λ * Cν * (2 * κ₀)) * (a * g) ^ 2) * a ≤ (T₀ ^ 2 * (Λ * Cν * (2 * κ₀)) * (a * g) ^ 2) * 1 :=
            mul_le_mul_of_nonneg_left ha1 hnn
        _ = _ := mul_one _
    have t2 : η ^ 2 * (c₁ * g) ≤ (2 * κ₀) ^ 2 * c₁ * (a * g) ^ 2 := by
      rw [hηa]
      have : (2 * κ₀ * a) ^ 2 * (c₁ * g) = ((2 * κ₀) ^ 2 * c₁ * (a ^ 2 * g)) := by ring
      rw [this]
      have : (2 * κ₀) ^ 2 * c₁ * (a * g) ^ 2 = ((2 * κ₀) ^ 2 * c₁ * (a ^ 2 * g)) * g := by ring
      rw [this]
      have hnn : 0 ≤ (2 * κ₀) ^ 2 * c₁ * (a ^ 2 * g) := by positivity
      calc (2 * κ₀) ^ 2 * c₁ * (a ^ 2 * g) = ((2 * κ₀) ^ 2 * c₁ * (a ^ 2 * g)) * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hg1 hnn
    rw [hX]
    calc Λ * (2 * ((T₀ * (a * g)) ^ 2 * (Λ * Cν * η) + η ^ 2 * (c₁ * g)))
        ≤ Λ * (2 * (T₀ ^ 2 * (Λ * Cν * (2 * κ₀)) * (a * g) ^ 2 + (2 * κ₀) ^ 2 * c₁ * (a * g) ^ 2)) := by
          gcongr
      _ = E * (a * g) ^ 2 := by rw [hE]; ring
  have hAE : AEStronglyMeasurable (ResponseAux.cv q w) μ := hcvm.aestronglyMeasurable
  have hsq : (eLpNorm (ResponseAux.cv q w) 2 μ) ^ 2 ≤ ENNReal.ofReal (Ccv * δ) ^ 2 := by
    rw [ResponseAux.eLpNorm_two_sq hAE, ← ENNReal.ofReal_pow (by positivity), mul_pow, hCcv,
      Real.sq_sqrt hE0]
    exact h1.trans (ENNReal.ofReal_le_ofReal hE')
  have hcvL2 : eLpNorm (ResponseAux.cv q w) 2 μ ≤ ENNReal.ofReal (Ccv * δ) :=
    (ENNReal.pow_le_pow_left_iff two_ne_zero).1 hsq
  -- the `λ q*ν` term
  have hQνm : Measurable Qν := measurable_integral_kernel (F := fun p : Torus d × Torus d => q (p.1 - p.2))
    (hqm.comp (measurable_fst.sub measurable_snd))
  have hQb : ∀ x, 0 ≤ Qν x ∧ Qν x ≤ Cν * (Λ * c) := fun x =>
    ⟨integral_nonneg fun y => hq0 _, integral_kernel_le hΛρ hΛ0 hνle hCν0 hqm hq0 hc0 hqc x⟩
  have hQL2 : eLpNorm (fun x => lam * Qν x) 2 μ ≤ ENNReal.ofReal (β * (Cν * (Λ * c)) * δ) :=
    eLpNorm_two_le_const (hQνm.const_mul lam).aestronglyMeasurable fun x => by
      rw [abs_of_nonneg (mul_nonneg hlam0 (hQb x).1)]
      calc lam * Qν x ≤ (β * δ) * (Cν * (Λ * c)) :=
            mul_le_mul hlam_le (hQb x).2 (hQb x).1 (by positivity)
        _ = _ := by ring
  -- Minkowski
  have hΦe : Φ = (Dfun + fun x => β * ResponseAux.cv q w x) + fun x => lam * Qν x := by
    funext x; simp [hΦ]
  have hΦnorm : eLpNorm Φ 2 μ ≤ ENNReal.ofReal (Cphi * δ) := by
    have m1 : AEStronglyMeasurable Dfun μ := hDm.aestronglyMeasurable
    have m2 : AEStronglyMeasurable (fun x => β * ResponseAux.cv q w x) μ :=
      (hcvm.const_mul β).aestronglyMeasurable
    have m3 : AEStronglyMeasurable (fun x => lam * Qν x) μ := (hQνm.const_mul lam).aestronglyMeasurable
    have e2 : eLpNorm (fun x => β * ResponseAux.cv q w x) 2 μ =
        ENNReal.ofReal β * eLpNorm (ResponseAux.cv q w) 2 μ := by
      have := eLpNorm_const_smul (p := 2) (μ := μ) β (ResponseAux.cv q w)
      rw [show (fun x => β * ResponseAux.cv q w x) = β • ResponseAux.cv q w from rfl, this,
        Real.enorm_of_nonneg hβ.le]
    rw [hΦe]
    refine (eLpNorm_add_le (by norm_num)).trans ?_
    refine (add_le_add_left (eLpNorm_add_le (by norm_num)) _).trans ?_
    rw [e2]
    calc eLpNorm Dfun 2 μ + ENNReal.ofReal β * eLpNorm (ResponseAux.cv q w) 2 μ +
          eLpNorm (fun x => lam * Qν x) 2 μ
        ≤ ENNReal.ofReal (CD * δ) + ENNReal.ofReal β * ENNReal.ofReal (Ccv * δ) +
          ENNReal.ofReal (β * (Cν * (Λ * c)) * δ) := by gcongr
      _ = ENNReal.ofReal (Cphi * δ) := by
          rw [← ENNReal.ofReal_mul hβ.le, ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          rw [hCphi]; ring
  have hΦm : Measurable Φ := (hDm.add (hcvm.const_mul β)).add (hQνm.const_mul lam)
  have hΦmem : MemLp Φ 2 μ := lt_of_le_of_lt hΦnorm ENNReal.ofReal_lt_top
  -- absorption
  have habs := absorption hρ hΛρ hkm hki ĝ hĝ hcoef hβ.le hθm hθ0 hCν1 hθC hθ1 hΦmem heq
  -- comparison of the constants with their values at `βp`
  have hCν_le : Cν ≤ Cνu := by
    rw [hCν, hCνu]
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_right hβpβ hγ0
    linarith
  have hκ_le : κ₀ ≤ κu := by
    rw [hκ₀, hκu]
    gcongr
  have hE_le : E ≤ Eu := by
    rw [hE, hEu]
    gcongr
  have hCcv0 : 0 ≤ Ccv := Real.sqrt_nonneg _
  have hCcv_le : Ccv ≤ Ccvu := Real.sqrt_le_sqrt hE_le
  have hCphi_le : Cphi ≤ Cphiu := by
    rw [hCphi, hCphiu]
    gcongr
  have hC : Cν * Cphi ≤ Cνu * Cphiu := mul_le_mul hCν_le hCphi_le hCphi0 hCνu0
  refine habs.trans ?_
  calc ENNReal.ofReal Cν * eLpNorm Φ 2 μ ≤ ENNReal.ofReal Cν * ENNReal.ofReal (Cphi * δ) := by gcongr
    _ = ENNReal.ofReal (Cν * Cphi * δ) := by
        rw [← ENNReal.ofReal_mul hCν0]; congr 1; ring
    _ ≤ ENNReal.ofReal (Cνu * Cphiu * δ) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC hδ0)

end HRS.ME.NfU

end
