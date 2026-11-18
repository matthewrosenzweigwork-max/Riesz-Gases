import HRS.Equilibrium.ReferenceMarginal
import HRS.Equilibrium.ReferenceGlue

/-!
# EQ-STATIC-U, part 3: the reference marginal in `L²`, uniform in `β ∈ [β₋,β₊]`

`HRS.External.RefMarg.reference_marginal_density_L2` (Proposition 4.2, reference part) with the constants chosen before
`β ∈ [β₋,β₊]`: `cavD_torus`, `core_L2` are re-run with every `β`-dependent constant replaced by its monotone bound
at `β₊` (and `1/β` by `1/β₋` in the scale lemma `gFun_mul_le`).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.MD.EQStat

open HRS HRS.External HRS.External.RefMarg HRS.External.Calib

/-- `gFun` is monotone on `[1,∞)`. -/
theorem eqstat_gFun_mono {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {K K' : ℝ}
    (hK : 1 ≤ K) (hKK' : K ≤ K') : gFun d s K ≤ gFun d s K' := by
  unfold gFun
  have hK0 : 0 < K := by linarith
  split_ifs with h1 h2
  · exact le_rfl
  · refine Real.log_le_log (by positivity) ?_
    exact mul_le_mul_of_nonneg_left hKK' (Real.exp_pos 1).le
  · have h3 : (d : ℝ) / 2 < s := lt_of_le_of_ne (not_lt.1 h1) (Ne.symm h2)
    have hs : 0 < s := by
      have : (0 : ℝ) < d / 2 := by
        have : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
        positivity
      linarith
    exact Real.rpow_le_rpow hK0.le hKK' (by rw [sub_nonneg, div_le_iff₀ hs]; linarith)

/-- `KappaSmall` is monotone in `β` (for `γ ≥ 0`). -/
theorem eqstat_kappaSmall_mono {β β' γ : ℝ} (hβ : 0 ≤ β) (hββ : β ≤ β') (hγ : 0 ≤ γ)
    (h : KappaSmall β' γ) : KappaSmall β γ := by
  unfold KappaSmall at *
  have h1 : β * γ ≤ β' * γ := mul_le_mul_of_nonneg_right hββ hγ
  have h0 : 0 ≤ β * γ := mul_nonneg hβ hγ
  have h2 : Real.exp (2 * (β * γ) + 1) ≤ Real.exp (2 * (β' * γ) + 1) := Real.exp_le_exp.2 (by linarith)
  calc 4 * Real.exp (2 * (β * γ) + 1) * (β * γ) ≤ 4 * Real.exp (2 * (β' * γ) + 1) * (β' * γ) := by
        gcongr
    _ ≤ 1 / 2 := h

variable {d : ℕ}

theorem eqstat_cavD_torus (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    {Λ : ℝ} (hΛ1 : 1 ≤ Λ)
    {q : Torus d → ℝ} (hqm : Measurable q) (hq0 : ∀ z, 0 ≤ q z) (hqe : ∀ z, q (-z) = q z)
    {c : ℝ} (hc0 : 0 ≤ c) (hqc : ∫⁻ z, ENNReal.ofReal (q z) ≤ ENNReal.ofReal c)
    {K0 : ℝ} (hK0 : 0 < K0)
    (hw : ∀ r : ℝ, 0 < r → (volume : Measure (Torus d)) {z : Torus d | r < q z} ≤
      ENNReal.ofReal (K0 * r ^ (-(pOf d s))))
    {βm βp : ℝ} (hβm : 0 < βm) (hββ : βm ≤ βp) {Cν : ℝ} (hCν : 1 ≤ Cν)  :
    ∃ (CD : ℝ) (N₁ : ℕ), 0 ≤ CD ∧ ∀ {β : ℝ}, βm ≤ β → β ≤ βp → ∀ (ρ : Torus d → ℝ), IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ (V : WeakPotential (withDensityReal ρ)),
      (∀ x y, V.q x y = q (x - y)) → Real.exp (V.M + V.M' + β * V.γ) ≤ Cν → weakKappa V β ≤ 1 / 2 →
      ∀ (N n : ℕ) [NeZero n], N₁ ≤ N → n ≤ N → ∀ x : Torus d,
        0 ≤ Real.log (cavU V (β / N) n (fun e : Empty => e.elim) x) +
          β / N * n * ∫ y, V.q y x ∂(cavMarg V (β / N) n) ∧
        Real.log (cavU V (β / N) n (fun e : Empty => e.elim) x) +
          β / N * n * ∫ y, V.q y x ∂(cavMarg V (β / N) n) ≤ CD * deltaN d s N := by
  have hp := one_lt_pOf hd hs0 hsd
  set p := pOf d s with hpdef
  obtain ⟨c₁, hc₁, hR2⟩ := second_moment_gFun hd hs0 hsd hK0
  have hβp : 0 < βp := lt_of_lt_of_le hβm hββ
  obtain ⟨c', hc', hscale⟩ := gFun_mul_le hd hs0 hsd (c := 1 / βm) (by positivity)
  have hΛ0 : 0 ≤ Λ := by linarith
  set mb : ℝ := βp * (Cν * (Λ * c)) with hmb
  set CD : ℝ := Real.exp mb * βp ^ 2 * Cν * Λ * c₁ * c' +
      βp * Cν * Λ * (K0 * (p / (p - 1))) * βp ^ (p - 1) with hCD
  refine ⟨CD, ⌈βp⌉₊ + 1, by positivity, ?_⟩
  intro β hβ1 hβ2 ρ hρ hΛ V hVq hVC hκ N n _ hN hn x
  have hβ : 0 < β := lt_of_lt_of_le hβm hβ1
  haveI := isProb_withDensityReal hρ
  have hNβp : βp ≤ N := by
    have : (⌈βp⌉₊ : ℝ) + 1 ≤ N := by exact_mod_cast hN
    linarith [Nat.le_ceil βp]
  have hNβ : β ≤ N := hβ2.trans hNβp
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
  have hCν0 : 0 ≤ Cν := by linarith
  have hI1 : ∫ y, V.q y x ∂(cavMarg V lam n) ≤ Cν * (Λ * c) := by
    simp_rw [hVqx]
    exact integral_kernel_le hΛ hΛ0 hν hCν0 hqm hq0 hc0 hqc x
  have hI0 : 0 ≤ ∫ y, V.q y x ∂(cavMarg V lam n) := integral_nonneg fun y => V.q_nonneg _ _
  have hlamn : lam * n ≤ β := by
    have : (n : ℝ) ≤ N := by exact_mod_cast hn
    calc lam * n ≤ lam * N := by gcongr
      _ = β := by rw [hlam]; field_simp
  have hlamn' : (n : ℝ) * lam ≤ β := by linarith [hlamn, mul_comm (n : ℝ) lam]
  have hm : lam * n * ∫ y, V.q y x ∂(cavMarg V lam n) ≤ mb := by
    calc lam * n * ∫ y, V.q y x ∂(cavMarg V lam n) ≤ β * ∫ y, V.q y x ∂(cavMarg V lam n) := by gcongr
      _ ≤ β * (Cν * (Λ * c)) := by gcongr
      _ ≤ βp * (Cν * (Λ * c)) := by gcongr
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
  have hgN1 := one_le_gFun hd hs0 hsd hN1'
  have hgK : gFun d s K ≤ c' * gFun d s N := by
    have hK' : K = 1 / β * N := by rw [hK]; field_simp
    have hKle : K ≤ 1 / βm * N := by
      rw [hK']; exact mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le hβm hβ1) hNpos.le
    have h1m : 1 ≤ 1 / βm * N := by
      rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hβm]; linarith
    exact (eqstat_gFun_mono hd hs0 hsd hK1 hKle).trans (hscale N hN1' h1m)
  have hKr : K ^ (1 - p) ≤ βp ^ (p - 1) * ((N : ℝ)⁻¹ * gFun d s N) := by
    have h1 := rpow_one_sub_le_gFun hd hs0 hsd hN1'
    have e : K ^ (1 - p) = (N : ℝ) ^ (1 - p) * β ^ (p - 1) := by
      rw [hK, Real.div_rpow hNpos.le hβ.le, div_eq_mul_inv, ← Real.rpow_neg hβ.le]
      congr 2; ring
    have hβpow : β ^ (p - 1) ≤ βp ^ (p - 1) := Real.rpow_le_rpow hβ.le hβ2 (by linarith)
    rw [e]
    calc (N : ℝ) ^ (1 - p) * β ^ (p - 1) ≤ ((N : ℝ)⁻¹ * gFun d s N) * βp ^ (p - 1) :=
          mul_le_mul h1 hβpow (Real.rpow_nonneg hβ.le _) (mul_nonneg (by positivity) (by linarith))
      _ = _ := by ring
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
  have hβl : β * lam ≤ βp * (βp * (N : ℝ)⁻¹) := by
    rw [hlam']
    exact mul_le_mul hβ2 (mul_le_mul_of_nonneg_right hβ2 hNi.le) (by positivity) hβp.le
  have hp1 : 0 < p - 1 := by linarith
  have hexpp : 0 < Real.exp mb := Real.exp_pos _
  calc Real.exp mb * (n * ∫ y, (min (lam * V.q y x) 1) ^ 2 ∂ν) + n * ∫ y, max (lam * V.q y x - 1) 0 ∂ν
      ≤ Real.exp mb * (β * lam * Cν * Λ * c₁ * gFun d s K) + β * Cν * Λ * T := add_le_add hE1 hE2
    _ ≤ Real.exp mb * (βp * (βp * (N : ℝ)⁻¹) * Cν * Λ * c₁ * (c' * gFun d s N)) +
          βp * Cν * Λ * (K0 * (βp ^ (p - 1) * ((N : ℝ)⁻¹ * gFun d s N)) * (p / (p - 1))) := by
        have h1 : Real.exp mb * (β * lam * Cν * Λ * c₁ * gFun d s K) ≤
            Real.exp mb * (βp * (βp * (N : ℝ)⁻¹) * Cν * Λ * c₁ * (c' * gFun d s N)) := by
          refine mul_le_mul_of_nonneg_left ?_ hexpp.le
          have h3 : β * lam * Cν * Λ * c₁ ≤ βp * (βp * (N : ℝ)⁻¹) * Cν * Λ * c₁ := by gcongr
          have h4 : 0 ≤ βp * (βp * (N : ℝ)⁻¹) * Cν * Λ * c₁ := by positivity
          calc β * lam * Cν * Λ * c₁ * gFun d s K ≤ (βp * (βp * (N : ℝ)⁻¹) * Cν * Λ * c₁) * gFun d s K :=
                mul_le_mul_of_nonneg_right h3 hgK0
            _ ≤ (βp * (βp * (N : ℝ)⁻¹) * Cν * Λ * c₁) * (c' * gFun d s N) :=
                mul_le_mul_of_nonneg_left hgK h4
            _ = _ := by ring
        have h2 : β * Cν * Λ * T ≤
            βp * Cν * Λ * (K0 * (βp ^ (p - 1) * ((N : ℝ)⁻¹ * gFun d s N)) * (p / (p - 1))) := by
          have h5 : β * Cν * Λ ≤ βp * Cν * Λ := by gcongr
          have h6 : T ≤ K0 * (βp ^ (p - 1) * ((N : ℝ)⁻¹ * gFun d s N)) * (p / (p - 1)) := by
            simp only [hT]
            have : 0 ≤ p / (p - 1) := by positivity
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKr hK0.le) this
          exact mul_le_mul h5 h6 hT0 (by positivity)
        exact add_le_add h1 h2
    _ = CD * deltaN d s N := by
        rw [hG, hCD]
        ring

end HRS.MD.EQStat

end
