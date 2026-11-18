import HRS.Equilibrium.QuadraticVariance

/-!
# EQ-STATIC-U, part 2: the crude second-moment bound of the weak ensemble, uniform in `β ∈ [β₋,β₊]`

`HRS.Quad.quad_crude_weak` with the constant chosen before `β ∈ [β₋,β₊]` and before `ρ ≤ Λ` (the particle number `n`
is fixed first, as in the original): `K = 1 + 2/λ` is replaced by `K = 1 + 2(n+1)/β₋` and `β` by `β₊` in `M0`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.MD.EQStat

open HRS HRS.Quad HRS.External HRS.External.RefMarg HRS.External.PoleVar

variable {d : ℕ} {s : ℝ}


set_option maxHeartbeats 800000 in
/-- **Crude bound** (fixed `n`, no smallness), uniform in `β ∈ [β₋,β₊]` and `ρ ≤ Λ`:
`E_R |D_N(h;ν)|² ≤ C (1 + Cp²) B²`. -/
theorem eqstat_quad_crude_weak (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {βm βp : ℝ} (hβm : 0 < βm)
    (hββ : βm ≤ βp) {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (Mmax M'max γmax Cq : ℝ)
    (hCq : 0 ≤ Cq) {n : ℕ} (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ {β : ℝ}, βm ≤ β → β ≤ βp → ∀ (ρ : Torus d → ℝ), IsProbDensity ρ → (∀ y, ρ y ≤ Λ) →
      ∀ (V : WeakPotential (withDensityReal ρ)), V.M ≤ Mmax → V.M' ≤ M'max → V.γ ≤ γmax →
      (∀ x y : Torus d, x ≠ y → envT s (x - y) - Cq ≤ V.q x y) →
      ∀ (B : ℝ), 0 ≤ B → ∀ (h : Torus d → Torus d → ℝ), Measurable (Function.uncurry h) →
      (∀ x y, x ≠ y → |h x y| ≤ B * singEnvelope s (Torus.eucDist x y)) →
      ∀ {Cp : ℝ}, 0 ≤ Cp → ∀ (ν : Measure (Torus d)) [IsProbabilityMeasure ν],
      ν ≤ ENNReal.ofReal Cp • withDensityReal ρ →
      ∫⁻ Y, ‖quadStat h ν Y‖ₑ ^ 2 ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim))
        ≤ ENNReal.ofReal (C * (1 + Cp ^ 2) * B ^ 2) := by
  have hβp : 0 < βp := lt_of_lt_of_le hβm hββ
  obtain ⟨cH, hcH, hHc⟩ := Hc_bound hd hs0 hsd
  obtain ⟨c₁, hc₁, hvar⟩ := variance_integral_le hd hs0 hsd
  have hN0 : 0 < n + 1 := Nat.succ_pos n
  have hNR : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hN0
  have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by linarith
  set K : ℝ := 1 + 2 * ((n + 1 : ℕ) : ℝ) / βm with hK
  have hK1 : 1 ≤ K := by
    rw [hK]; have : 0 ≤ 2 * ((n + 1 : ℕ) : ℝ) / βm := by positivity
    linarith
  set γ' : ℝ := max γmax 0 with hγ'
  set M0 : ℝ := Mmax + M'max + βp * γ' + βp * Cq with hM0
  set Wc : ℝ := c₁ * Λ * Real.exp M0 * gFun d s K with hWc
  have hg1 : 1 ≤ gFun d s K := one_le_gFun hd hs0 hsd hK1
  have hWc0 : 0 ≤ Wc := by rw [hWc]; positivity
  refine ⟨3 * Wc + 15 * (cH * Λ) ^ 2 + 1, by positivity, ?_⟩
  intro β hβ1 hβ2 ρ hρ hΛ V hVM hVM' hVγ hq B hB h hm hh Cp hCp ν _ hν
  have hβ : 0 < β := lt_of_lt_of_le hβm hβ1
  haveI hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ
  set lam : ℝ := β / ((n + 1 : ℕ) : ℝ) with hlam
  have hlam0 : 0 < lam := by positivity
  have hlamβ : lam ≤ β := by rw [hlam, div_le_iff₀ hNpos]; nlinarith
  have hK2 : 2 / lam ≤ K := by
    have h1 : 2 / lam = 2 * ((n + 1 : ℕ) : ℝ) / β := by rw [hlam]; field_simp
    rw [h1, hK]
    have h2 : 2 * ((n + 1 : ℕ) : ℝ) / β ≤ 2 * ((n + 1 : ℕ) : ℝ) / βm :=
      div_le_div_of_nonneg_left (by positivity) hβm hβ1
    linarith
  have hγ'0 : 0 ≤ γ' := le_max_right _ _
  have hβγ : β * V.γ ≤ βp * γ' :=
    (mul_le_mul_of_nonneg_left (hVγ.trans (le_max_left _ _)) hβ.le).trans
      (mul_le_mul_of_nonneg_right hβ2 hγ'0)
  set P0 := pinnedLaw V lam (n + 1) (fun e : Empty => e.elim) with hP0
  haveI hRp : IsProbabilityMeasure P0 := isProb_pinnedLaw V hlam0.le (n + 1) _
  -- pair bound
  have hpair : ∀ a b : Fin (n + 1), a ≠ b → ∫⁻ Y, ‖h ((Y : Config d (n + 1)) a) (Y b)‖ₑ ^ 2 ∂P0 ≤ ENNReal.ofReal (Wc * B ^ 2) := by
    intro a b hab
    refine pair_lintegral_le V hβ.le a b hab hm (fun x => ?_)
    have h1 := hvar hΛ hΛ0 (b := B) hB (x := x) (lam := lam) (K := K) (M0 := M0) hlam0 hK1 hK2
      (f := h x) (ψ := fun y => V.M' + β * V.γ + pinField V lam (pinsWith (fun e : Empty => e.elim) x) y)
      (fun y hy => by
        have := hh x y (Ne.symm hy)
        rwa [eucDist_sub] at this) (fun y hy => by
        rw [pinField_pinsWith, pinField_empty]
        have h2 := V.φ_le y
        have h3 := hq y x hy
        rw [envT_sub_comm y x] at h3
        have h4 := hβγ
        have h5 : lam * Cq ≤ βp * Cq := mul_le_mul_of_nonneg_right (hlamβ.trans hβ2) hCq
        have h6 : lam * (envT s (x - y) - Cq) ≤ lam * V.q y x := mul_le_mul_of_nonneg_left h3 hlam0.le
        rw [hM0]
        nlinarith)
    refine h1.trans (le_of_eq ?_)
    rw [hWc]; congr 1; ring
  -- the one-point function
  have hH' : ∀ x, |Hc h ν x| ≤ cH * Cp * Λ * B := fun x => hHc hΛ hΛ0 hν hCp hB hh x
  set H' : ℝ := cH * Cp * Λ * B with hH'def
  have hNn : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by linarith
  have hc3 : (0 : ℝ) ≤ 3 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by positivity
  have hmeas : ∀ i j : Fin (n + 1), Measurable fun Y : Config d (n + 1) => ‖h (Y i) (Y j)‖ₑ ^ 2 :=
    fun i j => ((measurable_h_pair hm i j).enorm).pow_const 2
  have hpt : ∀ Y : Config d (n + 1), ‖quadStat h ν Y‖ₑ ^ 2 ≤
      ∑ i, ∑ j ∈ Finset.univ.erase i, ENNReal.ofReal (3 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) * ‖h (Y i) (Y j)‖ₑ ^ 2
        + ENNReal.ofReal (15 * H' ^ 2) := by
    intro Y
    have h1 := quadStat_sq_le hN0 h ν hH' Y
    have e1 : ‖quadStat h ν Y‖ₑ ^ 2 = ENNReal.ofReal (quadStat h ν Y ^ 2) := by
      rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
    have e2 : ∀ i j : Fin (n + 1), ‖h (Y i) (Y j)‖ₑ ^ 2 = ENNReal.ofReal (h (Y i) (Y j) ^ 2) := fun i j => by
      rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
    rw [e1]
    simp_rw [e2]
    refine (ENNReal.ofReal_le_ofReal h1).trans ?_
    rw [ENNReal.ofReal_add (by positivity) (by positivity), Finset.mul_sum]
    refine add_le_add (le_of_eq ?_) le_rfl
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ENNReal.ofReal_mul hc3]
  have hF : Measurable fun Y : Config d (n + 1) => ‖quadStat h ν Y‖ₑ ^ 2 :=
    ((measurable_quadStat hm ν).enorm).pow_const 2
  calc ∫⁻ Y, ‖quadStat h ν Y‖ₑ ^ 2 ∂P0
      ≤ ∫⁻ Y, (∑ i, ∑ j ∈ Finset.univ.erase i, ENNReal.ofReal (3 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) *
          ‖h (Y i) (Y j)‖ₑ ^ 2 + ENNReal.ofReal (15 * H' ^ 2)) ∂P0 := lintegral_mono hpt
    _ = (∑ i, ∑ j ∈ Finset.univ.erase i, ENNReal.ofReal (3 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) *
          ∫⁻ Y, ‖h (Y i) (Y j)‖ₑ ^ 2 ∂P0) + ENNReal.ofReal (15 * H' ^ 2) := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
        congr 1
        rw [lintegral_finsetSum Finset.univ (f := fun i (Y : Config d (n + 1)) => ∑ j ∈ Finset.univ.erase i,
          ENNReal.ofReal (3 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) * ‖h (Y i) (Y j)‖ₑ ^ 2)
          (fun i _ => Finset.measurable_sum _ fun j _ => measurable_const.mul (hmeas i j))]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [lintegral_finsetSum (Finset.univ.erase i) (f := fun j (Y : Config d (n + 1)) =>
          ENNReal.ofReal (3 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) * ‖h (Y i) (Y j)‖ₑ ^ 2)
          (fun j _ => measurable_const.mul (hmeas i j))]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [lintegral_const_mul _ (hmeas i j)]
    _ ≤ (∑ i : Fin (n + 1), ∑ j ∈ Finset.univ.erase i, ENNReal.ofReal (3 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) *
          ENNReal.ofReal (Wc * B ^ 2)) + ENNReal.ofReal (15 * H' ^ 2) := by
        gcongr with i _ j hj
        exact hpair i j (Finset.ne_of_mem_erase hj).symm
    _ ≤ ENNReal.ofReal (3 * (Wc * B ^ 2)) + ENNReal.ofReal (15 * H' ^ 2) := by
        gcongr
        calc (∑ i : Fin (n + 1), ∑ j ∈ Finset.univ.erase i, ENNReal.ofReal (3 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) *
              ENNReal.ofReal (Wc * B ^ 2))
            ≤ ∑ _i : Fin (n + 1), ∑ _j : Fin (n + 1), ENNReal.ofReal (3 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) *
              ENNReal.ofReal (Wc * B ^ 2) := by
              refine Finset.sum_le_sum fun i _ => ?_
              exact Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
          _ = ENNReal.ofReal (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) * (3 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) *
              (Wc * B ^ 2)))) := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              rw [ENNReal.ofReal_mul hNn, ENNReal.ofReal_mul hNn, ENNReal.ofReal_mul hc3,
                ENNReal.ofReal_natCast]
          _ = _ := by congr 1; field_simp
    _ = ENNReal.ofReal (3 * (Wc * B ^ 2) + 15 * H' ^ 2) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hH'def]
        have h1 : 0 ≤ Wc * B ^ 2 := by positivity
        nlinarith [sq_nonneg (cH * Λ), sq_nonneg Cp, sq_nonneg B, mul_nonneg (sq_nonneg Cp) h1,
          mul_nonneg (sq_nonneg (cH * Λ)) (sq_nonneg B), mul_nonneg (sq_nonneg Cp) (sq_nonneg B)]


end HRS.MD.EQStat

end
