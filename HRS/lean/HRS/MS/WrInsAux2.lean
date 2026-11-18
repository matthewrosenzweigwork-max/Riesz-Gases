import HRS.MS.WrInsAux1

/-!
# HRS.MS.WrInsAux2 -- insertion defect `0 ≤ D_N ≤ C δ_N` and cavity total variation (WR-13c2, part 2)

Packet WR-13c2 (T9 of `docs/WR_B_PLAN.md`), namespace `HRS.MS.Wr`, helper prefix `wr13c2_`.

Whole space `ℝ^d`, `2 ≤ d`, `0 < s < d` (all three regimes `2s <, =, > d`), `μ = ρ dx`, `ρ ≤ M`,
`β ∈ [βm, βp]` with `0 < βm`, `N ≥ 2`, `n = N-1`, `λ = β/N`, `δ_N = deltaN d s N`.

* `wr13c2_lintegral_J`: `∫_0^1 J_s(tλ) dt ≤ JI_s(λ)` (the three cases of `wr13c_J`);
* `wr13c2_lam_JI_le`: `λ² n JI_s(λ) ≤ K δ_N`, uniformly in `β ∈ [βm, βp]`;
* `wr13c2_insDefect_le` (main): `insertionDefect` exists as a right derivative, `0 ≤ D_N(x) ≤ C δ_N`, and the second
  difference `F(1) - 2F(1/2) ≤ C δ_N`, uniformly in `x`, `ρ ≤ M`, `β ∈ [βm, βp]`, `N ≥ 2`;
* `wr13c2_tv_pole`: `|P^{x,1}(Y_1 ∈ A) - P_n^0(Y_1 ∈ A)| ≤ K √(δ_N/N)` (exponential-family TV `EF.ef_tv`, pole variance
  `wr13b_pole_variance`, and the second difference of `insDefect_le`);
* `wr13c2_disint`: `π_N(A) = ∫ P^{x,1}(Y_1 ∈ A) dπ_N(x)` (from `wr13a_cavity_disintegration_density`);
* `wr13c2_cavity_tv` (main): `tvDist (Q_N)^{(1)} ν_n ≤ C √(δ_N / N)` (the last conjunct of
  `Bias.StaticInputConclusion`; stated with `Bias.tvDist`, equal to `Entropy.tvDist` by `wr13c2_tvDist_eq`).

Adjustments with respect to the sketch of `docs/WR_B_PLAN.md`: the derivative `F'_x(0)` is the right derivative
(so `insDefect_le` also states that `HasDerivWithinAt` holds, in the shape needed by `Bias.insertionDefect`);
the constants depend on `(d, s, βm, βp, M)` and are quantified before `ρ, β, N, x`; the radial integral is the
merged `wr13c_radial_J` (WR-13c1) integrated in `t`, so no separate layer-cake argument is needed.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wr

open HRS.Whole (rieszKernel EucConfig)

/-! ### 1. The `t`-integral of `J_s(tλ)` -/

section JInt

variable {d : ℕ} {s : ℝ}

/-- Closed-form majorant of `∫_0^1 J_s(tλ) dt`. -/
def wr13c2_JI (d : ℕ) (s lam : ℝ) : ℝ :=
  if 2 * s < d then 1
  else if 2 * s = d then 2 + |Real.log lam|
  else 1 + lam ^ ((d : ℝ) / s - 2) / ((d : ℝ) / s - 1)

theorem wr13c2_lintegral_one : ∫⁻ _t in Ioc (0 : ℝ) 1, (1 : ℝ≥0∞) = 1 := by
  simp

theorem wr13c2_lintegral_J_sub (h : 2 * s < d) (lam : ℝ) :
    ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (wr13c_J d s (t * lam)) ≤
      ENNReal.ofReal (wr13c2_JI d s lam) := by
  have e : ∀ t : ℝ, wr13c_J d s (t * lam) = 1 := fun t => by unfold wr13c_J; rw [if_pos h]
  simp only [e, wr13c2_JI, if_pos h, ENNReal.ofReal_one]
  simp

theorem wr13c2_lintegral_J_crit (hc : 2 * s = d) {lam : ℝ} (hlam : 0 < lam) :
    ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (wr13c_J d s (t * lam)) ≤
      ENNReal.ofReal (wr13c2_JI d s lam) := by
  have hlt : ¬ 2 * s < d := by rw [hc]; exact lt_irrefl _
  have e : ∀ t : ℝ, wr13c_J d s (t * lam) = 1 + |Real.log (t * lam)| := fun t => by
    unfold wr13c_J; rw [if_neg hlt, if_pos hc]
  have hJI : wr13c2_JI d s lam = 2 + |Real.log lam| := by
    unfold wr13c2_JI; rw [if_neg hlt, if_pos hc]
  simp only [e, hJI]
  calc ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (1 + |Real.log (t * lam)|)
      ≤ ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal ((1 + |Real.log lam|) - Real.log t) := by
        refine setLIntegral_mono' measurableSet_Ioc fun t ht => ENNReal.ofReal_le_ofReal ?_
        have ht0 : 0 < t := ht.1
        have hlog : Real.log t ≤ 0 := Real.log_nonpos ht0.le ht.2
        have : Real.log (t * lam) = Real.log t + Real.log lam := Real.log_mul ht0.ne' hlam.ne'
        rw [this]
        have h1 := abs_add_le (Real.log t) (Real.log lam)
        rw [abs_of_nonpos hlog] at h1
        linarith
    _ = ENNReal.ofReal (∫ t in (0 : ℝ)..1, ((1 + |Real.log lam|) - Real.log t)) := by
        refine HRS.PoleCavityAux.lintegral_Ioc_ofReal 0 1 zero_le_one _ ?_ ?_
        · exact intervalIntegrable_const.sub intervalIntegral.intervalIntegrable_log'
        · intro t ht
          have := Real.log_nonpos ht.1.le ht.2
          have := abs_nonneg (Real.log lam)
          linarith
    _ = ENNReal.ofReal (2 + |Real.log lam|) := by
        congr 1
        rw [intervalIntegral.integral_sub intervalIntegrable_const
          intervalIntegral.intervalIntegrable_log']
        simp [integral_log]
        ring

theorem wr13c2_lintegral_J_super (hs0 : 0 < s) (hsd : s < d) (hsup : (d : ℝ) < 2 * s)
    {lam : ℝ} (hlam : 0 < lam) :
    ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (wr13c_J d s (t * lam)) ≤
      ENNReal.ofReal (wr13c2_JI d s lam) := by
  have hlt : ¬ 2 * s < d := not_lt.2 hsup.le
  have hne : ¬ 2 * s = d := fun h => by linarith
  have hp1 : 1 < (d : ℝ) / s := by rw [lt_div_iff₀ hs0]; linarith
  set r : ℝ := (d : ℝ) / s - 2 with hr
  have hr1 : -1 < r := by rw [hr]; linarith
  have e : ∀ t : ℝ, 0 < t → wr13c_J d s (t * lam) = 1 + lam ^ r * t ^ r := fun t ht => by
    unfold wr13c_J
    rw [if_neg hlt, if_neg hne, Real.mul_rpow ht.le hlam.le]
    ring
  have hJI : wr13c2_JI d s lam = 1 + lam ^ r / ((d : ℝ) / s - 1) := by
    unfold wr13c2_JI; rw [if_neg hlt, if_neg hne]
  rw [hJI]
  calc ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (wr13c_J d s (t * lam))
      = ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (1 + lam ^ r * t ^ r) := by
        refine setLIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
        rw [e t ht.1]
    _ = ENNReal.ofReal (∫ t in (0 : ℝ)..1, (1 + lam ^ r * t ^ r)) := by
        refine HRS.PoleCavityAux.lintegral_Ioc_ofReal 0 1 zero_le_one _ ?_ ?_
        · exact intervalIntegrable_const.add
            ((intervalIntegral.intervalIntegrable_rpow' hr1).const_mul _)
        · intro t ht
          have := Real.rpow_nonneg hlam.le r
          have := Real.rpow_nonneg ht.1.le r
          positivity
    _ ≤ ENNReal.ofReal (1 + lam ^ r / ((d : ℝ) / s - 1)) := le_of_eq <| by
        congr 1
        rw [intervalIntegral.integral_add intervalIntegrable_const
          ((intervalIntegral.intervalIntegrable_rpow' hr1).const_mul _),
          intervalIntegral.integral_const_mul, integral_rpow (Or.inl hr1)]
        have h0 : (0 : ℝ) ^ (r + 1) = 0 := Real.zero_rpow (by linarith)
        have h1 : r + 1 = (d : ℝ) / s - 1 := by rw [hr]; ring
        rw [h0, h1]
        simp
        ring

theorem wr13c2_lintegral_J (hs0 : 0 < s) (hsd : s < d) {lam : ℝ} (hlam : 0 < lam) :
    ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (wr13c_J d s (t * lam)) ≤
      ENNReal.ofReal (wr13c2_JI d s lam) := by
  by_cases h1 : 2 * s < d
  · exact wr13c2_lintegral_J_sub h1 lam
  · by_cases hc : 2 * s = d
    · exact wr13c2_lintegral_J_crit hc hlam
    · exact wr13c2_lintegral_J_super hs0 hsd (lt_of_le_of_ne (not_lt.1 h1) (Ne.symm hc)) hlam

end JInt

/-! ### 2. `λ² n JI_s(λ) ≤ K δ_N` -/

section Scale

variable {d : ℕ} {s : ℝ}

theorem wr13c2_lam_sq_le {β : ℝ} {N : ℕ} (hN : 1 ≤ N) :
    (β / N) ^ 2 * ((N - 1 : ℕ) : ℝ) ≤ β ^ 2 * (N : ℝ)⁻¹ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub hN]; simp
  rw [hcast]
  have : (β / N) ^ 2 * ((N : ℝ) - 1) = β ^ 2 * ((N : ℝ) - 1) / (N : ℝ) ^ 2 := by
    field_simp
  rw [this, div_le_iff₀ (by positivity)]
  have : β ^ 2 * (N : ℝ)⁻¹ * (N : ℝ) ^ 2 = β ^ 2 * N := by field_simp
  rw [this]
  nlinarith [sq_nonneg β]

theorem wr13c2_lam_JI_sub (h : 2 * s < d) {βp : ℝ} {β : ℝ} (hβ0 : 0 < β) (hβp : β ≤ βp) {N : ℕ}
    (hN : 1 ≤ N) :
    (β / N) ^ 2 * ((N - 1 : ℕ) : ℝ) * wr13c2_JI d s (β / N) ≤ βp ^ 2 * deltaN d s N := by
  have hJI : wr13c2_JI d s (β / N) = 1 := by unfold wr13c2_JI; rw [if_pos h]
  rw [hJI, mul_one, wr13c_deltaN_sub h]
  refine (wr13c2_lam_sq_le hN).trans ?_
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have : β ^ 2 ≤ βp ^ 2 := by nlinarith
  exact mul_le_mul_of_nonneg_right this (by positivity)

theorem wr13c2_lam_JI_crit (hc : 2 * s = d) {βm βp : ℝ} (hβm : 0 < βm) {β : ℝ} (hβ1 : βm ≤ β)
    (hβp : β ≤ βp) {N : ℕ} (hN : 1 ≤ N) :
    (β / N) ^ 2 * ((N - 1 : ℕ) : ℝ) * wr13c2_JI d s (β / N) ≤
      (βp ^ 2 * (2 + (|Real.log βm| + |Real.log βp|))) * deltaN d s N := by
  have hlt : ¬ 2 * s < d := by rw [hc]; exact lt_irrefl _
  have hJI : wr13c2_JI d s (β / N) = 2 + |Real.log (β / N)| := by
    unfold wr13c2_JI; rw [if_neg hlt, if_pos hc]
  rw [hJI, wr13c_deltaN_crit hc hN]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ1
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hlogβ : |Real.log β| ≤ |Real.log βm| + |Real.log βp| := by
    have h1 : Real.log βm ≤ Real.log β := Real.log_le_log hβm hβ1
    have h2 : Real.log β ≤ Real.log βp := Real.log_le_log hβ0 hβp
    have := neg_abs_le (Real.log βm)
    have := le_abs_self (Real.log βp)
    have := abs_nonneg (Real.log βm)
    have := abs_nonneg (Real.log βp)
    rw [abs_le]; constructor <;> linarith
  have hloglam : |Real.log (β / N)| ≤ |Real.log βm| + |Real.log βp| + Real.log N := by
    rw [Real.log_div hβ0.ne' hN0.ne']
    have := abs_sub (Real.log β) (Real.log N)
    rw [abs_of_nonneg hlogN] at this
    linarith
  set L : ℝ := |Real.log βm| + |Real.log βp| with hL
  have hL0 : 0 ≤ L := by positivity
  have h2 : 2 + |Real.log (β / N)| ≤ (2 + L) * (1 + Real.log N) := by nlinarith
  have h1 := wr13c2_lam_sq_le (β := β) hN
  have h3 : (β / N) ^ 2 * ((N - 1 : ℕ) : ℝ) * (2 + |Real.log (β / N)|) ≤
      (β ^ 2 * (N : ℝ)⁻¹) * ((2 + L) * (1 + Real.log N)) :=
    mul_le_mul h1 h2 (by positivity) (by positivity)
  refine h3.trans ?_
  have : β ^ 2 ≤ βp ^ 2 := by nlinarith
  calc (β ^ 2 * (N : ℝ)⁻¹) * ((2 + L) * (1 + Real.log N))
      = β ^ 2 * (2 + L) * ((N : ℝ)⁻¹ * (1 + Real.log N)) := by ring
    _ ≤ βp ^ 2 * (2 + L) * ((N : ℝ)⁻¹ * (1 + Real.log N)) := by
        gcongr
    _ = _ := by ring

theorem wr13c2_lam_JI_super (hs0 : 0 < s) (hsd : s < d) (hsup : (d : ℝ) < 2 * s) {βp : ℝ} {β : ℝ} (hβ0 : 0 < β)
    (hβp : β ≤ βp) {N : ℕ} (hN : 1 ≤ N) :
    (β / N) ^ 2 * ((N - 1 : ℕ) : ℝ) * wr13c2_JI d s (β / N) ≤
      (βp ^ 2 + βp ^ ((d : ℝ) / s) / ((d : ℝ) / s - 1)) * deltaN d s N := by
  have hlt : ¬ 2 * s < d := not_lt.2 hsup.le
  have hne : ¬ 2 * s = d := fun h => by linarith
  have hJI : wr13c2_JI d s (β / N) = 1 + (β / N) ^ ((d : ℝ) / s - 2) / ((d : ℝ) / s - 1) := by
    unfold wr13c2_JI; rw [if_neg hlt, if_neg hne]
  rw [hJI, wr13c_deltaN_super hsup]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set p : ℝ := (d : ℝ) / s with hp
  have hp1 : 1 < p := by rw [hp, lt_div_iff₀ hs0]; linarith
  have hp2 : p < 2 := by rw [hp, div_lt_iff₀ hs0]; linarith
  have hlam : 0 < β / N := by positivity
  have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by rw [Nat.cast_sub hN]; simp
  have hNp : (N : ℝ) ^ (1 - p) = (N : ℝ) / (N : ℝ) ^ p := by
    rw [Real.rpow_sub hN0, Real.rpow_one]
  have hβp0 : 0 < βp := lt_of_lt_of_le hβ0 hβp
  -- first term
  have t1 : (β / N) ^ 2 * ((N - 1 : ℕ) : ℝ) ≤ βp ^ 2 * (N : ℝ) ^ (1 - p) := by
    refine (wr13c2_lam_sq_le hN).trans ?_
    have h1 : (N : ℝ)⁻¹ ≤ (N : ℝ) ^ (1 - p) := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have : β ^ 2 ≤ βp ^ 2 := by nlinarith
    exact mul_le_mul this h1 (by positivity) (by positivity)
  -- second term
  have t2 : (β / N) ^ 2 * ((N - 1 : ℕ) : ℝ) * ((β / N) ^ (p - 2) / (p - 1)) ≤
      βp ^ p / (p - 1) * (N : ℝ) ^ (1 - p) := by
    have e1 : (β / N) ^ 2 * (β / N) ^ (p - 2) = (β / N) ^ p := by
      rw [← Real.rpow_two, ← Real.rpow_add hlam]
      congr 1; ring
    have e2 : (β / N) ^ p = β ^ p / (N : ℝ) ^ p := Real.div_rpow hβ0.le hN0.le p
    have hp0 : 0 < (N : ℝ) ^ p := Real.rpow_pos_of_pos hN0 p
    have e3 : (β / N) ^ 2 * ((N - 1 : ℕ) : ℝ) * ((β / N) ^ (p - 2) / (p - 1)) =
        ((β / N) ^ p * ((N : ℝ) - 1)) / (p - 1) := by
      rw [hcast, ← e1]; ring
    rw [e3, e2, hNp]
    have hβpp : β ^ p ≤ βp ^ p := Real.rpow_le_rpow hβ0.le hβp (by linarith)
    have hp1' : 0 < p - 1 := by linarith
    rw [div_le_iff₀ hp1']
    have : βp ^ p / (p - 1) * (↑N / ↑N ^ p) * (p - 1) = βp ^ p * (↑N / ↑N ^ p) := by
      field_simp
    rw [this]
    have h3 : β ^ p / (N : ℝ) ^ p * ((N : ℝ) - 1) ≤ β ^ p * ((N : ℝ) / (N : ℝ) ^ p) := by
      have e : β ^ p * ((N : ℝ) / (N : ℝ) ^ p) = β ^ p / (N : ℝ) ^ p * N := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    refine h3.trans ?_
    exact mul_le_mul_of_nonneg_right hβpp (by positivity)
  calc (β / N) ^ 2 * ((N - 1 : ℕ) : ℝ) * (1 + (β / N) ^ (p - 2) / (p - 1))
      = (β / N) ^ 2 * ((N - 1 : ℕ) : ℝ) +
        (β / N) ^ 2 * ((N - 1 : ℕ) : ℝ) * ((β / N) ^ (p - 2) / (p - 1)) := by ring
    _ ≤ βp ^ 2 * (N : ℝ) ^ (1 - p) + βp ^ p / (p - 1) * (N : ℝ) ^ (1 - p) := add_le_add t1 t2
    _ = _ := by ring

theorem wr13c2_lam_JI_le (hd : 1 ≤ d) (hs0 : 0 < s) (hsd : s < d) {βm : ℝ} (hβm : 0 < βm)
    (βp : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ β : ℝ, βm ≤ β → β ≤ βp → ∀ N : ℕ, 1 ≤ N →
      (β / N) ^ 2 * ((N - 1 : ℕ) : ℝ) * wr13c2_JI d s (β / N) ≤ K * deltaN d s N := by
  have hp1 : 1 < (d : ℝ) / s := by rw [lt_div_iff₀ hs0]; linarith
  refine ⟨max (βp ^ 2) 0 + max (βp ^ 2 * (2 + (|Real.log βm| + |Real.log βp|))) 0 +
      max (βp ^ 2 + βp ^ ((d : ℝ) / s) / ((d : ℝ) / s - 1)) 0, by positivity, ?_⟩
  intro β hβ1 hβp N hN
  have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ1
  have hδ : 0 ≤ deltaN d s N := (wr13c_deltaN_pos_le_one hd hs0 hsd hN).1.le
  by_cases h1 : 2 * s < d
  · have := wr13c2_lam_JI_sub h1 hβ0 hβp hN
    refine this.trans ?_
    have : βp ^ 2 ≤ max (βp ^ 2) 0 + max (βp ^ 2 * (2 + (|Real.log βm| + |Real.log βp|))) 0 +
      max (βp ^ 2 + βp ^ ((d : ℝ) / s) / ((d : ℝ) / s - 1)) 0 := by
      have := le_max_left (βp ^ 2) 0
      have := le_max_right (βp ^ 2 * (2 + (|Real.log βm| + |Real.log βp|))) 0
      have := le_max_right (βp ^ 2 + βp ^ ((d : ℝ) / s) / ((d : ℝ) / s - 1)) 0
      linarith
    exact mul_le_mul_of_nonneg_right this hδ
  · by_cases hc : 2 * s = d
    · have := wr13c2_lam_JI_crit hc hβm hβ1 hβp hN
      refine this.trans ?_
      have : βp ^ 2 * (2 + (|Real.log βm| + |Real.log βp|)) ≤ max (βp ^ 2) 0 +
          max (βp ^ 2 * (2 + (|Real.log βm| + |Real.log βp|))) 0 +
          max (βp ^ 2 + βp ^ ((d : ℝ) / s) / ((d : ℝ) / s - 1)) 0 := by
        have := le_max_right (βp ^ 2) 0
        have := le_max_left (βp ^ 2 * (2 + (|Real.log βm| + |Real.log βp|))) 0
        have := le_max_right (βp ^ 2 + βp ^ ((d : ℝ) / s) / ((d : ℝ) / s - 1)) 0
        linarith
      exact mul_le_mul_of_nonneg_right this hδ
    · have hsup : (d : ℝ) < 2 * s := lt_of_le_of_ne (not_lt.1 h1) (Ne.symm hc)
      have := wr13c2_lam_JI_super hs0 hsd hsup hβ0 hβp hN
      refine this.trans ?_
      have : βp ^ 2 + βp ^ ((d : ℝ) / s) / ((d : ℝ) / s - 1) ≤ max (βp ^ 2) 0 +
          max (βp ^ 2 * (2 + (|Real.log βm| + |Real.log βp|))) 0 +
          max (βp ^ 2 + βp ^ ((d : ℝ) / s) / ((d : ℝ) / s - 1)) 0 := by
        have := le_max_right (βp ^ 2) 0
        have := le_max_right (βp ^ 2 * (2 + (|Real.log βm| + |Real.log βp|))) 0
        have := le_max_left (βp ^ 2 + βp ^ ((d : ℝ) / s) / ((d : ℝ) / s - 1)) 0
        linarith
      exact mul_le_mul_of_nonneg_right this hδ

end Scale

/-! ### 3. The insertion defect -/

section Defect

variable {d : ℕ} {s : ℝ}

theorem wr13c2_JI_nonneg (hs0 : 0 < s) (hsd : s < d) {lam : ℝ} (hlam : 0 < lam) :
    0 ≤ wr13c2_JI d s lam := by
  unfold wr13c2_JI
  split_ifs with h1 h2
  · exact zero_le_one
  · positivity
  · have hp1 : 1 < (d : ℝ) / s := by rw [lt_div_iff₀ hs0]; linarith
    have : 0 < (d : ℝ) / s - 1 := by linarith
    have := Real.rpow_nonneg hlam.le ((d : ℝ) / s - 2)
    positivity

/-- The variance of the pole exponent along the pole path is `λ²` times the variance of `∑ g(x - Y_i)`. -/
theorem wr13c2_variance_X (N : ℕ) (β : ℝ) (x : Euc d) (P : Measure (EucConfig d (N - 1))) :
    Var[wr13c2_X d s N β x; P] =
      (β / N) ^ 2 * (evariance (fun Y : EucConfig d (N - 1) => ∑ i, rieszKernel d s (x - Y i)) P).toReal := by
  have := variance_const_mul (-(β / N)) (fun Y : EucConfig d (N - 1) => ∑ i, rieszKernel d s (x - Y i)) P
  rw [neg_sq] at this
  exact this

theorem wr13c2_enorm_sq_mul {z a : ℝ} :
    ‖z‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-a * z)) =
      ENNReal.ofReal (z ^ 2 * Real.exp (-(a * z))) := by
  rw [ENNReal.ofReal_mul (sq_nonneg _), ← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _), neg_mul]

/-- **Insertion defect** (`euc-insertion`): for `2 ≤ d`, `0 < s < d`, `0 < βm ≤ β ≤ βp`, `N ≥ 2`, `ρ ≤ M`,
the insertion pressure `F_{N,x}(t) = log P_n^0[e^{-tλ∑g(x-y_i)}]` has a right derivative at `0` (equal to the
cavity mean of the pole exponent), `0 ≤ D_N(x) = F(1) - F'(0) ≤ C δ_N` and `F(1) - 2F(1/2) ≤ C δ_N`;
`C` depends only on `(d, s, βm, βp, M)`. -/
theorem wr13c2_insDefect_le (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) {βm : ℝ} (hβm : 0 < βm)
    (βp M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ β : ℝ, βm ≤ β → β ≤ βp → ∀ N : ℕ, 2 ≤ N → ∀ x : Euc d,
        HasDerivWithinAt (HRS.Whole.insertionPressure d s N β (HRS.Whole.withDensityReal ρ) x)
          (∫ Y, wr13c2_X d s N β x Y ∂(HRS.Whole.cavityLaw d s N β (HRS.Whole.withDensityReal ρ)))
          (Ici 0) 0 ∧
        0 ≤ HRS.Whole.insertionDefect d s N β (HRS.Whole.withDensityReal ρ) x ∧
        HRS.Whole.insertionDefect d s N β (HRS.Whole.withDensityReal ρ) x ≤ C * deltaN d s N ∧
        HRS.Whole.insertionPressure d s N β (HRS.Whole.withDensityReal ρ) x 1 -
          2 * HRS.Whole.insertionPressure d s N β (HRS.Whole.withDensityReal ρ) x (1 / 2) ≤
            C * deltaN d s N := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C₁, hC₁, hvar⟩ := wr13b_pole_variance hd hs0 hsd βp M
  obtain ⟨Cr, hCr0, hrad⟩ := wr13c_radial_J hd1 hs0 hsd M
  obtain ⟨K, hK0, hK⟩ := wr13c2_lam_JI_le hd1 hs0 hsd hβm βp
  refine ⟨C₁ * Cr * K, by positivity, fun ρ hρ hM β hβ1 hββp N hN x => ?_⟩
  have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ1
  haveI := wr13a_isProb_density hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  have hconv := wr13a_conv_le_density hd1 hs0 hsd hρ hM
  haveI hP0 := wr13a_cavityLaw_isProb hs0 hconv hβ0.le N
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam : 0 < β / N := by positivity
  set P0 := HRS.Whole.cavityLaw d s N β μ with hP0def
  have hXm := wr13c2_X_meas hs0 N β x
  have hb := wr13c2_X_le_zero hs0 hβ0.le N x
  have hXi := wr13c2_integrable_X hd hs0 hsd hρ hM hβ0.le hN x
  have hgm : Measurable (fun y : Euc d => rieszKernel d s (x - y)) :=
    (wr13a_g_meas hs0).comp (measurable_const.sub measurable_id)
  set lam : ℝ := β / N with hlamdef
  set n : ℝ := ((N - 1 : ℕ) : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  set w : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (lam ^ 2) * (ENNReal.ofReal (C₁ * n) *
    ∫⁻ y, ‖rieszKernel d s (x - y)‖ₑ ^ 2 *
      ENNReal.ofReal (Real.exp (-(t * lam) * rieszKernel d s (x - y))) ∂μ) with hw
  have hwle : ∀ t ∈ Ioc (0 : ℝ) 1,
      ENNReal.ofReal (Var[wr13c2_X d s N β x; P0.tilted (fun Y => t * wr13c2_X d s N β x Y)]) ≤ w t := by
    intro t ht
    rw [← wr13c2_poleLaw_eq_tilted hs0 hconv hβ0.le ht.1.le N x, wr13c2_variance_X,
      ENNReal.ofReal_mul (sq_nonneg _)]
    have h1 := hvar ρ hρ hM β hβ0 hββp N hN x t ⟨ht.1.le, ht.2⟩ (fun y => rieszKernel d s (x - y)) hgm
    exact mul_le_mul' le_rfl ((ENNReal.ofReal_toReal_le).trans h1)
  -- pointwise radial bound
  have hinner : ∀ t ∈ Ioc (0 : ℝ) 1, ∫⁻ y, ‖rieszKernel d s (x - y)‖ₑ ^ 2 *
      ENNReal.ofReal (Real.exp (-(t * lam) * rieszKernel d s (x - y))) ∂μ ≤
      ENNReal.ofReal (Cr * wr13c_J d s (t * lam)) := by
    intro t ht
    have hu : 0 < t * lam := mul_pos ht.1 hlam
    have : ∀ y, ‖rieszKernel d s (x - y)‖ₑ ^ 2 *
        ENNReal.ofReal (Real.exp (-(t * lam) * rieszKernel d s (x - y))) =
        ENNReal.ofReal (rieszKernel d s (x - y) ^ 2 *
          Real.exp (-((t * lam) * rieszKernel d s (x - y)))) := fun y =>
      wr13c2_enorm_sq_mul
    simp_rw [this]
    exact hrad ρ hρ hM (t * lam) hu x
  have hJ1 := wr13c2_lintegral_J hs0 hsd hlam
  have hWle : ∫⁻ t in Ioc (0 : ℝ) 1, w t ≤ ENNReal.ofReal (C₁ * Cr * (lam ^ 2 * n * wr13c2_JI d s lam)) := by
    calc ∫⁻ t in Ioc (0 : ℝ) 1, w t
        ≤ ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (lam ^ 2 * (C₁ * n) * Cr) *
            ENNReal.ofReal (wr13c_J d s (t * lam)) := by
          refine setLIntegral_mono' measurableSet_Ioc fun t ht => ?_
          have hJ0 : 0 ≤ wr13c_J d s (t * lam) := (zero_le_one.trans (wr13c_one_le_J _ (mul_pos ht.1 hlam)))
          calc w t ≤ ENNReal.ofReal (lam ^ 2) * (ENNReal.ofReal (C₁ * n) *
                ENNReal.ofReal (Cr * wr13c_J d s (t * lam))) := by
                exact mul_le_mul' le_rfl (mul_le_mul' le_rfl (hinner t ht))
            _ = _ := by
                rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
                  ← ENNReal.ofReal_mul (by positivity)]
                congr 1; ring
      _ = ENNReal.ofReal (lam ^ 2 * (C₁ * n) * Cr) *
            ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (wr13c_J d s (t * lam)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (lam ^ 2 * (C₁ * n) * Cr) * ENNReal.ofReal (wr13c2_JI d s lam) :=
          mul_le_mul' le_rfl hJ1
      _ = ENNReal.ofReal (C₁ * Cr * (lam ^ 2 * n * wr13c2_JI d s lam)) := by
          have hJI0 := wr13c2_JI_nonneg (d := d) hs0 hsd hlam
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring
  have hWfin : ∫⁻ t in Ioc (0 : ℝ) 1, w t ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hWle
  obtain ⟨hD1, hD2⟩ := HRS.MarginalAux.EF.ef_main hXm hb hXi w hwle hWfin
  have hδ := (wr13c_deltaN_pos_le_one hd1 hs0 hsd (by omega : 1 ≤ N)).1
  have hJI0 := wr13c2_JI_nonneg (d := d) hs0 hsd hlam
  have hWb : (∫⁻ t in Ioc (0 : ℝ) 1, w t).toReal ≤ C₁ * Cr * K * deltaN d s N := by
    refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top hWle).trans ?_
    rw [ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg hC₁.le hCr0)
      (mul_nonneg (mul_nonneg (sq_nonneg lam) hn0) hJI0))]
    have hK1 : lam ^ 2 * n * wr13c2_JI d s lam ≤ K * deltaN d s N := hK β hβ1 hββp N (by omega)
    calc C₁ * Cr * (lam ^ 2 * n * wr13c2_JI d s lam) ≤ C₁ * Cr * (K * deltaN d s N) :=
          mul_le_mul_of_nonneg_left hK1 (mul_nonneg hC₁.le hCr0)
      _ = C₁ * Cr * K * deltaN d s N := by ring
  obtain ⟨hder, hdefeq⟩ := wr13c2_insertionDefect_eq hd hs0 hsd hρ hM hβ0.le hN x
  have hWnn : 0 ≤ (∫⁻ t in Ioc (0 : ℝ) 1, w t).toReal := ENNReal.toReal_nonneg
  have hge := HRS.MarginalAux.EF.ef_cgf_ge hXm hb hXi
  refine ⟨hder, ?_, ?_, ?_⟩
  · rw [hdefeq]; linarith
  · rw [hdefeq]; linarith
  · have e1 := congrFun (wr13c2_insertionPressure_eq (d := d) (s := s) N β μ x) 1
    have e2 := congrFun (wr13c2_insertionPressure_eq (d := d) (s := s) N β μ x) (1 / 2)
    rw [e1, e2]
    linarith

end Defect

/-! ### 4. The cavity total variation: pieces -/

section TVPieces

variable {d : ℕ} {s : ℝ}

/-- The fraction `φ_A(Y) = n⁻¹ ∑_j 1_A(Y_j)` of particles in `A`. -/
def wr13c2_fracIn {n : ℕ} (A : Set (Euc d)) (Y : EucConfig d n) : ℝ :=
  (1 / (n : ℝ)) * ∑ j, A.indicator (fun _ => (1 : ℝ)) (Y j)

theorem wr13c2_measurable_fracIn {n : ℕ} {A : Set (Euc d)} (hA : MeasurableSet A) :
    Measurable (wr13c2_fracIn (n := n) A) :=
  (Finset.measurable_sum _ fun j _ =>
    (measurable_const.indicator hA).comp (measurable_pi_apply j)).const_mul _

theorem wr13c2_abs_fracIn_le {n : ℕ} (hn : 0 < n) (A : Set (Euc d)) (Y : EucConfig d n) :
    |wr13c2_fracIn A Y| ≤ 1 := by
  unfold wr13c2_fracIn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : ∀ j, |A.indicator (fun _ => (1 : ℝ)) (Y j)| ≤ 1 := fun j => by
    by_cases h : Y j ∈ A <;> simp [Set.indicator, h]
  rw [abs_mul, abs_of_pos (by positivity)]
  have : |∑ j, A.indicator (fun _ => (1 : ℝ)) (Y j)| ≤ n := by
    calc _ ≤ ∑ j, |A.indicator (fun _ => (1 : ℝ)) (Y j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin n, (1 : ℝ) := Finset.sum_le_sum fun j _ => h1 j
      _ = n := by simp
  calc 1 / (n : ℝ) * |∑ j, A.indicator (fun _ => (1 : ℝ)) (Y j)| ≤ 1 / (n : ℝ) * n :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = 1 := by field_simp

theorem wr13c2_integral_fracIn {n : ℕ} (hn : 0 < n) {A : Set (Euc d)} (hA : MeasurableSet A)
    (Pm : Measure (EucConfig d n)) [IsProbabilityMeasure Pm]
    (hR : HRS.External.Entropy.IsExchangeable Pm) :
    ∫ Y, wr13c2_fracIn A Y ∂Pm = (Pm {Y : EucConfig d n | Y ⟨0, hn⟩ ∈ A}).toReal := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold wr13c2_fracIn
  rw [integral_const_mul, integral_finset_sum]
  · have : ∀ j : Fin n, ∫ Y, A.indicator (fun _ => (1 : ℝ)) (Y j) ∂Pm =
        (Pm {Y : EucConfig d n | Y ⟨0, hn⟩ ∈ A}).toReal := by
      intro j
      have h1 : ∫ Y, A.indicator (fun _ => (1 : ℝ)) (Y j) ∂Pm = (Pm {Y : EucConfig d n | Y j ∈ A}).toReal := by
        have : (fun Y : EucConfig d n => A.indicator (fun _ => (1 : ℝ)) (Y j)) =
            ({Y : EucConfig d n | Y j ∈ A}).indicator (fun _ => (1 : ℝ)) := by
          funext Y; simp [Set.indicator]
        have hm : MeasurableSet {Y : EucConfig d n | Y j ∈ A} := (measurable_pi_apply j) hA
        rw [this, integral_indicator_const _ hm]
        simp [Measure.real]
      rw [h1]
      have := hR.marginal_eq j ⟨0, hn⟩
      have h2 := congrArg (fun m => m A) this
      rw [Measure.map_apply (measurable_pi_apply j) hA,
        Measure.map_apply (measurable_pi_apply (⟨0, hn⟩ : Fin n)) hA] at h2
      exact congrArg ENNReal.toReal h2
    simp_rw [this]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  · intro j _
    exact (Integrable.of_bound (C := 1)
      ((measurable_const.indicator hA).comp (measurable_pi_apply j)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun Y => by
        by_cases h : Y j ∈ A <;> simp [Set.indicator, h]))

theorem wr13c2_var_fracIn_le {n : ℕ} (hn : 0 < n) {A : Set (Euc d)} {P : Measure (EucConfig d n)}
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (h : evariance (fun Y : EucConfig d n => ∑ i, A.indicator (fun _ : Euc d => (1 : ℝ)) (Y i)) P ≤
      ENNReal.ofReal (C₁ * n)) :
    Var[wr13c2_fracIn (n := n) A; P] ≤ C₁ / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h2 : Var[wr13c2_fracIn (n := n) A; P] =
      (1 / (n : ℝ)) ^ 2 * (evariance (fun Y : EucConfig d n =>
        ∑ i, A.indicator (fun _ : Euc d => (1 : ℝ)) (Y i)) P).toReal :=
    variance_const_mul (1 / (n : ℝ)) (fun Y : EucConfig d n =>
      ∑ i, A.indicator (fun _ : Euc d => (1 : ℝ)) (Y i)) P
  rw [h2]
  have h4 : (evariance (fun Y : EucConfig d n => ∑ i, A.indicator (fun _ : Euc d => (1 : ℝ)) (Y i)) P).toReal
      ≤ C₁ * n :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans (by rw [ENNReal.toReal_ofReal (by positivity)])
  calc (1 / (n : ℝ)) ^ 2 * (evariance _ _).toReal ≤ (1 / (n : ℝ)) ^ 2 * (C₁ * n) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = C₁ / n := by field_simp

theorem wr13c2_exp_sub_one_le (Δ c δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hc : 0 ≤ c)
    (hΔ : Δ ≤ c * δ) : Real.exp Δ - 1 ≤ (c * Real.exp c) * δ := by
  rcases le_total Δ 0 with h | h
  · have : Real.exp Δ ≤ 1 := Real.exp_le_one_iff.2 h
    have : 0 ≤ (c * Real.exp c) * δ := by positivity
    linarith
  · have h1 : Real.exp Δ - 1 ≤ Δ * Real.exp Δ := by
      have h2 := Real.add_one_le_exp (-Δ)
      have h3 : Real.exp (-Δ) * Real.exp Δ = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos Δ]
    have h4 : Δ ≤ c := hΔ.trans (by nlinarith)
    have h5 : Real.exp Δ ≤ Real.exp c := Real.exp_le_exp.2 h4
    calc Real.exp Δ - 1 ≤ Δ * Real.exp Δ := h1
      _ ≤ (c * δ) * Real.exp c := mul_le_mul hΔ h5 (Real.exp_pos _).le (by positivity)
      _ = (c * Real.exp c) * δ := by ring

theorem wr13c2_sqrt_chain {a b e K1 K2 δ : ℝ} {n N : ℝ} (hn : 0 < n) (hN : 0 < N) (hnN : N ≤ 2 * n)
    (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hδ : 0 ≤ δ) (ha : a ≤ K1 / n) (hb : b ≤ K1 / n)
    (he : e ≤ K2 * δ) :
    (Real.sqrt a + Real.sqrt b) * Real.sqrt e ≤ 2 * Real.sqrt (2 * (K1 * K2)) * Real.sqrt (δ / N) := by
  have h1 : Real.sqrt a ≤ Real.sqrt (K1 / n) := Real.sqrt_le_sqrt ha
  have h2 : Real.sqrt b ≤ Real.sqrt (K1 / n) := Real.sqrt_le_sqrt hb
  have h3 : Real.sqrt e ≤ Real.sqrt (K2 * δ) := Real.sqrt_le_sqrt he
  have h4 : (Real.sqrt a + Real.sqrt b) * Real.sqrt e ≤ (2 * Real.sqrt (K1 / n)) * Real.sqrt (K2 * δ) :=
    mul_le_mul (by linarith) h3 (Real.sqrt_nonneg _) (by positivity)
  refine h4.trans ?_
  have h5 : Real.sqrt (K1 / n) * Real.sqrt (K2 * δ) ≤ Real.sqrt (2 * (K1 * K2)) * Real.sqrt (δ / N) := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    have : K1 / n * (K2 * δ) = (K1 * K2) * δ / n := by ring
    rw [this, show 2 * (K1 * K2) * (δ / N) = (2 * (K1 * K2) * δ) / N by ring]
    rw [div_le_div_iff₀ hn hN]
    have : 0 ≤ K1 * K2 * δ := by positivity
    nlinarith
  calc 2 * Real.sqrt (K1 / n) * Real.sqrt (K2 * δ) = 2 * (Real.sqrt (K1 / n) * Real.sqrt (K2 * δ)) := by ring
    _ ≤ 2 * (Real.sqrt (2 * (K1 * K2)) * Real.sqrt (δ / N)) := by gcongr
    _ = _ := by ring

theorem wr13c2_real_close {a b : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞) {K : ℝ} (hK : 0 ≤ K)
    (h1 : a ≤ b + ENNReal.ofReal K) (h2 : b ≤ a + ENNReal.ofReal K) :
    |a.toReal - b.toReal| ≤ K := by
  have e1 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hb, ENNReal.ofReal_ne_top⟩) h1
  have e2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ha, ENNReal.ofReal_ne_top⟩) h2
  rw [ENNReal.toReal_add hb ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hK] at e1
  rw [ENNReal.toReal_add ha ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hK] at e2
  rw [abs_le]; constructor <;> linarith

theorem wr13c2_ennreal_close {a b : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞) {K : ℝ}
    (h : |a.toReal - b.toReal| ≤ K) : a ≤ b + ENNReal.ofReal K ∧ b ≤ a + ENNReal.ofReal K := by
  have hK : 0 ≤ K := (abs_nonneg _).trans h
  rw [abs_le] at h
  constructor
  · rw [← ENNReal.toReal_le_toReal ha (ENNReal.add_ne_top.2 ⟨hb, ENNReal.ofReal_ne_top⟩),
      ENNReal.toReal_add hb ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hK]
    linarith
  · rw [← ENNReal.toReal_le_toReal hb (ENNReal.add_ne_top.2 ⟨ha, ENNReal.ofReal_ne_top⟩),
      ENNReal.toReal_add ha ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hK]
    linarith

end TVPieces

/-! ### 5. The pole TV bound at a fixed pole location -/

section TVPole

variable {d : ℕ} {s : ℝ}

theorem wr13c2_pole_ind_variance (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) (βp M : ℝ) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ β : ℝ, 0 < β → β ≤ βp → ∀ N : ℕ, 2 ≤ N → ∀ x : Euc d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ A : Set (Euc d), MeasurableSet A →
          Var[wr13c2_fracIn (n := N - 1) A;
            HRS.Whole.poleLaw d s N β (HRS.Whole.withDensityReal ρ) x t] ≤ C₁ / ((N - 1 : ℕ) : ℝ) := by
  obtain ⟨C₁, hC₁, hvar⟩ := wr13b_pole_variance hd hs0 hsd βp M
  refine ⟨C₁, hC₁, fun ρ hρ hM β hβ0 hββp N hN x t ht A hA => ?_⟩
  haveI := wr13a_isProb_density hρ
  have hf : Measurable (A.indicator (fun _ : Euc d => (1 : ℝ))) := measurable_const.indicator hA
  have h1 := hvar ρ hρ hM β hβ0 hββp N hN x t ht _ hf
  have h3 : ∫⁻ y, ‖A.indicator (fun _ : Euc d => (1 : ℝ)) y‖ₑ ^ 2 *
      ENNReal.ofReal (Real.exp (-(t * (β / N)) * rieszKernel d s (x - y)))
        ∂(HRS.Whole.withDensityReal ρ) ≤ 1 := by
    calc _ ≤ ∫⁻ _y, (1 : ℝ≥0∞) ∂(HRS.Whole.withDensityReal ρ) := by
          refine lintegral_mono fun y => ?_
          have e1 : ‖A.indicator (fun _ : Euc d => (1 : ℝ)) y‖ₑ ^ 2 ≤ 1 := by
            by_cases h : y ∈ A <;> simp [Set.indicator, h]
          have e2 : ENNReal.ofReal (Real.exp (-(t * (β / N)) * rieszKernel d s (x - y))) ≤ 1 := by
            refine ENNReal.ofReal_le_one.2 (Real.exp_le_one_iff.2 ?_)
            exact mul_nonpos_of_nonpos_of_nonneg
              (neg_nonpos.2 (mul_nonneg ht.1 (div_nonneg hβ0.le (Nat.cast_nonneg _))))
              (wr13a_g_nonneg hs0 _)
          calc _ ≤ 1 * 1 := mul_le_mul' e1 e2
            _ = 1 := one_mul 1
      _ = 1 := by simp
  have h5 : evariance (fun Y : EucConfig d (N - 1) => ∑ i, A.indicator (fun _ : Euc d => (1 : ℝ)) (Y i))
      (HRS.Whole.poleLaw d s N β (HRS.Whole.withDensityReal ρ) x t) ≤
      ENNReal.ofReal (C₁ * ((N - 1 : ℕ) : ℝ)) :=
    h1.trans (by simpa using mul_le_mul' (le_refl (ENNReal.ofReal (C₁ * ((N - 1 : ℕ) : ℝ)))) h3)
  exact wr13c2_var_fracIn_le (by omega) hC₁.le h5

/-- The pole tilt moves the one-coordinate law by at most `K √(δ_N/N)`: for the event
`{Y_1 ∈ A}`, `|P^{x,1}(Y_1 ∈ A) - P_n^0(Y_1 ∈ A)| ≤ K √(δ_N/N)`, uniformly in `x`. -/
theorem wr13c2_tv_pole (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) {βm : ℝ} (hβm : 0 < βm)
    (βp M : ℝ) :
    ∃ Kt : ℝ, 0 ≤ Kt ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ β : ℝ, βm ≤ β → β ≤ βp → ∀ N : ℕ, ∀ hN : 2 ≤ N, ∀ x : Euc d, ∀ A : Set (Euc d),
        MeasurableSet A →
        |(HRS.Whole.poleLaw d s N β (HRS.Whole.withDensityReal ρ) x 1
            {Y : EucConfig d (N - 1) | Y ⟨0, by omega⟩ ∈ A}).toReal -
          (HRS.Whole.cavityLaw d s N β (HRS.Whole.withDensityReal ρ)
            {Y : EucConfig d (N - 1) | Y ⟨0, by omega⟩ ∈ A}).toReal| ≤
          Kt * Real.sqrt (deltaN d s N / N) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C₁, hC₁, hvar⟩ := wr13c2_pole_ind_variance hd hs0 hsd βp M
  obtain ⟨Cd, hCd0, hCd⟩ := wr13c2_insDefect_le hd hs0 hsd hβm βp M
  set K2 : ℝ := |Cd| * Real.exp |Cd| with hK2
  refine ⟨2 * Real.sqrt (2 * (C₁ * K2)), by positivity, fun ρ hρ hM β hβ1 hββp N hN x A hA => ?_⟩
  have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ1
  haveI := wr13a_isProb_density hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  have hconv := wr13a_conv_le_density hd1 hs0 hsd hρ hM
  haveI hP0 := wr13a_cavityLaw_isProb hs0 hconv hβ0.le N
  have hpos : 0 < N - 1 := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hn0 : (0 : ℝ) < ((N - 1 : ℕ) : ℝ) := by exact_mod_cast hpos
  have hnN : (N : ℝ) ≤ 2 * ((N - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  set P0 := HRS.Whole.cavityLaw d s N β μ with hP0def
  set A' : Set (EucConfig d (N - 1)) := {Y | Y ⟨0, hpos⟩ ∈ A} with hA'
  have hXm := wr13c2_X_meas hs0 N β x
  have hb := wr13c2_X_le_zero hs0 hβ0.le N x
  have hδ := wr13c_deltaN_pos_le_one hd1 hs0 hsd (by omega : 1 ≤ N)
  obtain ⟨-, -, -, hΔ⟩ := hCd ρ hρ hM β hβ1 hββp N hN x
  have hΔ' : cgf (wr13c2_X d s N β x) P0 1 - 2 * cgf (wr13c2_X d s N β x) P0 (1 / 2) ≤
      |Cd| * deltaN d s N := by
    have e1 := congrFun (wr13c2_insertionPressure_eq (d := d) (s := s) N β μ x) 1
    have e2 := congrFun (wr13c2_insertionPressure_eq (d := d) (s := s) N β μ x) (1 / 2)
    rw [e1, e2] at hΔ
    exact hΔ.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hδ.1.le)
  have hee := wr13c2_exp_sub_one_le _ |Cd| (deltaN d s N) hδ.1.le hδ.2 (abs_nonneg _) hΔ'
  have e1 : P0.tilted (wr13c2_X d s N β x) = HRS.Whole.poleLaw d s N β μ x 1 := by
    have := wr13c2_poleLaw_eq_tilted hs0 hconv hβ0.le zero_le_one N x
    simp only [one_mul] at this
    exact this.symm
  have e0 : P0 = HRS.Whole.poleLaw d s N β μ x 0 := (wr13c2_poleLaw_zero hs0 hconv hβ0.le N x).symm
  haveI hP1 := wr13c2_poleLaw_isProb hs0 hconv hβ0.le zero_le_one N x
  have htv := HRS.MarginalAux.EF.ef_tv (P := P0) hXm hb (wr13c2_measurable_fracIn (n := N - 1) hA)
    (fun Y => wr13c2_abs_fracIn_le hpos A Y)
  have hint1 : ∫ Y, wr13c2_fracIn A Y ∂(P0.tilted (wr13c2_X d s N β x)) =
      (HRS.Whole.poleLaw d s N β μ x 1 A').toReal := by
    rw [e1]
    exact wr13c2_integral_fracIn hpos hA _ (wr13b_poleLaw_exchangeable hs0 hconv hβ0.le zero_le_one N x)
  have hint0 : ∫ Y, wr13c2_fracIn A Y ∂P0 = (P0 A').toReal :=
    wr13c2_integral_fracIn hpos hA P0 (wr13c2_cavityLaw_exchangeable hs0 hconv hβ0.le N)
  have hV0 : Var[wr13c2_fracIn (n := N - 1) A; P0] ≤ C₁ / ((N - 1 : ℕ) : ℝ) := by
    rw [e0]
    exact hvar ρ hρ hM β hβ0 hββp N hN x 0 ⟨le_rfl, zero_le_one⟩ A hA
  have hV1 : Var[wr13c2_fracIn (n := N - 1) A; P0.tilted (wr13c2_X d s N β x)] ≤
      C₁ / ((N - 1 : ℕ) : ℝ) := by
    rw [e1]
    exact hvar ρ hρ hM β hβ0 hββp N hN x 1 ⟨zero_le_one, le_rfl⟩ A hA
  rw [hint1, hint0] at htv
  refine htv.trans ?_
  exact wr13c2_sqrt_chain (n := ((N - 1 : ℕ) : ℝ)) (N := (N : ℝ)) hn0 hN0 hnN hC₁.le
    (by positivity) hδ.1.le hV0 hV1 hee

end TVPole

/-! ### 6. Disintegration and the cavity total variation -/

section TVFinal

variable {d : ℕ} {s : ℝ}

theorem wr13c2_Q_isProb {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {Mg β : ℝ} (hs0 : 0 < s)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) (hβ : 0 ≤ β) {N : ℕ}
    (hN : 1 ≤ N) : IsProbabilityMeasure (HRS.Whole.modulatedGibbs (rieszKernel d s) N β μ) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [wr13a_modulatedGibbs_eq hs0 hconv hβ n]
  exact wr13a_tilt_isProb _ (wr13a_E_meas hs0 μ (β / ((n + 1 : ℕ) : ℝ)) β)
    (fun Y => wr13a_E_le hs0 hconv (div_nonneg hβ (Nat.cast_nonneg _)) hβ Y)

/-- Exact disintegration of the first marginal of `Q_N` over the pole laws:
`π_N(A) = ∫ P^{x,1}(Y_1 ∈ A) dπ_N(x)`. -/
theorem wr13c2_disint (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M) {β : ℝ} (hβ : 0 ≤ β)
    {N : ℕ} (hN : 2 ≤ N) {A : Set (Euc d)} (hA : MeasurableSet A) :
    HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs (rieszKernel d s) N β
        (HRS.Whole.withDensityReal ρ)) A =
      ∫⁻ x, HRS.Whole.poleLaw d s N β (HRS.Whole.withDensityReal ρ) x 1
          {Y : EucConfig d (N - 1) | Y ⟨0, by omega⟩ ∈ A}
        ∂(HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs (rieszKernel d s) N β
          (HRS.Whole.withDensityReal ρ))) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 0 < n := by omega
  set Q := HRS.Whole.modulatedGibbs (rieszKernel d s) (n + 1) β (HRS.Whole.withDensityReal ρ) with hQ
  set i0 : Fin n := ⟨0, hn⟩ with hi0
  set F : Euc d × EucConfig d n → ℝ≥0∞ := fun p => A.indicator (fun _ => (1 : ℝ≥0∞)) (p.2 i0) with hF
  have hFm : Measurable F :=
    (measurable_const.indicator hA).comp ((measurable_pi_apply i0).comp measurable_snd)
  have key := wr13a_cavity_disintegration_density hd hs0 hsd hρ hM hβ n F hFm
  have hex : HRS.External.Entropy.IsExchangeable Q :=
    HRS.Whole.modulatedGibbs_isExchangeable (rieszKernel d s) β _ (fun z => HRS.Whole.rieszKernel_neg z)
  have hLHS : ∫⁻ X : EucConfig d (n + 1), F (X 0, Fin.tail X) ∂Q =
      HRS.Whole.firstMarginal Q A := by
    have h1 : ∀ X : EucConfig d (n + 1), F (X 0, Fin.tail X) =
        ((fun X : EucConfig d (n + 1) => X (Fin.succ i0)) ⁻¹' A).indicator (fun _ => (1 : ℝ≥0∞)) X := by
      intro X
      by_cases h : X (Fin.succ i0) ∈ A <;> simp [F, Set.indicator, h, Fin.tail]
    simp_rw [h1]
    rw [lintegral_indicator_const ((measurable_pi_apply (Fin.succ i0)) hA), one_mul,
      ← Measure.map_apply (measurable_pi_apply (Fin.succ i0)) hA, wr13a_firstMarginal_def,
      hex.marginal_eq (Fin.succ i0) 0]
  rw [← hLHS, key]
  refine lintegral_congr fun x => ?_
  have h2 : ∀ Y : EucConfig d n, F (x, Y) =
      ({Y : EucConfig d n | Y i0 ∈ A}).indicator (fun _ => (1 : ℝ≥0∞)) Y := by
    intro Y
    by_cases h : Y i0 ∈ A <;> simp [F, Set.indicator, h]
  simp_rw [h2]
  have hm : MeasurableSet {Y : EucConfig d n | Y i0 ∈ A} := (measurable_pi_apply i0) hA
  rw [lintegral_indicator_const hm, one_mul]
  rfl

/-- **Cavity total variation** (`euc-cavity-TV`, last conjunct of `Bias.StaticInputConclusion`):
`‖π_N - ν_n‖_TV ≤ C √(δ_N/N)`, `π_N = Q_N^{(1)}`, `ν_n = (P_n^0)^{(1)}`. -/
theorem wr13c2_cavity_tv (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) {βm : ℝ} (hβm : 0 < βm)
    (βp M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ β : ℝ, βm ≤ β → β ≤ βp → ∀ N : ℕ, 2 ≤ N →
        HRS.Whole.tvDist
          (HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs (rieszKernel d s) N β
            (HRS.Whole.withDensityReal ρ)))
          (HRS.Whole.cavityMarginal d s N β (HRS.Whole.withDensityReal ρ)) ≤
          C * Real.sqrt (deltaN d s N / N) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Kt, hKt0, hKt⟩ := wr13c2_tv_pole hd hs0 hsd hβm βp M
  refine ⟨Kt, hKt0, fun ρ hρ hM β hβ1 hββp N hN => ?_⟩
  have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ1
  haveI := wr13a_isProb_density hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  have hconv := wr13a_conv_le_density hd1 hs0 hsd hρ hM
  haveI hP0 := wr13a_cavityLaw_isProb hs0 hconv hβ0.le N
  haveI hQ := wr13c2_Q_isProb hs0 hconv hβ0.le (by omega : 1 ≤ N)
  have hpos : 0 < N - 1 := by omega
  set π : Measure (Euc d) := HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs (rieszKernel d s) N β μ)
    with hπ
  haveI hπp : IsProbabilityMeasure π := by
    rw [hπ]
    unfold HRS.Whole.firstMarginal
    rw [dif_pos (by omega : 0 < N)]
    infer_instance
  set K : ℝ := Kt * Real.sqrt (deltaN d s N / N) with hK
  have hK0 : 0 ≤ K := by positivity
  unfold HRS.Whole.tvDist
  refine Real.iSup_le (fun E => ?_) (by positivity)
  obtain ⟨A, hA⟩ := E
  show |(π A).toReal - ((HRS.Whole.cavityMarginal d s N β μ) A).toReal| ≤ K
  set A' : Set (EucConfig d (N - 1)) := {Y | Y ⟨0, hpos⟩ ∈ A} with hA'
  have hν : HRS.Whole.cavityMarginal d s N β μ A = HRS.Whole.cavityLaw d s N β μ A' := by
    unfold HRS.Whole.cavityMarginal HRS.Whole.firstMarginal
    rw [dif_pos hpos, Measure.map_apply (measurable_pi_apply (⟨0, hpos⟩ : Fin (N - 1))) hA]
    rfl
  rw [hν]
  have hdis := wr13c2_disint hd hs0 hsd hρ hM hβ0.le hN hA
  have hpt : ∀ x : Euc d,
      HRS.Whole.poleLaw d s N β μ x 1 A' ≤ HRS.Whole.cavityLaw d s N β μ A' + ENNReal.ofReal K ∧
      HRS.Whole.cavityLaw d s N β μ A' ≤ HRS.Whole.poleLaw d s N β μ x 1 A' + ENNReal.ofReal K := by
    intro x
    haveI := wr13c2_poleLaw_isProb hs0 hconv hβ0.le zero_le_one N x
    exact wr13c2_ennreal_close (measure_ne_top _ _) (measure_ne_top _ _)
      (hKt ρ hρ hM β hβ1 hββp N hN x A hA)
  have hπA : π A ≤ HRS.Whole.cavityLaw d s N β μ A' + ENNReal.ofReal K := by
    rw [hπ, hdis]
    calc ∫⁻ x, HRS.Whole.poleLaw d s N β μ x 1 A' ∂π
        ≤ ∫⁻ _x, (HRS.Whole.cavityLaw d s N β μ A' + ENNReal.ofReal K) ∂π :=
          lintegral_mono fun x => (hpt x).1
      _ = _ := by simp
  have hAπ : HRS.Whole.cavityLaw d s N β μ A' ≤ π A + ENNReal.ofReal K := by
    rw [hπ, hdis]
    calc HRS.Whole.cavityLaw d s N β μ A'
        = ∫⁻ _x, HRS.Whole.cavityLaw d s N β μ A' ∂π := by simp
      _ ≤ ∫⁻ x, (HRS.Whole.poleLaw d s N β μ x 1 A' + ENNReal.ofReal K) ∂π :=
          lintegral_mono fun x => (hpt x).2
      _ = ∫⁻ x, HRS.Whole.poleLaw d s N β μ x 1 A' ∂π + ENNReal.ofReal K := by
          rw [lintegral_add_right _ measurable_const]
          simp
  exact wr13c2_real_close (measure_ne_top _ _) (measure_ne_top _ _) hK0 hπA hAπ

end TVFinal

end HRS.MS.Wr
