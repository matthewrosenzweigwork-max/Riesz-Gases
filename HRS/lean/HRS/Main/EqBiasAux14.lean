import HRS.Main.EqBiasAux13

/-!
# EQ-BIAS, S9e: the insertion defect from a per-time variance estimate
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ} {s c : ℝ}

open HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer HRS.CavResp

theorem eqbias_defect_time (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)
    {N : ℕ} (hN : 2 ≤ N) (x : Torus d) {q : ℝ} (hq : -1 < q) {R Bc B1 κq : ℝ} (hR : 0 ≤ R)
    (hBc : 0 ≤ Bc) (hB1 : 0 ≤ B1) (hκq : 0 ≤ κq)
    (hv : ∀ t ∈ Ioc (0 : ℝ) 1,
      MemLp (fun Y : Config d (N - 1) => ∑ i, gPlus d s c (x - Y i)) 2
          (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ∧
        |Var[fun Y : Config d (N - 1) => ∑ i, gPlus d s c (x - Y i);
            poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t] -
          ((N - 1 : ℕ) : ℝ) * R * (κq * t ^ q)| ≤ Bc + B1 * (κq * t ^ q)) :
    |insDefect (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x -
        (β / N) ^ 2 * (((N - 1 : ℕ) : ℝ) * R * κq) * (1 / ((q + 1) * (q + 2)))| ≤
      (β / N) ^ 2 * (Bc + B1 * κq / (q + 1)) := by
  obtain ⟨C, hC⟩ := partA hd hs0 hsd β hβ hρ c hc
  obtain ⟨-, -, hnn, hform, -⟩ := hC N hN x
  rw [← insertionDefect_eq_insDefect hd hs0 hsd c β hβ hρ hN x]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  refine eqbias_time_int (n := ((N - 1 : ℕ) : ℝ)) (v := fun t =>
    Var[fun Y : Config d (N - 1) => ∑ i, gPlus d s c (x - Y i);
      poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t]) hq
    (by positivity) (Nat.cast_nonneg _) hR hBc hB1 hκq hnn ?_ fun t ht => (hv t ht).2
  rw [hform]
  refine setLIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
  rw [critPole_eq_poleLaw hd hs0 hsd β hβ hρ hN x t]
  congr 1
  haveI := (isProbabilityMeasure_poleLaw hd hs0 hsd β hβ ρ hρ N hN x t
    ⟨ht.1.le, ht.2⟩).2
  exact (ENNReal.ofReal_toReal (hv t ht).1.evariance_lt_top.ne).symm

theorem eqbias_rest_sq_le (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (x : Torus d) {H : ℝ}
    (hH : 0 < H) :
    ∫ y, eqbias_rest d s c x H y ^ 2 ∂(withDensityReal ρ) ≤
      Real.exp 1 * ∫ y, gPlus d s c (x - y) ^ 2 *
        Real.exp (-((1 / H) * gPlus d s c (x - y))) ∂(withDensityReal ρ) := by
  haveI := isProbabilityMeasure_mu hρ
  have hf2m := eqbias_rest_measurable hd hs0 hsd (c := c) x H
  have hprops := eqbias_rest_props (s := s) (c := c) hc x H
  have hu : 0 < 1 / H := by positivity
  have hgm := measurable_gPlus hd hs0 hsd c
  have hgxm : Measurable fun y : Torus d => gPlus d s c (x - y) :=
    hgm.comp (measurable_const.sub measurable_id)
  have hi1 : Integrable (fun y => eqbias_rest d s c x H y ^ 2) (withDensityReal ρ) := by
    refine Integrable.mono' (integrable_const (H ^ 2)) (hf2m.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (hprops y).1 ((hprops y).2.2.1 hH.le) 2
  have hi2 : Integrable (fun y => gPlus d s c (x - y) ^ 2 *
      Real.exp (-((1 / H) * gPlus d s c (x - y)))) (withDensityReal ρ) := by
    have := eqbias_sqint hd hs0 hsd hρ (c := c) hgxm (fun y => hc _) x (fun y => le_rfl) hu
    simpa [neg_mul] using this
  rw [← integral_const_mul]
  refine integral_mono hi1 (hi2.const_mul _) fun y => ?_
  simp only
  have hg0 : 0 ≤ gPlus d s c (x - y) := hc _
  unfold eqbias_rest
  by_cases h : H < gPlus d s c (x - y)
  · rw [if_pos h]
    have : 0 ≤ Real.exp 1 * (gPlus d s c (x - y) ^ 2 * Real.exp (-((1 / H) * gPlus d s c (x - y)))) := by
      positivity
    simpa using this
  · rw [if_neg h]
    have hle : gPlus d s c (x - y) ≤ H := not_lt.1 h
    have h1 : (1 / H) * gPlus d s c (x - y) ≤ 1 := by
      rw [one_div, inv_mul_le_iff₀ hH]; linarith
    have h2 : 1 ≤ Real.exp 1 * Real.exp (-((1 / H) * gPlus d s c (x - y))) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
    calc gPlus d s c (x - y) ^ 2 = gPlus d s c (x - y) ^ 2 * 1 := by ring
      _ ≤ gPlus d s c (x - y) ^ 2 * (Real.exp 1 * Real.exp (-((1 / H) * gPlus d s c (x - y)))) :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = _ := by ring


theorem eqbias_pow_facts {β h₀ p : ℝ} (hβ : 0 < β) (hh₀ : 0 < h₀) (N : ℕ) (hN : 2 ≤ N) :
    ((N - 1 : ℕ) : ℝ) * (β / N) ^ p ≤ β ^ p * (N : ℝ) ^ (1 - p) ∧
    (β / N) ^ (2 : ℝ) * (h₀ / (β / N)) ^ (2 - p) = h₀ ^ (2 - p) * (β / N) ^ p ∧
    (β / N) * (h₀ / (β / N)) ^ (1 - p) = h₀ ^ (1 - p) * (β / N) ^ p ∧
    (β / N) ^ (2 : ℝ) * (β / N) ^ (p - 2) = (β / N) ^ p := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hl : 0 < β / N := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Real.div_rpow hβ.le hN0.le, Real.rpow_sub hN0, Real.rpow_one]
    have h1 : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
    have h2 : 0 ≤ β ^ p / (N : ℝ) ^ p := by positivity
    calc ((N - 1 : ℕ) : ℝ) * (β ^ p / (N : ℝ) ^ p) ≤ N * (β ^ p / (N : ℝ) ^ p) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = _ := by ring
  · rw [Real.div_rpow hh₀.le hl.le]
    have : (β / N) ^ (2 : ℝ) * ((β / N) ^ (2 - p))⁻¹ = (β / N) ^ p := by
      rw [← Real.rpow_neg hl.le, ← Real.rpow_add hl]; congr 1; ring
    calc (β / N) ^ (2 : ℝ) * (h₀ ^ (2 - p) / (β / N) ^ (2 - p))
        = h₀ ^ (2 - p) * ((β / N) ^ (2 : ℝ) * ((β / N) ^ (2 - p))⁻¹) := by ring
      _ = _ := by rw [this]
  · rw [Real.div_rpow hh₀.le hl.le]
    have : (β / N) * ((β / N) ^ (1 - p))⁻¹ = (β / N) ^ p := by
      have h1 : (β / N) * ((β / N) ^ (1 - p))⁻¹ = (β / N) ^ (1 : ℝ) * (β / N) ^ (-(1 - p)) := by
        rw [Real.rpow_neg hl.le, Real.rpow_one]
      rw [h1, ← Real.rpow_add hl]; congr 1; ring
    calc (β / N) * (h₀ ^ (1 - p) / (β / N) ^ (1 - p))
        = h₀ ^ (1 - p) * ((β / N) * ((β / N) ^ (1 - p))⁻¹) := by ring
      _ = _ := by rw [this]
  · rw [← Real.rpow_add hl]; congr 1; ring


set_option maxHeartbeats 3200000 in
theorem eqbias_D_estimate (hd : 2 ≤ d) (hs1 : (d : ℝ) / 2 < s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)
    (hc0 : 0 ≤ c) :
    ∃ Cψ Cv κ CJ Cm H₀ : ℝ, 0 ≤ Cψ ∧ 0 ≤ Cv ∧ 0 ≤ κ ∧ 0 ≤ CJ ∧ 0 ≤ Cm ∧ 0 < H₀ ∧
      ∀ (θ h₀ ε₁ ε' u₀ : ℝ) (N : ℕ) (hN : 2 ≤ N), 0 < θ → θ ≤ 1 → 0 < h₀ → 0 ≤ ε₁ → 0 ≤ ε' →
      (∀ u : ℝ, 0 < u → u ≤ u₀ → ∀ x : Torus d,
        |u ^ (2 - (d : ℝ) / s) *
            (∫ y, gPlus d s c (x - y) ^ 2 * Real.exp (-(u * gPlus d s c (x - y)))
              ∂(withDensityReal ρ)) -
          ρ x * (sphereArea d * Real.Gamma (2 - (d : ℝ) / s) / s)| ≤ ε') →
      β / N ≤ 1 → β / N ≤ u₀ → max H₀ 1 ≤ h₀ / (β / N) → Cψ * (ε₁ + 1 / (N : ℝ)) ≤ 1 →
      (∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y' : Torus d,
        Integrable (fun Y => |cavityField d s c β ρ N (⟨0, by omega⟩ : Fin (N - 1)) Y y'|)
          (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ∧
        ∫ Y, |cavityField d s c β ρ N (⟨0, by omega⟩ : Fin (N - 1)) Y y'|
          ∂(poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ≤ ε₁) →
      ∀ x : Torus d,
      |insDefect (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x -
          (β / N) ^ ((d : ℝ) / s) *
            (((N - 1 : ℕ) : ℝ) * (ρ x * (sphereArea d * Real.Gamma (2 - (d : ℝ) / s) / s))) *
            (1 / (((d : ℝ) / s) * ((d : ℝ) / s - 1)))| ≤
        (N : ℝ) ^ (1 - (d : ℝ) / s) *
          (β ^ ((d : ℝ) / s) * (ε' + (2 * θ + Cψ * (ε₁ + 1 / (N : ℝ))) * CJ) / ((d : ℝ) / s - 1) +
            β ^ ((d : ℝ) / s) * (((1 + 1 / θ) * Cv * Real.exp (β * c) + 1) * Real.exp 1 * CJ *
              h₀ ^ (2 - (d : ℝ) / s)) +
            (β ^ ((d : ℝ) / s)) ^ 2 * (N : ℝ) ^ (1 - (d : ℝ) / s) *
              ((1 + θ) * κ * Cm ^ 2 * (h₀ ^ (1 - (d : ℝ) / s)) ^ 2)) := by
  have hs0 : 0 ≤ s := (eqbias_p_range hs1 hsd hd).1.le
  obtain ⟨hs0', hp1, hp2⟩ := eqbias_p_range hs1 hsd hd
  haveI hμ := isProbabilityMeasure_mu hρ
  obtain ⟨Cψ, Cv, κ, hCψ, hCv, hκ, hvar⟩ := eqbias_var_F hd hs0 hsd hβ hρ hc hc0
  obtain ⟨CJ, hCJ, hJle⟩ := eqbias_J_le hd hs1 hsd hρ c hc
  obtain ⟨Cm, H₀, hCm, hH₀, hcore⟩ := eqbias_core_mass hd hs1 hsd hρ c hc
  refine ⟨Cψ, Cv, κ, CJ, Cm, H₀, hCψ, hCv, hκ, hCJ, hCm, hH₀, ?_⟩
  intro θ h₀ ε₁ ε' u₀ N hN hθ hθ1 hh₀ hε₁ hε' hJt hl1 hlu hH hεA hfield x
  set p : ℝ := (d : ℝ) / s with hp
  set lam : ℝ := β / N with hlam
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam0 : 0 < lam := by positivity
  set n : ℝ := ((N - 1 : ℕ) : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  set κ₂ : ℝ := sphereArea d * Real.Gamma (2 - p) / s with hκ₂
  have hκ₂0 : 0 ≤ κ₂ := by
    have h1 := HRS.StaticLimitsAux.sphereArea_pos hd
    have h2 : 0 < Real.Gamma (2 - p) := Real.Gamma_pos_of_pos (by linarith)
    positivity
  have hR0 : 0 ≤ ρ x * κ₂ := mul_nonneg (hρ.pos x).le hκ₂0
  set R : ℝ := ρ x * κ₂ with hR
  set H : ℝ := h₀ / lam with hHdef
  have hHge : max H₀ 1 ≤ H := hH
  have hH0 : 0 < H := by have := le_max_right H₀ 1; linarith
  have hH1 : 1 ≤ H := (le_max_right _ _).trans hHge
  have hHH₀ : H₀ ≤ H := (le_max_left _ _).trans hHge
  -- the two bounds on T and m
  have hT : ∫ y, eqbias_rest d s c x H y ^ 2 ∂(withDensityReal ρ) ≤
      Real.exp 1 * CJ * H ^ (2 - p) := by
    refine (eqbias_rest_sq_le hd hs0 hsd hρ hc x hH0).trans ?_
    have h1 : 1 / H ≤ 1 := by rw [div_le_one hH0]; exact hH1
    have h2 := hJle (1 / H) (by positivity) h1 x
    have h3 : (1 / H) ^ (p - 2) = H ^ (2 - p) := by
      rw [one_div, Real.inv_rpow hH0.le, ← Real.rpow_neg hH0.le]; congr 1; ring
    rw [h3] at h2
    calc Real.exp 1 * ∫ y, gPlus d s c (x - y) ^ 2 * Real.exp (-((1 / H) * gPlus d s c (x - y)))
          ∂(withDensityReal ρ) ≤ Real.exp 1 * (CJ * H ^ (2 - p)) :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos 1).le
      _ = _ := by ring
  have hm : ∫ y, eqbias_core d s c x H y ∂(withDensityReal ρ) ≤ Cm * H ^ (1 - p) := hcore H hHH₀ x
  have hm0 : 0 ≤ ∫ y, eqbias_core d s c x H y ∂(withDensityReal ρ) :=
    integral_nonneg fun y => (eqbias_core_le hc x H y).1
  have hT0 : 0 ≤ ∫ y, eqbias_rest d s c x H y ^ 2 ∂(withDensityReal ρ) :=
    integral_nonneg fun y => sq_nonneg _
  set T := ∫ y, eqbias_rest d s c x H y ^ 2 ∂(withDensityReal ρ) with hTdef
  set m := ∫ y, eqbias_core d s c x H y ∂(withDensityReal ρ) with hmdef
  set εA : ℝ := Cψ * (ε₁ + 1 / (N : ℝ)) with hεAdef
  have hεA0 : 0 ≤ εA := by positivity
  set Tb : ℝ := Real.exp 1 * CJ * H ^ (2 - p) with hTb
  set mb : ℝ := Cm * H ^ (1 - p) with hmb
  set C₁ : ℝ := (1 + 1 / θ) * Cv * Real.exp (β * c) + 1 with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  set Bc : ℝ := C₁ * n * Tb + (1 + θ) * n ^ 2 * (κ * mb ^ 2) with hBc
  set B1 : ℝ := n * (ε' + (2 * θ + εA) * CJ) with hB1
  have hBc0 : 0 ≤ Bc := by positivity
  have hB10 : 0 ≤ B1 := by positivity
  have hq : -1 < p - 2 := by linarith
  have hκq0 : 0 ≤ lam ^ (p - 2) := Real.rpow_nonneg hlam0.le _
  have hbound := eqbias_defect_time hd hs0 hsd hβ hρ hc hN x hq hR0 hBc0 hB10 hκq0 (fun t ht => by
    have ht0 : 0 < t := ht.1
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    obtain ⟨hmem, hbd⟩ := hvar N hN x t ht' ht0 ε₁ hε₁ (hfield x t ht') H hH0.le θ hθ
    refine ⟨hmem, ?_⟩
    have hu0 : 0 < t * lam := by positivity
    have hu1 : t * lam ≤ 1 := by nlinarith [ht.2]
    have huu : t * lam ≤ u₀ := by nlinarith [ht.2]
    have hJu := hJle (t * lam) hu0 hu1 x
    have hJc := hJt (t * lam) hu0 huu x
    set u := t * lam with hu
    set Jv := ∫ y, gPlus d s c (x - y) ^ 2 * Real.exp (-(u * gPlus d s c (x - y)))
      ∂(withDensityReal ρ) with hJv
    have hJeq : (∫ y, gPlus d s c (x - y) ^ 2 *
        Real.exp (-(t * lam) * gPlus d s c (x - y)) ∂(withDensityReal ρ)) = Jv := by
      simp only [hJv, neg_mul]
      rfl
    rw [hJeq] at hbd
    have hJv0 : 0 ≤ Jv := integral_nonneg fun y => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
    have hup0 : 0 < u ^ (p - 2) := Real.rpow_pos_of_pos hu0 _
    have hupp : u ^ (p - 2) * u ^ (2 - p) = 1 := by
      rw [← Real.rpow_add hu0]; simp
    have hJcl : |Jv - R * u ^ (p - 2)| ≤ ε' * u ^ (p - 2) := by
      have : Jv - R * u ^ (p - 2) = u ^ (p - 2) * (u ^ (2 - p) * Jv - R) := by
        have : u ^ (p - 2) * (u ^ (2 - p) * Jv) = Jv := by rw [← mul_assoc, hupp, one_mul]
        linarith [this]
      rw [this, abs_mul, abs_of_pos hup0, mul_comm]
      exact mul_le_mul_of_nonneg_right hJc hup0.le
    have hmul : lam ^ (p - 2) * t ^ (p - 2) = u ^ (p - 2) := by
      rw [hu, Real.mul_rpow ht0.le hlam0.le]; ring
    rw [hmul]
    -- bounding the error terms
    have hTm : T ≤ Tb := hT
    have hmm : m ≤ mb := hm
    have e1 : (1 + 1 / θ) * (Cv * n * (Real.exp (β * c) * T)) + n * T ≤ C₁ * n * Tb := by
      have : (1 + 1 / θ) * (Cv * n * (Real.exp (β * c) * T)) + n * T = C₁ * n * T := by
        simp only [hC₁]; ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hTm (by positivity)
    have e2 : θ * (n ^ 2 * (κ * m ^ 2)) + n ^ 2 * (κ * m ^ 2) ≤ (1 + θ) * n ^ 2 * (κ * mb ^ 2) := by
      have h1 : m ^ 2 ≤ mb ^ 2 := pow_le_pow_left₀ hm0 hmm 2
      have h2 : n ^ 2 * (κ * m ^ 2) ≤ n ^ 2 * (κ * mb ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hκ) (sq_nonneg _)
      nlinarith [h2, mul_nonneg hθ.le (sub_nonneg.2 h2)]
    have e3 : θ * (n * (1 + εA) * Jv) + n * (εA * Jv) ≤ n * (2 * θ + εA) * CJ * u ^ (p - 2) := by
      have h1 : θ * (n * (1 + εA) * Jv) + n * (εA * Jv) ≤ n * (2 * θ + εA) * Jv := by
        have : 0 ≤ n * Jv * (θ - θ * εA) := mul_nonneg (mul_nonneg hn0 hJv0)
          (by nlinarith [hεA0, hθ.le])
        nlinarith [this]
      calc _ ≤ n * (2 * θ + εA) * Jv := h1
        _ ≤ n * (2 * θ + εA) * (CJ * u ^ (p - 2)) :=
          mul_le_mul_of_nonneg_left hJu (by positivity)
        _ = _ := by ring
    have e4 : n * |Jv - R * u ^ (p - 2)| ≤ n * (ε' * u ^ (p - 2)) :=
      mul_le_mul_of_nonneg_left hJcl hn0
    have tri : |Var[fun Y : Config d (N - 1) => ∑ i, gPlus d s c (x - Y i);
          poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) lam β x t] - n * R * u ^ (p - 2)| ≤
        |Var[fun Y : Config d (N - 1) => ∑ i, gPlus d s c (x - Y i);
          poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) lam β x t] - n * Jv| +
          n * |Jv - R * u ^ (p - 2)| := by
      have h1 := abs_sub_le (Var[fun Y : Config d (N - 1) => ∑ i, gPlus d s c (x - Y i);
          poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) lam β x t]) (n * Jv)
          (n * R * u ^ (p - 2))
      have h2 : |n * Jv - n * R * u ^ (p - 2)| = n * |Jv - R * u ^ (p - 2)| := by
        rw [show n * Jv - n * R * u ^ (p - 2) = n * (Jv - R * u ^ (p - 2)) by ring, abs_mul,
          abs_of_nonneg hn0]
      linarith
    have : |Var[fun Y : Config d (N - 1) => ∑ i, gPlus d s c (x - Y i);
          poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) lam β x t] - n * R * u ^ (p - 2)| ≤
        Bc + B1 * u ^ (p - 2) := by
      have hB : Bc + B1 * u ^ (p - 2) = C₁ * n * Tb + (1 + θ) * n ^ 2 * (κ * mb ^ 2) +
          n * (2 * θ + εA) * CJ * u ^ (p - 2) + n * (ε' * u ^ (p - 2)) := by
        simp only [hBc, hB1]; ring
      rw [hB]
      linarith [tri, hbd, e1, e2, e3, e4]
    exact this)
  obtain ⟨hZ, hf2, hf3, hf4⟩ := eqbias_pow_facts (β := β) (h₀ := h₀) (p := p) hβ hh₀ N hN
  have hX0 : 0 ≤ β ^ p := Real.rpow_nonneg hβ.le _
  have hδ0 : 0 ≤ (N : ℝ) ^ (1 - p) := Real.rpow_nonneg hN0.le _
  have hlp0 : 0 ≤ lam ^ p := Real.rpow_nonneg hlam0.le _
  have hZ0 : 0 ≤ n * lam ^ p := mul_nonneg hn0 hlp0
  have hlam2 : lam ^ (2 : ℝ) = lam ^ 2 := Real.rpow_two lam
  rw [hlam2] at hf2 hf4
  have hf2' : lam ^ 2 * H ^ (2 - p) = h₀ ^ (2 - p) * lam ^ p := hf2
  have hf3' : lam * H ^ (1 - p) = h₀ ^ (1 - p) * lam ^ p := hf3
  have hf4' : lam ^ 2 * lam ^ (p - 2) = lam ^ p := hf4
  have hZ' : n * lam ^ p ≤ β ^ p * (N : ℝ) ^ (1 - p) := hZ
  -- identification of the main term
  have hq1 : p - 2 + 1 = p - 1 := by ring
  have hq2 : p - 2 + 2 = p := by ring
  rw [hq1, hq2] at hbound
  have hmain : lam ^ 2 * (n * R * lam ^ (p - 2)) * (1 / ((p - 1) * p)) =
      lam ^ p * (n * R) * (1 / (p * (p - 1))) := by
    have : lam ^ 2 * (n * R * lam ^ (p - 2)) = (lam ^ 2 * lam ^ (p - 2)) * (n * R) := by ring
    rw [this, hf4']; congr 1; ring
  rw [hmain] at hbound
  refine hbound.trans ?_
  -- bounding the error
  have hT1 : lam ^ 2 * Tb = Real.exp 1 * CJ * h₀ ^ (2 - p) * lam ^ p := by
    simp only [hTb]
    calc lam ^ 2 * (Real.exp 1 * CJ * H ^ (2 - p)) = Real.exp 1 * CJ * (lam ^ 2 * H ^ (2 - p)) := by ring
      _ = _ := by rw [hf2']; ring
  have hm1 : lam * mb = Cm * (h₀ ^ (1 - p) * lam ^ p) := by
    simp only [hmb]
    calc lam * (Cm * H ^ (1 - p)) = Cm * (lam * H ^ (1 - p)) := by ring
      _ = _ := by rw [hf3']
  have hterm1 : lam ^ 2 * (C₁ * n * Tb) = C₁ * Real.exp 1 * CJ * h₀ ^ (2 - p) * (n * lam ^ p) := by
    have : lam ^ 2 * (C₁ * n * Tb) = C₁ * n * (lam ^ 2 * Tb) := by ring
    rw [this, hT1]; ring
  have hterm2 : lam ^ 2 * ((1 + θ) * n ^ 2 * (κ * mb ^ 2)) =
      (1 + θ) * κ * Cm ^ 2 * (h₀ ^ (1 - p)) ^ 2 * (n * lam ^ p) ^ 2 := by
    have : lam ^ 2 * ((1 + θ) * n ^ 2 * (κ * mb ^ 2)) = (1 + θ) * n ^ 2 * κ * (lam * mb) ^ 2 := by ring
    rw [this, hm1]; ring
  have hterm3 : lam ^ 2 * (B1 * lam ^ (p - 2) / (p - 1)) =
      (n * lam ^ p) * (ε' + (2 * θ + εA) * CJ) / (p - 1) := by
    have : lam ^ 2 * (B1 * lam ^ (p - 2) / (p - 1)) = (lam ^ 2 * lam ^ (p - 2)) * B1 / (p - 1) := by ring
    rw [this, hf4']; simp only [hB1]; ring
  have hsplit : lam ^ 2 * (Bc + B1 * lam ^ (p - 2) / (p - 1)) =
      C₁ * Real.exp 1 * CJ * h₀ ^ (2 - p) * (n * lam ^ p) +
        (1 + θ) * κ * Cm ^ 2 * (h₀ ^ (1 - p)) ^ 2 * (n * lam ^ p) ^ 2 +
        (n * lam ^ p) * (ε' + (2 * θ + εA) * CJ) / (p - 1) := by
    have : lam ^ 2 * (Bc + B1 * lam ^ (p - 2) / (p - 1)) =
        lam ^ 2 * (C₁ * n * Tb) + lam ^ 2 * ((1 + θ) * n ^ 2 * (κ * mb ^ 2)) +
          lam ^ 2 * (B1 * lam ^ (p - 2) / (p - 1)) := by simp only [hBc]; ring
    rw [this, hterm1, hterm2, hterm3]
  rw [hsplit]
  have hε'' : 0 ≤ ε' + (2 * θ + εA) * CJ := by positivity
  have hp1' : 0 < p - 1 := by linarith
  have a1 : C₁ * Real.exp 1 * CJ * h₀ ^ (2 - p) * (n * lam ^ p) ≤
      C₁ * Real.exp 1 * CJ * h₀ ^ (2 - p) * (β ^ p * (N : ℝ) ^ (1 - p)) :=
    mul_le_mul_of_nonneg_left hZ' (by positivity)
  have a2 : (1 + θ) * κ * Cm ^ 2 * (h₀ ^ (1 - p)) ^ 2 * (n * lam ^ p) ^ 2 ≤
      (1 + θ) * κ * Cm ^ 2 * (h₀ ^ (1 - p)) ^ 2 * (β ^ p * (N : ℝ) ^ (1 - p)) ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hZ0 hZ' 2) (by positivity)
  have a3 : (n * lam ^ p) * (ε' + (2 * θ + εA) * CJ) / (p - 1) ≤
      (β ^ p * (N : ℝ) ^ (1 - p)) * (ε' + (2 * θ + εA) * CJ) / (p - 1) := by
    gcongr
  refine (add_le_add (add_le_add a1 a2) a3).trans (le_of_eq ?_)
  simp only [hC₁]
  ring


end Main

end HRS

end
