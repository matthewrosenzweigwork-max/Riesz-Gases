import HRS.Main.EqBiasAux14

/-!
# EQ-BIAS, S9f: asymptotics of the insertion defect (hypothesis `hD` of `eqbias_tendsto_of_D`)
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

theorem eqbias_small_rpow {a r η : ℝ} (ha : 0 ≤ a) (hr : 0 < r) (hη : 0 < η) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ a * h₀ ^ r ≤ η := by
  have hb : 0 < η / (a + 1) := by positivity
  refine ⟨(η / (a + 1)) ^ (1 / r), Real.rpow_pos_of_pos hb _, ?_⟩
  rw [← Real.rpow_mul hb.le, one_div, inv_mul_cancel₀ hr.ne', Real.rpow_one]
  calc a * (η / (a + 1)) = η * (a / (a + 1)) := by ring
    _ ≤ η * 1 := mul_le_mul_of_nonneg_left (div_le_one_of_le₀ (by linarith) (by linarith)) hη.le
    _ = η := mul_one η

theorem eqbias_c0_eq (hs0 : 0 < s) (hp1 : 1 < (d : ℝ) / s) :
    eqbias_c0 d s = (sphereArea d * Real.Gamma (2 - (d : ℝ) / s) / s) *
      (1 / (((d : ℝ) / s) * ((d : ℝ) / s - 1))) := by
  unfold eqbias_c0
  have h1 : (d : ℝ) / s - 1 ≠ 0 := by linarith
  have h2 : (d : ℝ) / s ≠ 0 := by linarith
  field_simp

theorem eqbias_gap {β : ℝ} (hβ : 0 < β) {p : ℝ} (N : ℕ) (hN : 2 ≤ N) :
    β ^ p * (N : ℝ) ^ (1 - p) - ((N - 1 : ℕ) : ℝ) * (β / N) ^ p =
      β ^ p * (N : ℝ) ^ (1 - p) / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rw [Real.div_rpow hβ.le hN0.le, Real.rpow_sub hN0, Real.rpow_one,
    Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
  have : (N : ℝ) ^ p ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
  field_simp
  ring

set_option maxHeartbeats 3200000 in
theorem eqbias_hD (hd : 2 ≤ d) (hs1 : (d : ℝ) / 2 < s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 2 ≤ N → ∀ x : Torus d,
      |insDefect (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x -
          deltaN d s N * (eqbias_c0 d s * β ^ ((d : ℝ) / s)) * ρ x| ≤ ε * deltaN d s N := by
  intro ε hε
  obtain ⟨hs0', hp1, hp2⟩ := eqbias_p_range hs1 hsd hd
  have hs0 : 0 ≤ s := hs0'.le
  obtain ⟨B, hB⟩ := periodicRiesz_ge (d := d) hd hs0 hsd
  obtain ⟨c, hc, hc0⟩ : ∃ c : ℝ, (∀ z, 0 ≤ periodicRiesz d s z + c) ∧ 0 ≤ c :=
    ⟨max B 0, fun z => by have := hB z; have := le_max_left B 0; linarith, le_max_right _ _⟩
  obtain ⟨Cψ, Cv, κ, CJ, Cm, H₀, hCψ, hCv, hκ, hCJ, hCm, hH₀, hall⟩ :=
    eqbias_D_estimate hd hs1 hsd hβ hρ hc hc0
  obtain ⟨Mρ, hMρ0, hMρ⟩ := exists_density_bound hρ
  set p : ℝ := (d : ℝ) / s with hp
  have hp1' : 0 < p - 1 := by linarith
  set X : ℝ := β ^ p with hX
  have hX0 : 0 ≤ X := Real.rpow_nonneg hβ.le _
  set κ₂ : ℝ := sphereArea d * Real.Gamma (2 - p) / s with hκ₂
  have hκ₂0 : 0 ≤ κ₂ := by
    have h1 := HRS.StaticLimitsAux.sphereArea_pos hd
    have h2 : 0 < Real.Gamma (2 - p) := Real.Gamma_pos_of_pos (by linarith)
    positivity
  have hc₀ : eqbias_c0 d s = κ₂ * (1 / (p * (p - 1))) := eqbias_c0_eq hs0' hp1
  have hc₀0 : 0 ≤ eqbias_c0 d s := by
    rw [hc₀]; have : 0 < p * (p - 1) := by positivity
    positivity
  set η : ℝ := ε / 6 with hη
  have hη0 : 0 < η := by positivity
  -- choice of the small parameters
  set θ : ℝ := min 1 (η * (p - 1) / (2 * (X * CJ + 1))) with hθ
  have hθ0 : 0 < θ := lt_min one_pos (by positivity)
  have hθ1 : θ ≤ 1 := min_le_left _ _
  have hθ2 : θ * (2 * (X * CJ + 1)) ≤ η * (p - 1) :=
    (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
  set ε' : ℝ := η * (p - 1) / (X + 1) with hε'
  have hε'0 : 0 < ε' := by positivity
  set εa : ℝ := min 1 (η * (p - 1) / (X * CJ + 1)) with hεa
  have hεa0 : 0 < εa := lt_min one_pos (by positivity)
  have hεa1 : εa ≤ 1 := min_le_left _ _
  have hεa2 : εa * (X * CJ + 1) ≤ η * (p - 1) :=
    (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
  set ε₁ : ℝ := εa / (2 * (Cψ + 1)) with hε₁
  have hε₁0 : 0 < ε₁ := by positivity
  set C₁ : ℝ := (1 + 1 / θ) * Cv * Real.exp (β * c) + 1 with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  obtain ⟨h₀, hh₀, hh₀η⟩ := eqbias_small_rpow (a := X * (C₁ * Real.exp 1 * CJ)) (r := 2 - p)
    (η := η) (by positivity) (by linarith) hη0
  obtain ⟨u₀, hu₀, hJ⟩ := eqbias_J_torus hd hs1 hsd hρ c hc ε' hε'0
  obtain ⟨N₁, hN₁⟩ := eqbias_field_small hd hs1 hsd hβ hρ c hc ε₁ hε₁0
  -- eventual conditions
  have hdel : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - p)) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (y := p - 1) (by linarith)).comp tendsto_natCast_atTop_atTop
    refine this.congr fun N => ?_
    simp only [Function.comp]; congr 1; ring
  have hinv : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hlamt : Tendsto (fun N : ℕ => β / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat β
  set K5 : ℝ := X ^ 2 * ((1 + θ) * κ * Cm ^ 2 * (h₀ ^ (1 - p)) ^ 2) with hK5
  have ev5 : ∀ᶠ N : ℕ in atTop, K5 * (N : ℝ) ^ (1 - p) ≤ η := by
    have := hdel.const_mul K5
    rw [mul_zero] at this
    exact (this.eventually (gt_mem_nhds hη0)).mono fun N hN => hN.le
  have ev6 : ∀ᶠ N : ℕ in atTop, Mρ * eqbias_c0 d s * X / (N : ℝ) ≤ η := by
    have := (hinv.const_mul (Mρ * eqbias_c0 d s * X))
    rw [mul_zero] at this
    refine (this.eventually (gt_mem_nhds hη0)).mono fun N hN => ?_
    have e : Mρ * eqbias_c0 d s * X / (N : ℝ) = Mρ * eqbias_c0 d s * X * (1 / (N : ℝ)) := by ring
    rw [e]; exact hN.le
  have ev4 : ∀ᶠ N : ℕ in atTop, 1 / (N : ℝ) < ε₁ := hinv.eventually (gt_mem_nhds hε₁0)
  have ev2 : ∀ᶠ N : ℕ in atTop, β / (N : ℝ) < min 1 u₀ :=
    hlamt.eventually (gt_mem_nhds (lt_min one_pos hu₀))
  have ev3 : ∀ᶠ N : ℕ in atTop, β * max H₀ 1 / h₀ ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (ev5.and (ev6.and (ev4.and (ev2.and (ev3.and
    (eventually_ge_atTop (max N₁ 2)))))))
  refine ⟨N₀, fun N hN₀' hN2 x => ?_⟩
  obtain ⟨h5, h6, h4, h2, h3, h1⟩ := hN₀ N hN₀'
  have hN1 : N₁ ≤ N := (le_max_left _ _).trans h1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam0 : 0 < β / N := by positivity
  have hl1 : β / N ≤ 1 := (h2.trans_le (min_le_left _ _)).le
  have hlu : β / N ≤ u₀ := (h2.trans_le (min_le_right _ _)).le
  have hH : max H₀ 1 ≤ h₀ / (β / N) := by
    rw [div_div_eq_mul_div, le_div_iff₀ hβ]
    rw [div_le_iff₀ hh₀] at h3
    nlinarith
  have hεA : Cψ * (ε₁ + 1 / (N : ℝ)) ≤ εa := by
    have : Cψ * (ε₁ + 1 / (N : ℝ)) ≤ Cψ * (2 * ε₁) :=
      mul_le_mul_of_nonneg_left (by linarith) hCψ
    refine this.trans ?_
    have : Cψ * (2 * ε₁) = εa * (Cψ / (Cψ + 1)) := by
      simp only [hε₁]; field_simp
    rw [this]
    calc εa * (Cψ / (Cψ + 1)) ≤ εa * 1 :=
          mul_le_mul_of_nonneg_left (div_le_one_of_le₀ (by linarith) (by linarith)) hεa0.le
      _ = εa := mul_one _
  have hJ' : ∀ u : ℝ, 0 < u → u ≤ u₀ → ∀ x : Torus d,
      |u ^ (2 - p) * (∫ y, gPlus d s c (x - y) ^ 2 * Real.exp (-(u * gPlus d s c (x - y)))
        ∂(withDensityReal ρ)) - ρ x * κ₂| ≤ ε' := fun u hu hu' x => hJ u hu hu' x
  have hmain := hall θ h₀ ε₁ ε' u₀ N hN2 hθ0 hθ1 hh₀ hε₁0.le hε'0.le hJ' hl1 hlu hH
    (hεA.trans hεa1) (fun x t ht y => hN₁ N hN2 hN1 x t ht y) x
  have hδ : deltaN d s N = (N : ℝ) ^ (1 - p) := eqbias_deltaN hs1 N
  rw [hδ]
  have hδ0 : 0 < (N : ℝ) ^ (1 - p) := Real.rpow_pos_of_pos hN0 _
  set δ : ℝ := (N : ℝ) ^ (1 - p) with hδdef
  have hgap := eqbias_gap (p := p) hβ N hN2
  rw [← hX, ← hδdef] at hgap
  set εA : ℝ := Cψ * (ε₁ + 1 / (N : ℝ)) with hεAdef
  have hεA0 : 0 ≤ εA := by positivity
  have hmain' : |insDefect (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x -
      (β / N) ^ p * (((N - 1 : ℕ) : ℝ) * (ρ x * κ₂)) * (1 / (p * (p - 1)))| ≤
      δ * (X * (ε' + (2 * θ + εA) * CJ) / (p - 1) + X * (C₁ * Real.exp 1 * CJ * h₀ ^ (2 - p)) +
        X ^ 2 * δ * ((1 + θ) * κ * Cm ^ 2 * (h₀ ^ (1 - p)) ^ 2)) := hmain
  have P1 : X * ε' / (p - 1) ≤ η := by
    rw [div_le_iff₀ hp1']
    calc X * ε' = η * (p - 1) * (X / (X + 1)) := by simp only [hε']; field_simp
      _ ≤ η * (p - 1) * 1 :=
          mul_le_mul_of_nonneg_left (div_le_one_of_le₀ (by linarith) (by positivity))
            (by positivity)
      _ = η * (p - 1) := mul_one _
  have P2 : 2 * θ * (X * CJ) / (p - 1) ≤ η := by
    rw [div_le_iff₀ hp1']
    nlinarith [mul_nonneg hθ0.le (mul_nonneg hX0 hCJ)]
  have P3 : εA * (X * CJ) / (p - 1) ≤ η := by
    rw [div_le_iff₀ hp1']
    have h' : εA * (X * CJ + 1) ≤ η * (p - 1) :=
      (mul_le_mul_of_nonneg_right hεA (by positivity)).trans hεa2
    nlinarith [mul_nonneg hεA0 (mul_nonneg hX0 hCJ)]
  have P4 : X * (C₁ * Real.exp 1 * CJ * h₀ ^ (2 - p)) ≤ η := by
    have : X * (C₁ * Real.exp 1 * CJ * h₀ ^ (2 - p)) = X * (C₁ * Real.exp 1 * CJ) * h₀ ^ (2 - p) := by
      ring
    rw [this]; exact hh₀η
  have P5 : X ^ 2 * δ * ((1 + θ) * κ * Cm ^ 2 * (h₀ ^ (1 - p)) ^ 2) ≤ η := by
    have : X ^ 2 * δ * ((1 + θ) * κ * Cm ^ 2 * (h₀ ^ (1 - p)) ^ 2) = K5 * δ := by
      simp only [hK5]; ring
    rw [this]; exact h5
  have hRel : X * (ε' + (2 * θ + εA) * CJ) / (p - 1) + X * (C₁ * Real.exp 1 * CJ * h₀ ^ (2 - p)) +
      X ^ 2 * δ * ((1 + θ) * κ * Cm ^ 2 * (h₀ ^ (1 - p)) ^ 2) ≤ 5 * η := by
    have : X * (ε' + (2 * θ + εA) * CJ) / (p - 1) =
        X * ε' / (p - 1) + 2 * θ * (X * CJ) / (p - 1) + εA * (X * CJ) / (p - 1) := by ring
    rw [this]
    linarith
  -- the discrepancy between the main term and the target
  set c₀ := eqbias_c0 d s with hc₀def
  have hmainE : (β / N) ^ p * (((N - 1 : ℕ) : ℝ) * (ρ x * κ₂)) * (1 / (p * (p - 1))) -
      δ * (c₀ * X) * ρ x = -(ρ x * c₀ * (X * δ / N)) := by
    rw [hc₀]
    linear_combination (-(ρ x * (κ₂ * (1 / (p * (p - 1)))))) * hgap
  have hdisc : |(β / N) ^ p * (((N - 1 : ℕ) : ℝ) * (ρ x * κ₂)) * (1 / (p * (p - 1))) -
      δ * (c₀ * X) * ρ x| ≤ δ * η := by
    rw [hmainE, abs_neg, abs_of_nonneg (mul_nonneg (mul_nonneg (hρ.pos x).le hc₀0)
      (div_nonneg (mul_nonneg hX0 hδ0.le) hN0.le))]
    have h6' : Mρ * c₀ * X / (N : ℝ) ≤ η := h6
    have hρx : ρ x ≤ Mρ := hMρ x
    calc ρ x * c₀ * (X * δ / N) = (ρ x * c₀ * X / N) * δ := by ring
      _ ≤ (Mρ * c₀ * X / N) * δ := by
          refine mul_le_mul_of_nonneg_right ?_ hδ0.le
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hρx hc₀0) hX0) hN0.le
      _ ≤ η * δ := mul_le_mul_of_nonneg_right h6' hδ0.le
      _ = δ * η := mul_comm _ _
  have hfin := abs_sub_le (insDefect (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x)
    ((β / N) ^ p * (((N - 1 : ℕ) : ℝ) * (ρ x * κ₂)) * (1 / (p * (p - 1))))
    (δ * (c₀ * X) * ρ x)
  have hmain'' := hmain'.trans (mul_le_mul_of_nonneg_left hRel hδ0.le)
  have : ε * δ = δ * (5 * η) + δ * η := by simp only [hη]; ring
  rw [this]
  linarith [hfin, hmain'', hdisc]


end Main

end HRS

end
