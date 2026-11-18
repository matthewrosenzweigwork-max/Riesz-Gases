import HRS.MS.MovEntAux12

/-!
# S6.6, packet P6 (part 7): data of the reference density `ρ₀` and of the class for the S.B.1 hypotheses

* `s66_gauss_data`: a probability density with a Gaussian bound has a bounded sup, a finite log moment (S3.1 class).
* `s66_regular_family`: the S6.4 weighted bounds (`K = 3`, `L = d+3`) give `IsRegularDensityW 3 Λ` for `ρ_t`, uniformly.
* `s66_lip_family`: the S6.3 velocity bound gives the Lipschitz bound `C₁ ε_* e^{-ct}` of the transport of the flow.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovEnt

open HRS.Whole

local notation "wd" => Whole.withDensityReal

variable {d : ℕ}

/-- A probability density with a Gaussian bound: log moment finite. -/
theorem s66_gauss_data (hd : 1 ≤ d) {ρ : Euc d → ℝ} (hρ : Whole.IsProbDensity ρ) {A cg : ℝ} (hA : 0 ≤ A)
    (hcg : 0 < cg) (hg : ∀ x, ρ x ≤ A * Real.exp (-cg * ‖x‖ ^ 2)) :
    ∃ L : ℝ, HasLogMoment (wd ρ) L := by
  haveI : IsProbabilityMeasure (wd ρ) := HRS.MS.Thm.cb_withDensityReal_isProb hρ
  set c₁ : ℝ := cg / 2 with hc₁
  have hc₁0 : 0 < c₁ := by positivity
  have hIgi : Integrable (fun x : Euc d => Real.exp (-c₁ * ‖x‖ ^ 2)) := s66_gauss_int hd hc₁0
  set Ig : ℝ := ∫ x : Euc d, Real.exp (-c₁ * ‖x‖ ^ 2) with hIg
  have hIg0 : 0 ≤ Ig := integral_nonneg fun x => (Real.exp_pos _).le
  set E : ℝ := A * Ig with hE
  have hE0 : 0 ≤ E := by positivity
  have hexp : ∫⁻ x, ENNReal.ofReal (Real.exp (c₁ * ‖x‖ ^ 2)) ∂(wd ρ) ≤ ENNReal.ofReal E := by
    have hmeas : Measurable fun x : Euc d => Real.exp (c₁ * ‖x‖ ^ 2) := by fun_prop
    unfold Whole.withDensityReal
    rw [lintegral_withDensity_eq_lintegral_mul (volume : Measure (Euc d))
      (f := fun x => ENNReal.ofReal (ρ x)) (g := fun x => ENNReal.ofReal (Real.exp (c₁ * ‖x‖ ^ 2)))
      (ENNReal.measurable_ofReal.comp hρ.measurable) (ENNReal.measurable_ofReal.comp hmeas)]
    have hpt : ∀ x : Euc d, ENNReal.ofReal (ρ x) * ENNReal.ofReal (Real.exp (c₁ * ‖x‖ ^ 2)) ≤
        ENNReal.ofReal (A * Real.exp (-c₁ * ‖x‖ ^ 2)) := by
      intro x
      rw [← ENNReal.ofReal_mul (hρ.nonneg x)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := hg x
      have h2 : Real.exp (c₁ * ‖x‖ ^ 2) * (A * Real.exp (-cg * ‖x‖ ^ 2)) =
          A * Real.exp (-c₁ * ‖x‖ ^ 2) := by
        have : Real.exp (c₁ * ‖x‖ ^ 2) * Real.exp (-cg * ‖x‖ ^ 2) = Real.exp (-c₁ * ‖x‖ ^ 2) := by
          rw [← Real.exp_add]; congr 1; rw [hc₁]; ring
        calc _ = A * (Real.exp (c₁ * ‖x‖ ^ 2) * Real.exp (-cg * ‖x‖ ^ 2)) := by ring
          _ = _ := by rw [this]
      calc ρ x * Real.exp (c₁ * ‖x‖ ^ 2) = Real.exp (c₁ * ‖x‖ ^ 2) * ρ x := mul_comm _ _
        _ ≤ Real.exp (c₁ * ‖x‖ ^ 2) * (A * Real.exp (-cg * ‖x‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = _ := h2
    refine (lintegral_mono hpt).trans ?_
    rw [← ofReal_integral_eq_lintegral_ofReal ((hIgi.const_mul A)) (ae_of_all _ fun x => by positivity)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    rw [integral_const_mul]
  refine ⟨(2 + 1 / (4 * c₁)) + E, ?_⟩
  have hmeas : Measurable fun x : Euc d => Real.exp (c₁ * ‖x‖ ^ 2) := by fun_prop
  have hfin : ∫⁻ x, ENNReal.ofReal (Real.exp (c₁ * ‖x‖ ^ 2)) ∂(wd ρ) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hexp
  have hint : Integrable (fun x : Euc d => Real.exp (c₁ * ‖x‖ ^ 2)) (wd ρ) :=
    (lintegral_ofReal_ne_top_iff_integrable hmeas.aestronglyMeasurable
      (ae_of_all _ fun x => (Real.exp_pos _).le)).1 hfin
  have hI : ∫ x, Real.exp (c₁ * ‖x‖ ^ 2) ∂(wd ρ) ≤ E := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => (Real.exp_pos _).le)
      hmeas.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hE0 hexp
  have hlogm : Measurable fun x : Euc d => Real.log (2 + ‖x‖) := by fun_prop
  have hdom : ∀ x : Euc d, |Real.log (2 + ‖x‖)| ≤ (2 + 1 / (4 * c₁)) + Real.exp (c₁ * ‖x‖ ^ 2) := by
    intro x
    have h0 : 0 ≤ Real.log (2 + ‖x‖) := Real.log_nonneg (by linarith [norm_nonneg x])
    rw [abs_of_nonneg h0]
    exact s66_log_le hc₁0 ‖x‖ (norm_nonneg x)
  have hli : Integrable (fun x : Euc d => Real.log (2 + ‖x‖)) (wd ρ) := by
    refine Integrable.mono' ((integrable_const ((2 + 1 / (4 * c₁) : ℝ))).add hint)
      hlogm.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs]
    exact hdom x
  refine ⟨hli, ?_⟩
  calc ∫ x, Real.log (2 + ‖x‖) ∂(wd ρ) ≤
        ∫ x, ((2 + 1 / (4 * c₁)) + Real.exp (c₁ * ‖x‖ ^ 2)) ∂(wd ρ) :=
        integral_mono hli ((integrable_const ((2 + 1 / (4 * c₁) : ℝ))).add hint)
          fun x => (le_abs_self _).trans (hdom x)
    _ = (2 + 1 / (4 * c₁)) + ∫ x, Real.exp (c₁ * ‖x‖ ^ 2) ∂(wd ρ) := by
        rw [integral_add (integrable_const ((2 + 1 / (4 * c₁) : ℝ))) hint]
        simp
    _ ≤ (2 + 1 / (4 * c₁)) + E := by linarith

/-- Uniform weighted derivative bounds of `ρ_t` give `IsRegularDensityW 3 Λ`. -/
theorem s66_regular_of_schwartz (hd : 2 ≤ d) {s q β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hq : 0 < q) (hβ : 0 < β)
    {ρ₀ : Euc d → ℝ} (hρ₀ : Whole.IsThermalEquilibrium d s q β ρ₀) (B₁ : ℝ) (hB₁ : 0 ≤ B₁) :
    ∃ Λ : ℝ, 1 ≤ Λ ∧ ∀ ρt : Euc d → ℝ, ContDiff ℝ 3 ρt →
      (∀ k : ℕ, k ≤ 3 → ∀ x : Euc d,
        movBracket x ^ (d + 3) * ‖iteratedFDeriv ℝ k (fun y => ρt y - ρ₀ y) x‖ ≤ B₁) →
      IsRegularDensityW 3 Λ ρt := by
  obtain ⟨hsm, hgs⟩ := HRS.MS.Mov0.mv0_hgauss hd hs0 hsd hq hβ hρ₀
  have hρ0c : ContDiff ℝ 3 ρ₀ := hsm.of_le (by first | exact_mod_cast (le_top : (3 : ℕ∞) ≤ ⊤) | exact WithTop.coe_le_coe.2 le_top | simp)
  have hex : ∀ k : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ x : Euc d,
      movBracket x ^ (d + 3) * ‖iteratedFDeriv ℝ k ρ₀ x‖ ≤ B := by
    intro k
    obtain ⟨C, c, hc, hC⟩ := hgs k
    obtain ⟨B, hB0, hB⟩ := s66_poly_gauss (d := d) hc (d + 3)
    refine ⟨|C| * B, by positivity, fun x => ?_⟩
    calc movBracket x ^ (d + 3) * ‖iteratedFDeriv ℝ k ρ₀ x‖
        ≤ movBracket x ^ (d + 3) * (C * Real.exp (-c * ‖x‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left (hC x) (by have := s66_one_le_bracket x; positivity)
      _ ≤ movBracket x ^ (d + 3) * (|C| * Real.exp (-c * ‖x‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le)
            (by have := s66_one_le_bracket x; positivity)
      _ = |C| * (movBracket x ^ (d + 3) * Real.exp (-c * ‖x‖ ^ 2)) := by ring
      _ ≤ |C| * B := mul_le_mul_of_nonneg_left (hB x) (abs_nonneg _)
  choose B0 hB00 hB0 using hex
  set Bs : ℝ := ∑ k ∈ Finset.range 4, B0 k with hBs
  have hBs0 : 0 ≤ Bs := Finset.sum_nonneg fun k _ => hB00 k
  have hk0 : ∀ k : ℕ, k ≤ 3 → B0 k ≤ Bs := fun k hk =>
    Finset.single_le_sum (f := B0) (fun i _ => hB00 i) (by simpa [Nat.lt_succ_iff] using hk)
  refine ⟨max 1 (5 * (Bs + B₁)), le_max_left _ _, fun ρt hct hb => ?_⟩
  refine s66_isRegular_of_bounds hct (B := Bs + B₁) ?_ (le_max_right _ _)
  intro k hk x
  have hsub : iteratedFDeriv ℝ k ρt x = iteratedFDeriv ℝ k (fun y => ρt y - ρ₀ y) x + iteratedFDeriv ℝ k ρ₀ x := by
    have := iteratedFDeriv_sub (𝕜 := ℝ) (i := k) (f := ρt) (g := ρ₀)
      (hct.of_le (by exact_mod_cast hk)) (hρ0c.of_le (by exact_mod_cast hk))
    rw [show (fun y => ρt y - ρ₀ y) = ρt - ρ₀ from rfl, this]
    simp
  have hn : ‖iteratedFDeriv ℝ k ρt x‖ ≤ ‖iteratedFDeriv ℝ k (fun y => ρt y - ρ₀ y) x‖ + ‖iteratedFDeriv ℝ k ρ₀ x‖ := by
    rw [hsub]; exact norm_add_le _ _
  have hbr : 0 ≤ movBracket x ^ (d + 3) := by have := s66_one_le_bracket x; positivity
  calc movBracket x ^ (d + 3) * ‖iteratedFDeriv ℝ k ρt x‖
      ≤ movBracket x ^ (d + 3) * (‖iteratedFDeriv ℝ k (fun y => ρt y - ρ₀ y) x‖ + ‖iteratedFDeriv ℝ k ρ₀ x‖) :=
        mul_le_mul_of_nonneg_left hn hbr
    _ = movBracket x ^ (d + 3) * ‖iteratedFDeriv ℝ k (fun y => ρt y - ρ₀ y) x‖ +
        movBracket x ^ (d + 3) * ‖iteratedFDeriv ℝ k ρ₀ x‖ := by ring
    _ ≤ B₁ + Bs := add_le_add (hb k hk x) ((hB0 k x).trans (hk0 k hk))
    _ = Bs + B₁ := by ring

/-- Lipschitz bound of the transport along the flow from the S6.3 velocity bound (`j = 1`). -/
theorem s66_lip_of_decay {s q β : ℝ} {ρ₀ : Euc d → ℝ} {m : ℕ} {εstar c C₁ : ℝ} (hK : 0 ≤ C₁ * εstar)
    {ρ : ℝ → Euc d → ℝ} (hdec : MovDecayBounds d s q β ρ₀ 1 m c C₁ εstar ρ) {t : ℝ} (ht : 0 ≤ t) :
    HasLipBoundW (mfeTransportW (quadraticGradientDyn d s q β) (ρ t)) (C₁ * εstar * Real.exp (-c * t)) := by
  obtain ⟨-, -, hcd, hcb⟩ := hdec t ht
  rw [s66_transport_eq]
  refine s66_lip_of_cb (by exact_mod_cast hcd) (by positivity) ?_
  exact le_trans le_add_self (by simpa using hcb)

end HRS.MS.MovEnt

end
