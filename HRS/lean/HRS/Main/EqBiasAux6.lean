import HRS.Main.EqBiasAux5

/-!
# EQ-BIAS, S8b: the abstract local asymptotics of `J(u) = ∫ γ² e^{-uγ} ρ̃`

For `γ(w) = ‖w‖^{-s} + O(1)` near `0`, bounded away from `0`, and a Lipschitz density `ρ̃`:
`u^{2-p} ∫_{cube} γ² e^{-uγ} ρ̃ → ρ̃(0) |𝕊^{d-1}| Γ(2-p)/s` as `u → 0` (`p = d/s ∈ (1,2)`),
with the threshold depending only on the constants (`eqbias_J_abstract`).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ}

open HRS.LocalDivAux

theorem eqbias_exp_sub_le {x y : ℝ} (h : y ≤ x) : Real.exp x - Real.exp y ≤ (x - y) * Real.exp x := by
  have h1 := Real.add_one_le_exp (y - x)
  have h2 : Real.exp (y - x) = Real.exp y / Real.exp x := by rw [Real.exp_sub]
  have hx := Real.exp_pos x
  rw [h2, le_div_iff₀ hx] at h1
  nlinarith

/-- Pointwise comparison of `G² e^{-uG}` and `A² e^{-uA}` for `|G - A| ≤ R`. -/
theorem eqbias_pt_diff {A G R u : ℝ} (hA : 0 ≤ A) (hG : 0 ≤ G) (hGA : |G - A| ≤ R) (hu0 : 0 < u)
    (hu1 : u ≤ 1) :
    |G ^ 2 * Real.exp (-(u * G)) - A ^ 2 * Real.exp (-(u * A))| ≤
      Real.exp R * Real.exp (-(u * A)) * (R * (2 * A + R) + A ^ 2 * (u * R)) := by
  have hR : 0 ≤ R := (abs_nonneg _).trans hGA
  have hGA' := abs_le.1 hGA
  have hexpG : Real.exp (-(u * G)) ≤ Real.exp R * Real.exp (-(u * A)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    nlinarith [hGA'.1, hGA'.2]
  have hexpA : Real.exp (-(u * A)) ≤ Real.exp R * Real.exp (-(u * A)) := by
    have := Real.one_le_exp hR
    nlinarith [Real.exp_pos (-(u * A))]
  have hdiff : |Real.exp (-(u * G)) - Real.exp (-(u * A))| ≤
      (u * R) * (Real.exp R * Real.exp (-(u * A))) := by
    have hd : |(-(u * G)) - (-(u * A))| ≤ u * R := by
      have : (-(u * G)) - (-(u * A)) = -(u * (G - A)) := by ring
      rw [this, abs_neg, abs_mul, abs_of_pos hu0]
      exact mul_le_mul_of_nonneg_left hGA hu0.le
    rcases le_total (-(u * A)) (-(u * G)) with h | h
    · have := eqbias_exp_sub_le h
      rw [abs_of_nonneg (by linarith [Real.exp_le_exp.2 h])]
      calc _ ≤ ((-(u * G)) - (-(u * A))) * Real.exp (-(u * G)) := this
        _ ≤ (u * R) * (Real.exp R * Real.exp (-(u * A))) := by
            refine mul_le_mul ((le_abs_self _).trans hd) hexpG (Real.exp_pos _).le (by positivity)
    · have := eqbias_exp_sub_le h
      rw [abs_sub_comm, abs_of_nonneg (by linarith [Real.exp_le_exp.2 h])]
      calc _ ≤ ((-(u * A)) - (-(u * G))) * Real.exp (-(u * A)) := this
        _ ≤ (u * R) * (Real.exp R * Real.exp (-(u * A))) := by
            refine mul_le_mul (by rw [abs_sub_comm] at hd; exact (le_abs_self _).trans hd) hexpA
              (Real.exp_pos _).le (by positivity)
  have hsq : |G ^ 2 - A ^ 2| ≤ R * (2 * A + R) := by
    have e : G ^ 2 - A ^ 2 = (G - A) * (G + A) := by ring
    rw [e, abs_mul]
    have : |G + A| ≤ 2 * A + R := by
      rw [abs_of_nonneg (by linarith)]
      linarith [hGA'.2]
    exact mul_le_mul hGA this (abs_nonneg _) hR
  have e2 : G ^ 2 * Real.exp (-(u * G)) - A ^ 2 * Real.exp (-(u * A)) =
      (G ^ 2 - A ^ 2) * Real.exp (-(u * G)) + A ^ 2 * (Real.exp (-(u * G)) - Real.exp (-(u * A))) :=
    by ring
  rw [e2]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg (sq_nonneg A)]
  have h1 : |G ^ 2 - A ^ 2| * Real.exp (-(u * G)) ≤
      (R * (2 * A + R)) * (Real.exp R * Real.exp (-(u * A))) :=
    mul_le_mul hsq hexpG (Real.exp_pos _).le (by positivity)
  have h2 : A ^ 2 * |Real.exp (-(u * G)) - Real.exp (-(u * A))| ≤
      A ^ 2 * ((u * R) * (Real.exp R * Real.exp (-(u * A)))) :=
    mul_le_mul_of_nonneg_left hdiff (sq_nonneg A)
  nlinarith

theorem eqbias_sq_exp_le {t : ℝ} (ht : 0 ≤ t) : t ^ 2 * Real.exp (-t) ≤ 2 := by
  have h := Real.quadratic_le_exp_of_nonneg ht
  have hpos := Real.exp_pos t
  have : Real.exp (-t) = (Real.exp t)⁻¹ := Real.exp_neg t
  rw [this, ← div_eq_mul_inv, div_le_iff₀ hpos]
  nlinarith [sq_nonneg t]

theorem eqbias_gam_exp_le {γ u : ℝ} (hγ : 0 ≤ γ) (hu : 0 < u) :
    γ ^ 2 * Real.exp (-(u * γ)) ≤ 2 / u ^ 2 := by
  have h := eqbias_sq_exp_le (mul_nonneg hu.le hγ)
  rw [le_div_iff₀ (by positivity)]
  nlinarith [h, sq_nonneg γ]

set_option maxHeartbeats 1600000 in
/-- The near-region estimate: `|∫_{0<|w|≤δ} (Φ - ρ̃(0)Ψ)| ≤ …` -/
theorem eqbias_near (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d)
    {δ R Λ L : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) (hR : 0 ≤ R) (hΛ : 0 ≤ Λ) (hL : 0 ≤ L)
    {γ ρt : Euc d → ℝ} (hγm : Measurable γ) (hρm : Measurable ρt) (hγ0 : ∀ w, 0 ≤ γ w)
    (hloc : ∀ w : Euc d, 0 < ‖w‖ → ‖w‖ ≤ δ → |γ w - ‖w‖ ^ (-s)| ≤ R)
    (hρb : ∀ w, 0 ≤ ρt w ∧ ρt w ≤ Λ) (hρL : ∀ w : Euc d, ‖w‖ ≤ δ → |ρt w - ρt 0| ≤ L * ‖w‖)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) {η : ℝ} (hη : 0 < η) :
    ‖∫ w in {w : Euc d | ‖w‖ ∈ Ioc 0 δ},
        (γ w ^ 2 * Real.exp (-(u * γ w)) * ρt w -
          ρt 0 * (‖w‖ ^ (-(2 * s)) * Real.exp (-(u * ‖w‖ ^ (-s)))))‖ ≤
      Λ * Real.exp R * (2 * R * (∫ w in {w : Euc d | ‖w‖ ∈ Ioc 0 δ}, ‖w‖ ^ (-s)) + R ^ 2) +
        (Λ * Real.exp R * R * u + L * η) *
          (∫ w in {w : Euc d | ‖w‖ ∈ Ioc 0 δ}, ‖w‖ ^ (-(2 * s)) * Real.exp (-(u * ‖w‖ ^ (-s)))) +
        2 * Λ * η ^ (-(2 * s)) := by
  set Nn : Set (Euc d) := {w : Euc d | ‖w‖ ∈ Ioc 0 δ} with hNn
  have hNm : MeasurableSet Nn := (measurableSet_Ioc).preimage measurable_norm
  have hNcube : Nn ⊆ cube d := fun w hw => cube_of_norm_le hδ4 hw.2
  have hvol : (volume : Measure (Euc d)) Nn ≤ 1 := by
    rw [← volume_cube (d := d)]; exact measure_mono hNcube
  have hvolr : (volume : Measure (Euc d)).real Nn ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top hvol
    simpa [Measure.real] using this
  have hNfin : (volume : Measure (Euc d)) Nn < ∞ := lt_of_le_of_lt hvol ENNReal.one_lt_top
  -- the power `a = ‖w‖^{-s}` is integrable on `Nn`
  have hAint : IntegrableOn (fun w : Euc d => ‖w‖ ^ (-s)) Nn := by
    have h := (HRS.L49.l49_radial_ind hd (ε := 0) (δ := δ) le_rfl hδ.le s (Or.inl (by
      have : (0 : ℝ) < d - s := by linarith
      linarith))).1
    refine (h.integrableOn (s := Nn)).congr_fun (fun w hw => ?_) hNm
    simp only [indicator_of_mem (show ‖w‖ ∈ Ioc 0 δ from hw)]
  set Ψ : Euc d → ℝ := fun w => ‖w‖ ^ (-(2 * s)) * Real.exp (-(u * ‖w‖ ^ (-s))) with hΨ
  have hΨm : Measurable Ψ := by
    refine (measurable_norm.pow_const _).mul ?_
    exact Real.measurable_exp.comp (((measurable_norm.pow_const _).const_mul u).neg)
  have hA2 : ∀ w : Euc d, ‖w‖ ^ (-(2 * s)) = (‖w‖ ^ (-s)) ^ 2 := by
    intro w
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg w)]
    congr 1; push_cast; ring
  have hΨb : ∀ w, Ψ w ≤ 2 / u ^ 2 := by
    intro w
    have h0 : 0 ≤ ‖w‖ ^ (-s) := Real.rpow_nonneg (norm_nonneg w) _
    simp only [hΨ]
    rw [hA2]
    exact eqbias_gam_exp_le h0 hu0
  have hΨ0 : ∀ w, 0 ≤ Ψ w := fun w => mul_nonneg (Real.rpow_nonneg (norm_nonneg w) _) (Real.exp_pos _).le
  have hΨint : IntegrableOn Ψ Nn :=
    Measure.integrableOn_of_bounded (M := 2 / u ^ 2) hNfin.ne hΨm.aestronglyMeasurable
      (Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hΨ0 w)]; exact hΨb w)
  -- the dominating function
  set c₁ : ℝ := Λ * Real.exp R * (2 * R) with hc₁
  set c₂ : ℝ := Λ * Real.exp R * R * u + L * η with hc₂
  set c₃ : ℝ := Λ * Real.exp R * R ^ 2 + 2 * Λ * η ^ (-(2 * s)) with hc₃
  have hc₁0 : 0 ≤ c₁ := by positivity
  have hc₂0 : 0 ≤ c₂ := by positivity
  have hc₃0 : 0 ≤ c₃ := by positivity
  set D : Euc d → ℝ := fun w => c₁ * ‖w‖ ^ (-s) + c₂ * Ψ w + c₃ with hD
  have hDint : IntegrableOn D Nn :=
    Integrable.add (Integrable.add (Integrable.const_mul hAint c₁) (Integrable.const_mul hΨint c₂))
      (integrableOn_const hNfin.ne)
  have hpt : ∀ w ∈ Nn, ‖γ w ^ 2 * Real.exp (-(u * γ w)) * ρt w - ρt 0 * Ψ w‖ ≤ D w := by
    intro w hw
    have hw0 : 0 < ‖w‖ := hw.1
    have hwδ : ‖w‖ ≤ δ := hw.2
    set A : ℝ := ‖w‖ ^ (-s) with hAdef
    have hA0 : 0 ≤ A := Real.rpow_nonneg (norm_nonneg w) _
    have hdiff := eqbias_pt_diff hA0 (hγ0 w) (hloc w hw0 hwδ) hu0 hu1
    have hΨA : Ψ w = A ^ 2 * Real.exp (-(u * A)) := by
      simp only [hΨ]; rw [hA2]
    have hexpA : Real.exp (-(u * A)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    have e : γ w ^ 2 * Real.exp (-(u * γ w)) * ρt w - ρt 0 * Ψ w =
        (γ w ^ 2 * Real.exp (-(u * γ w)) - A ^ 2 * Real.exp (-(u * A))) * ρt w +
          Ψ w * (ρt w - ρt 0) := by
      rw [hΨA]; ring
    rw [e, Real.norm_eq_abs]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have hρw := hρb w
    have hρ0 := hρb 0
    have h1 : |γ w ^ 2 * Real.exp (-(u * γ w)) - A ^ 2 * Real.exp (-(u * A))| * |ρt w| ≤
        Real.exp R * (R * (2 * A + R) + u * R * Ψ w) * Λ := by
      rw [abs_of_nonneg hρw.1]
      refine mul_le_mul ?_ hρw.2 hρw.1 (by positivity)
      refine hdiff.trans ?_
      have hexpR := Real.exp_pos R
      rw [hΨA]
      have : Real.exp (-(u * A)) * (R * (2 * A + R) + A ^ 2 * (u * R)) ≤
          R * (2 * A + R) + u * R * (A ^ 2 * Real.exp (-(u * A))) := by
        have h2 : 0 ≤ R * (2 * A + R) := by positivity
        have h3 : 0 ≤ A ^ 2 * (u * R) := by positivity
        nlinarith [mul_le_mul_of_nonneg_right hexpA h2, Real.exp_pos (-(u * A))]
      calc Real.exp R * Real.exp (-(u * A)) * (R * (2 * A + R) + A ^ 2 * (u * R))
          = Real.exp R * (Real.exp (-(u * A)) * (R * (2 * A + R) + A ^ 2 * (u * R))) := by ring
        _ ≤ Real.exp R * (R * (2 * A + R) + u * R * (A ^ 2 * Real.exp (-(u * A)))) :=
            mul_le_mul_of_nonneg_left this hexpR.le
    have h2 : |Ψ w| * |ρt w - ρt 0| ≤ L * η * Ψ w + 2 * Λ * η ^ (-(2 * s)) := by
      rw [abs_of_nonneg (hΨ0 w)]
      by_cases hwη : ‖w‖ ≤ η
      · have := hρL w hwδ
        have h4 : |ρt w - ρt 0| ≤ L * η :=
          this.trans (mul_le_mul_of_nonneg_left hwη hL)
        have h5 : Ψ w * |ρt w - ρt 0| ≤ Ψ w * (L * η) :=
          mul_le_mul_of_nonneg_left h4 (hΨ0 w)
        have h6 : 0 ≤ 2 * Λ * η ^ (-(2 * s)) := by positivity
        nlinarith
      · push_neg at hwη
        have h4 : |ρt w - ρt 0| ≤ 2 * Λ := by
          rw [abs_le]; constructor <;> linarith [hρw.1, hρw.2, hρ0.1, hρ0.2]
        have h5 : Ψ w ≤ η ^ (-(2 * s)) := by
          have h7 : Ψ w ≤ ‖w‖ ^ (-(2 * s)) := by
            simp only [hΨ]
            have : Real.exp (-(u * ‖w‖ ^ (-s))) ≤ 1 := by
              rw [Real.exp_le_one_iff]
              have := Real.rpow_nonneg (norm_nonneg w) (-s)
              nlinarith
            calc ‖w‖ ^ (-(2 * s)) * Real.exp (-(u * ‖w‖ ^ (-s))) ≤ ‖w‖ ^ (-(2 * s)) * 1 :=
                  mul_le_mul_of_nonneg_left this (Real.rpow_nonneg (norm_nonneg w) _)
              _ = _ := mul_one _
          exact h7.trans (Real.rpow_le_rpow_of_nonpos hη hwη.le (by linarith))
        have h6 : Ψ w * |ρt w - ρt 0| ≤ η ^ (-(2 * s)) * (2 * Λ) :=
          mul_le_mul h5 h4 (abs_nonneg _) (Real.rpow_nonneg hη.le _)
        have h8 : 0 ≤ L * η * Ψ w := by positivity
        linarith
    simp only [hD, hc₁, hc₂, hc₃]
    linarith [h1, h2]
  have hnorm := norm_integral_le_of_norm_le (μ := volume.restrict Nn)
    (f := fun w => γ w ^ 2 * Real.exp (-(u * γ w)) * ρt w - ρt 0 * Ψ w) hDint
    (ae_restrict_of_forall_mem hNm hpt)
  refine hnorm.trans ?_
  -- evaluate `∫ D`
  have hA0 : ∀ w : Euc d, 0 ≤ ‖w‖ ^ (-s) := fun w => Real.rpow_nonneg (norm_nonneg w) _
  have e1 : ∫ w in Nn, D w = c₁ * (∫ w in Nn, ‖w‖ ^ (-s)) + c₂ * (∫ w in Nn, Ψ w) +
      c₃ * (volume : Measure (Euc d)).real Nn := by
    simp only [hD]
    have hI1 : IntegrableOn (fun w : Euc d => c₁ * ‖w‖ ^ (-s)) Nn := Integrable.const_mul hAint c₁
    have hI2 : IntegrableOn (fun w : Euc d => c₂ * Ψ w) Nn := Integrable.const_mul hΨint c₂
    have hI12 : IntegrableOn (fun w : Euc d => c₁ * ‖w‖ ^ (-s) + c₂ * Ψ w) Nn := Integrable.add hI1 hI2
    have hI3 : IntegrableOn (fun _ : Euc d => c₃) Nn := integrableOn_const hNfin.ne
    have ea := integral_add (μ := volume.restrict Nn) hI12 hI3
    have eb := integral_add (μ := volume.restrict Nn) hI1 hI2
    rw [ea, eb, integral_const_mul, integral_const_mul, setIntegral_const, smul_eq_mul]
    ring
  rw [e1]
  have hK : 0 ≤ ∫ w in Nn, ‖w‖ ^ (-s) := setIntegral_nonneg hNm fun w _ => hA0 w
  have hM : 0 ≤ ∫ w in Nn, Ψ w := setIntegral_nonneg hNm fun w _ => hΨ0 w
  have : c₃ * (volume : Measure (Euc d)).real Nn ≤ c₃ := by
    nlinarith [measureReal_nonneg (μ := (volume : Measure (Euc d))) (s := Nn)]
  have e2 : c₁ * (∫ w in Nn, ‖w‖ ^ (-s)) + c₂ * (∫ w in Nn, Ψ w) + c₃ =
      Λ * Real.exp R * (2 * R * (∫ w in Nn, ‖w‖ ^ (-s)) + R ^ 2) +
        (Λ * Real.exp R * R * u + L * η) * (∫ w in Nn, Ψ w) + 2 * Λ * η ^ (-(2 * s)) := by
    simp only [hc₁, hc₂, hc₃]; ring
  linarith [e2]

set_option maxHeartbeats 3200000 in
/-- The abstract local asymptotics of `J(u) = ∫_{cube} γ² e^{-uγ} ρ̃` (`p = d/s ∈ (1,2)`),
uniform in `γ, ρ̃` satisfying the hypotheses with the given constants. -/
theorem eqbias_J_abstract (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d)
    (hp2 : (d : ℝ) / s < 2) {δ R G₀ Λ L : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) (hR : 0 ≤ R)
    (hG₀ : 0 ≤ G₀) (hΛ : 0 ≤ Λ) (hL : 0 ≤ L) :
    ∀ ε : ℝ, 0 < ε → ∃ u₀ : ℝ, 0 < u₀ ∧ ∀ (γ ρt : Euc d → ℝ), Measurable γ → Measurable ρt →
      (∀ w, 0 ≤ γ w) → (∀ w : Euc d, 0 < ‖w‖ → ‖w‖ ≤ δ → |γ w - ‖w‖ ^ (-s)| ≤ R) →
      (∀ w ∈ cube d, δ < ‖w‖ → γ w ≤ G₀) → (∀ w, 0 ≤ ρt w ∧ ρt w ≤ Λ) →
      (∀ w : Euc d, ‖w‖ ≤ δ → |ρt w - ρt 0| ≤ L * ‖w‖) →
      ∀ u : ℝ, 0 < u → u ≤ u₀ →
        |u ^ (2 - (d : ℝ) / s) * (∫ w in cube d, γ w ^ 2 * Real.exp (-(u * γ w)) * ρt w) -
            ρt 0 * (ballConst d * Real.Gamma (2 - (d : ℝ) / s) / s)| ≤ ε := by
  intro ε hε
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hp1 : 1 < (d : ℝ) / s := by rw [lt_div_iff₀ hs0]; linarith
  set p : ℝ := (d : ℝ) / s with hp
  set P : ℝ := 2 - p with hP
  have hP0 : 0 < P := by rw [hP]; linarith
  have hP1 : P < 1 := by rw [hP]; linarith
  have hΓ : 0 < Real.Gamma P := Real.Gamma_pos_of_pos hP0
  have hbc : 0 ≤ ballConst d := ballConst_nonneg
  set bc : ℝ := ballConst d with hbcdef
  set κ : ℝ := bc * Real.Gamma P / s with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set Nn : Set (Euc d) := {w : Euc d | ‖w‖ ∈ Ioc 0 δ} with hNn
  have hNm : MeasurableSet Nn := (measurableSet_Ioc).preimage measurable_norm
  have hNcube : Nn ⊆ cube d := fun w hw => cube_of_norm_le hδ4 hw.2
  set K₁ : ℝ := ∫ w in Nn, ‖w‖ ^ (-s) with hK₁
  have hK₁0 : 0 ≤ K₁ := setIntegral_nonneg hNm fun w _ => Real.rpow_nonneg (norm_nonneg w) _
  set I₀m : ℝ := (δ ^ (-s)) ^ P / P with hI₀m
  have hI₀m0 : 0 ≤ I₀m := by positivity
  set η : ℝ := ε / (2 * (L * κ + 1)) with hη
  have hη0 : 0 < η := by positivity
  set C₁ : ℝ := Λ * Real.exp R * (2 * R * K₁ + R ^ 2) + 2 * Λ * η ^ (-(2 * s)) + G₀ ^ 2 * Λ with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  set C₃ : ℝ := C₁ + Λ * (bc / s) * I₀m + Λ * Real.exp R * R * κ with hC₃
  have hC₃0 : 0 ≤ C₃ := by positivity
  set u₀ : ℝ := min 1 ((ε / (2 * (C₃ + 1))) ^ (1 / P)) with hu₀
  have hu₀pos : 0 < u₀ := lt_min one_pos (Real.rpow_pos_of_pos (by positivity) _)
  refine ⟨u₀, hu₀pos, ?_⟩
  intro γ ρt hγm hρm hγ0 hloc hfar hρb hρL u hu0 hu
  have hu1 : u ≤ 1 := hu.trans (min_le_left _ _)
  have huP : u ^ P ≤ ε / (2 * (C₃ + 1)) := by
    have h1 : u ≤ (ε / (2 * (C₃ + 1))) ^ (1 / P) := hu.trans (min_le_right _ _)
    have h2 : u ^ P ≤ ((ε / (2 * (C₃ + 1))) ^ (1 / P)) ^ P :=
      Real.rpow_le_rpow hu0.le h1 hP0.le
    rwa [← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ hP0.ne', Real.rpow_one] at h2
  have huuP : u ≤ u ^ P := by
    have := Real.rpow_le_rpow_of_exponent_ge hu0 hu1 hP1.le
    simpa using this
  have huP0 : 0 < u ^ P := Real.rpow_pos_of_pos hu0 _
  -- the model integral
  obtain ⟨I₀, hI0, hI1, hmodel⟩ := eqbias_model hd hs0 hsd hp2 hδ hu0
  set Ψ : Euc d → ℝ := fun w => ‖w‖ ^ (-(2 * s)) * Real.exp (-(u * ‖w‖ ^ (-s))) with hΨ
  have hΨm : Measurable Ψ := by
    refine (measurable_norm.pow_const _).mul ?_
    exact Real.measurable_exp.comp (((measurable_norm.pow_const _).const_mul u).neg)
  have hA2 : ∀ w : Euc d, ‖w‖ ^ (-(2 * s)) = (‖w‖ ^ (-s)) ^ 2 := by
    intro w
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg w)]
    congr 1; push_cast; ring
  have hΨb : ∀ w, Ψ w ≤ 2 / u ^ 2 := by
    intro w
    have h0 : 0 ≤ ‖w‖ ^ (-s) := Real.rpow_nonneg (norm_nonneg w) _
    simp only [hΨ]
    rw [hA2]
    exact eqbias_gam_exp_le h0 hu0
  have hΨ0 : ∀ w, 0 ≤ Ψ w :=
    fun w => mul_nonneg (Real.rpow_nonneg (norm_nonneg w) _) (Real.exp_pos _).le
  have hM : ∫ w in Nn, Ψ w = bc / s * ((1 / u) ^ P * Real.Gamma P - I₀) := by
    rw [← hmodel, ← integral_indicator hNm]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    show Nn.indicator Ψ w = (Ioc (0 : ℝ) δ).indicator
      (fun r : ℝ => r ^ (-(2 * s)) * Real.exp (-(u * r ^ (-s)))) ‖w‖
    by_cases hw : ‖w‖ ∈ Ioc 0 δ
    · rw [indicator_of_mem (show w ∈ Nn from hw), indicator_of_mem hw]
    · rw [indicator_of_notMem (show w ∉ Nn from hw), indicator_of_notMem hw]
  have huPM : u ^ P * ∫ w in Nn, Ψ w = bc / s * (Real.Gamma P - u ^ P * I₀) := by
    rw [hM]
    have : u ^ P * (1 / u) ^ P = 1 := by
      rw [← Real.mul_rpow hu0.le (by positivity), mul_one_div_cancel hu0.ne', Real.one_rpow]
    calc u ^ P * (bc / s * ((1 / u) ^ P * Real.Gamma P - I₀))
        = bc / s * ((u ^ P * (1 / u) ^ P) * Real.Gamma P - u ^ P * I₀) := by ring
      _ = _ := by rw [this]; ring
  have hMnn : 0 ≤ ∫ w in Nn, Ψ w := setIntegral_nonneg hNm fun w _ => hΨ0 w
  have hkey : bc / s * (Real.Gamma P - u ^ P * I₀) = κ - bc / s * (u ^ P * I₀) := by
    rw [hκ]; ring
  have huPM_le : u ^ P * ∫ w in Nn, Ψ w ≤ κ := by
    rw [huPM, hkey]
    have : 0 ≤ bc / s * (u ^ P * I₀) := by positivity
    linarith
  have huPM_ge : κ - bc / s * (u ^ P * I₀m) ≤ u ^ P * ∫ w in Nn, Ψ w := by
    rw [huPM, hkey]
    have h1 : u ^ P * I₀ ≤ u ^ P * I₀m := mul_le_mul_of_nonneg_left hI1 huP0.le
    have h2 : 0 ≤ bc / s := by positivity
    have := mul_le_mul_of_nonneg_left h1 h2
    linarith
  -- the decomposition of the cube integral
  set Φ : Euc d → ℝ := fun w => γ w ^ 2 * Real.exp (-(u * γ w)) * ρt w with hΦ
  have hΦm : Measurable Φ := by
    refine ((hγm.pow_const 2).mul ?_).mul hρm
    exact Real.measurable_exp.comp ((hγm.const_mul u).neg)
  have hΦb : ∀ w, |Φ w| ≤ 2 * Λ / u ^ 2 := by
    intro w
    have h0 := hρb w
    simp only [hΦ]
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) h0.1)]
    have h1 := eqbias_gam_exp_le (hγ0 w) hu0
    calc γ w ^ 2 * Real.exp (-(u * γ w)) * ρt w ≤ (2 / u ^ 2) * Λ :=
          mul_le_mul h1 h0.2 h0.1 (by positivity)
      _ = _ := by ring
  have hΦcube : IntegrableOn Φ (cube d) := integrableOn_cube_bdd hΦm (fun w _ => hΦb w)
  have hΦN : IntegrableOn Φ Nn := hΦcube.mono_set hNcube
  have hΨN : IntegrableOn Ψ Nn :=
    (integrableOn_cube_bdd hΨm (C := 2 / u ^ 2) (fun w _ => by
      rw [abs_of_nonneg (hΨ0 w)]; exact hΨb w)).mono_set hNcube
  have hsplit := setIntegral_diff hNm hΦcube hNcube
  have hfar_b : ‖∫ w in cube d \ Nn, Φ w‖ ≤ G₀ ^ 2 * Λ := by
    have := norm_setIntegral_le_of_norm_le_const_ae' (μ := (volume : Measure (Euc d)))
      (s := cube d \ Nn) (f := Φ) (C := G₀ ^ 2 * Λ)
      (lt_of_le_of_lt (measure_mono (Set.diff_subset.trans (le_of_eq rfl)) |>.trans
        (le_of_eq volume_cube)) ENNReal.one_lt_top) ?_
    · refine this.trans ?_
      have h1 : (volume : Measure (Euc d)).real (cube d \ Nn) ≤ 1 := by
        have : (volume : Measure (Euc d)) (cube d \ Nn) ≤ 1 :=
          (measure_mono Set.diff_subset).trans (le_of_eq volume_cube)
        have := ENNReal.toReal_mono ENNReal.one_ne_top this
        simpa [Measure.real] using this
      have h2 : 0 ≤ G₀ ^ 2 * Λ := by positivity
      nlinarith [measureReal_nonneg (μ := (volume : Measure (Euc d))) (s := cube d \ Nn)]
    · have hne : ∀ᵐ w ∂(volume : Measure (Euc d)), w ≠ 0 := by
        rw [ae_iff]
        simpa using measure_singleton (μ := (volume : Measure (Euc d))) (0 : Euc d)
      filter_upwards [hne] with w hw0 hw
      have hwcube : w ∈ cube d := hw.1
      have hwδ : δ < ‖w‖ := by
        by_contra hcon
        push Not at hcon
        exact hw.2 ⟨norm_pos_iff.2 hw0, hcon⟩
      have hg := hfar w hwcube hwδ
      have h0 := hρb w
      rw [Real.norm_eq_abs]
      simp only [hΦ]
      rw [abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) h0.1)]
      have h1 : γ w ^ 2 * Real.exp (-(u * γ w)) ≤ G₀ ^ 2 := by
        have hexp : Real.exp (-(u * γ w)) ≤ 1 := by
          rw [Real.exp_le_one_iff]; nlinarith [hγ0 w]
        calc γ w ^ 2 * Real.exp (-(u * γ w)) ≤ γ w ^ 2 * 1 :=
              mul_le_mul_of_nonneg_left hexp (sq_nonneg _)
          _ ≤ G₀ ^ 2 := by rw [mul_one]; exact pow_le_pow_left₀ (hγ0 w) hg 2
      exact mul_le_mul h1 h0.2 h0.1 (by positivity)
  have hnear := eqbias_near hd hs0 hsd hδ hδ4 hR hΛ hL hγm hρm hγ0 hloc hρb hρL hu0 hu1 hη0
  -- bookkeeping
  set Mv : ℝ := ∫ w in Nn, Ψ w with hMv
  set I : ℝ := ∫ w in cube d, Φ w with hIdef
  set near : ℝ := ∫ w in Nn, (Φ w - ρt 0 * Ψ w) with hnearv
  set far : ℝ := ∫ w in cube d \ Nn, Φ w with hfarv
  have hnear_eq : near = (∫ w in Nn, Φ w) - ρt 0 * Mv := by
    rw [hnearv, integral_sub hΦN (hΨN.const_mul (ρt 0)), integral_const_mul]
  have hI_eq : I - ρt 0 * Mv = near + far := by
    rw [hnear_eq, hfarv]
    have : far = I - ∫ w in Nn, Φ w := hsplit
    rw [hfarv] at this
    rw [this]; ring
  have hρ0 := hρb 0
  have hrhs : u ^ P * I - ρt 0 * κ = u ^ P * (near + far) + ρt 0 * (u ^ P * Mv - κ) := by
    have : I = near + far + ρt 0 * Mv := by linarith [hI_eq]
    rw [this]; ring
  have hb1 : |u ^ P * Mv - κ| ≤ bc / s * (u ^ P * I₀m) := by
    rw [abs_le]; constructor <;> linarith [huPM_le, huPM_ge]
  have hb2 : |u ^ P * (near + far)| ≤ u ^ P * (‖near‖ + ‖far‖) := by
    rw [abs_mul, abs_of_pos huP0]
    refine mul_le_mul_of_nonneg_left ?_ huP0.le
    exact (abs_add_le _ _)
  have hb3 : |ρt 0 * (u ^ P * Mv - κ)| ≤ Λ * (bc / s * (u ^ P * I₀m)) := by
    rw [abs_mul, abs_of_nonneg hρ0.1]
    exact mul_le_mul hρ0.2 hb1 (abs_nonneg _) hΛ
  have hTn : ‖near‖ + ‖far‖ ≤ Λ * Real.exp R * (2 * R * K₁ + R ^ 2) +
      (Λ * Real.exp R * R * u + L * η) * Mv + 2 * Λ * η ^ (-(2 * s)) + G₀ ^ 2 * Λ := by
    have := hnear
    linarith [hfar_b]
  have hcoef : 0 ≤ Λ * Real.exp R * R * u + L * η := by positivity
  have hb4 : u ^ P * (‖near‖ + ‖far‖) ≤ u ^ P * C₁ + (Λ * Real.exp R * R * u + L * η) * κ := by
    have h1 := mul_le_mul_of_nonneg_left hTn huP0.le
    have h2 : (Λ * Real.exp R * R * u + L * η) * (u ^ P * Mv) ≤
        (Λ * Real.exp R * R * u + L * η) * κ := mul_le_mul_of_nonneg_left huPM_le hcoef
    have h3 : u ^ P * ((Λ * Real.exp R * R * u + L * η) * Mv) =
        (Λ * Real.exp R * R * u + L * η) * (u ^ P * Mv) := by ring
    have h4 : u ^ P * (Λ * Real.exp R * (2 * R * K₁ + R ^ 2) +
        (Λ * Real.exp R * R * u + L * η) * Mv + 2 * Λ * η ^ (-(2 * s)) + G₀ ^ 2 * Λ) =
        u ^ P * C₁ + (Λ * Real.exp R * R * u + L * η) * (u ^ P * Mv) := by
      rw [hC₁]; ring
    linarith
  have hfin : |u ^ P * I - ρt 0 * κ| ≤ u ^ P * C₃ + L * η * κ := by
    rw [hrhs]
    refine (abs_add_le _ _).trans ?_
    have h5 : Λ * Real.exp R * R * u * κ ≤ Λ * Real.exp R * R * κ * u ^ P := by
      have : 0 ≤ Λ * Real.exp R * R * κ := by positivity
      nlinarith [mul_le_mul_of_nonneg_left huuP this]
    have h6 : u ^ P * C₃ = u ^ P * C₁ + Λ * (bc / s * (u ^ P * I₀m)) +
        Λ * Real.exp R * R * κ * u ^ P := by
      rw [hC₃]; ring
    have h7 : (Λ * Real.exp R * R * u + L * η) * κ = Λ * Real.exp R * R * u * κ + L * η * κ := by
      ring
    linarith [hb2, hb3, hb4]
  have hη1 : L * η * κ ≤ ε / 2 := by
    rw [hη]
    have hpos : 0 < 2 * (L * κ + 1) := by positivity
    have : L * (ε / (2 * (L * κ + 1))) * κ = ε / 2 * ((L * κ) / (L * κ + 1)) := by
      field_simp
    rw [this]
    have h8 : (L * κ) / (L * κ + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have : 0 ≤ ε / 2 := by positivity
    nlinarith
  have hη2 : u ^ P * C₃ ≤ ε / 2 := by
    have h9 : u ^ P * C₃ ≤ ε / (2 * (C₃ + 1)) * C₃ := mul_le_mul_of_nonneg_right huP hC₃0
    have h10 : ε / (2 * (C₃ + 1)) * C₃ = ε / 2 * (C₃ / (C₃ + 1)) := by field_simp
    have h11 : C₃ / (C₃ + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    have : 0 ≤ ε / 2 := by positivity
    nlinarith
  have hgoal : |u ^ P * I - ρt 0 * κ| ≤ ε := by linarith [hfin, hη1, hη2]
  have hI' : I = ∫ w in cube d, γ w ^ 2 * Real.exp (-(u * γ w)) * ρt w := by
    simp only [hIdef, hΦ]
  rw [hI'] at hgoal
  exact hgoal

end Main

end HRS

end
