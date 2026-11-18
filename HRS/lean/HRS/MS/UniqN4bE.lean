import HRS.MS.UniqN4bD

/-!
# N4b of `UniqPlan.md`, part E: the far-field integral and the interpolated local bound of `H_i`

* `n4b_far`: with `1 - θ` vanishing at distance `< δ` from `tsupport ψ` and `ρ'`, `∂_jρ'` decaying like
  `⟨y⟩^{-(d+3)}`, `|∫ f (1 - θ) (∂_jρ' H_i + ρ' ∂_jH_i)| ≤ C_f Cρ ‖ψ‖₁ A` for `f` of local mass `A`.
* `n4b_H_interp`: `‖1_{B̄(p,R)} H_i‖₂ ≤ C₂ a^{1-κ} (a + √d Γ)^κ` where `‖ψ‖₂ ≤ a`, `‖∇ψ‖₂ ≤ Γ`,
  `κ = kgOrder d s`  (`n0_kcd_local` and `n4a_interp_E_bound`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqN4b

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqT3 HRS.MS.UniqM1
  HRS.MS.UniqNDefs HRS.MS.UniqN2b HRS.MS.UniqN0 HRS.MS.UniqN1c HRS.MS.UniqN4a

variable {d : ℕ}

theorem n4b_far {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {δ : ℝ} (hδ : 0 < δ) :
    ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ (i j : Fin d) {ρ' : Euc d → ℝ}, ContDiff ℝ 1 ρ' → ∀ {Cρ : ℝ}, 0 ≤ Cρ →
      (∀ y, |ρ' y| ≤ Cρ * (1 + ‖y‖) ^ (-((d : ℝ) + 3))) →
      (∀ y, |D1 j ρ' y| ≤ Cρ * (1 + ‖y‖) ^ (-((d : ℝ) + 3))) →
      ∀ {ψ : Euc d → ℝ}, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      ∀ {θ : Euc d → ℝ}, Continuous θ → (∀ y, |1 - θ y| ≤ 1) →
      (∀ y, 1 - θ y ≠ 0 → ∀ x ∈ tsupport ψ, δ ≤ ‖y - x‖) →
      ∀ {A : ℝ}, 0 ≤ A → ∀ {f : Euc d → ℝ}, LocMass A f → ∀ {Q : ℝ}, 0 ≤ Q → ∫ x, |ψ x| ≤ Q →
      Integrable (fun y => f y * ((1 - θ y) * (D1 j ρ' y * kernelConvDeriv d s i ψ y +
          ρ' y * D1 j (kernelConvDeriv d s i ψ) y))) volume ∧
      |∫ y, f y * ((1 - θ y) * (D1 j ρ' y * kernelConvDeriv d s i ψ y +
          ρ' y * D1 j (kernelConvDeriv d s i ψ) y))| ≤ Cf * Cρ * Q * A := by
  obtain ⟨Cc, hCc0, hCc⟩ := n0_cell_decay_mul (d := d) (κ := (d : ℝ) + 3) (by linarith)
  set Mh : ℝ := max 1 s * δ ^ (-s - 1) with hMh
  set Md : ℝ := max 1 s * (s + 3) * δ ^ (-s - 2) with hMd
  have hMh0 : 0 ≤ Mh := by positivity
  have hMd0 : 0 ≤ Md := by positivity
  refine ⟨Cc * (Mh + Md), by positivity, fun i j ρ' hρ Cρ hCρ hρ0 hρ1 ψ hψ hψc θ hθ hθ1 hsep A hA f hf Q hQ hψQ => ?_⟩
  set H : Euc d → ℝ := kernelConvDeriv d s i ψ with hH
  have hXc := n4b_X_cont hs0 hsd hρ hψ hψc i j
  have hmeas : AEStronglyMeasurable (fun y => (1 - θ y) * (D1 j ρ' y * H y +
      ρ' y * D1 j H y)) volume :=
    ((continuous_const.sub hθ).mul hXc).aestronglyMeasurable
  have hbd : ∀ y, |(1 - θ y) * (D1 j ρ' y * H y + ρ' y * D1 j H y)| ≤
      (Cρ * (Mh * Q + Md * Q)) * (1 + ‖y - 0‖) ^ (-((d : ℝ) + 3)) := by
    intro y
    rw [sub_zero]
    have hw : 0 ≤ (1 + ‖y‖) ^ (-((d : ℝ) + 3)) := by positivity
    by_cases h0 : 1 - θ y = 0
    · rw [h0, zero_mul, abs_zero]; positivity
    · have hsy := hsep y h0
      have hHy : |H y| ≤ Mh * Q := by
        refine (n4b_far_H hs0 i (hψ.of_le (by norm_num)) hψc hδ hsy).trans ?_
        exact mul_le_mul_of_nonneg_left hψQ hMh0
      have hdHy : |D1 j H y| ≤ Md * Q := by
        refine (n4b_far_dH hs0 hsd i j hψ hψc hδ hsy).trans ?_
        exact mul_le_mul_of_nonneg_left hψQ hMd0
      rw [abs_mul]
      calc |1 - θ y| * |D1 j ρ' y * H y + ρ' y * D1 j H y|
          ≤ 1 * |D1 j ρ' y * H y + ρ' y * D1 j H y| :=
            mul_le_mul_of_nonneg_right (hθ1 y) (abs_nonneg _)
        _ ≤ |D1 j ρ' y * H y| + |ρ' y * D1 j H y| := by rw [one_mul]; exact abs_add_le _ _
        _ = |D1 j ρ' y| * |H y| + |ρ' y| * |D1 j H y| := by rw [abs_mul, abs_mul]
        _ ≤ (Cρ * (1 + ‖y‖) ^ (-((d : ℝ) + 3))) * (Mh * Q) +
              (Cρ * (1 + ‖y‖) ^ (-((d : ℝ) + 3))) * (Md * Q) := by
            gcongr
            · exact hρ1 y
            · exact hρ0 y
        _ = _ := by ring
  have hA' : 0 ≤ Cρ * (Mh * Q + Md * Q) := by positivity
  obtain ⟨_, hfin⟩ := hCc 0 (Cρ * (Mh * Q + Md * Q)) A f
    (fun y => (1 - θ y) * (D1 j ρ' y * H y + ρ' y * D1 j H y)) hA' hf hbd
  obtain ⟨hint, hle⟩ := hfin hmeas
  refine ⟨hint, ?_⟩
  refine (abs_integral_le_integral_abs).trans (hle.trans ?_)
  rw [abs_of_nonneg hA]
  have : Cc * (Cρ * (Mh * Q + Md * Q)) * A = (Cc * (Mh + Md)) * Cρ * Q * A := by ring
  rw [this]

theorem n4b_kgOrder_lt_one {s : ℝ} (hsd : s < d) : kgOrder d s < 1 := by
  unfold kgOrder
  refine max_lt (by linarith) one_pos

theorem n4b_kgOrder_nonneg (d : ℕ) (s : ℝ) : 0 ≤ kgOrder d s := le_max_right _ _

theorem n4b_H_interp (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {R : ℝ} (hR : 1 ≤ R) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ (i : Fin d) (p : Euc d) (ψ : Euc d → ℝ), ContDiff ℝ 1 ψ →
      HasCompactSupport ψ → Function.support ψ ⊆ closedBall p R → ∀ {a Γ : ℝ}, 0 ≤ a → 0 ≤ Γ →
      eLpNorm ψ 2 volume ≤ ENNReal.ofReal a →
      eLpNorm (fun x => ‖fderiv ℝ ψ x‖) 2 volume ≤ ENNReal.ofReal Γ →
      eLpNorm ((closedBall p R).indicator (kernelConvDeriv d s i ψ)) 2 volume ≤
        ENNReal.ofReal (C₂ * (a ^ (1 - kgOrder d s) * (a + Real.sqrt d * Γ) ^ kgOrder d s)) := by
  obtain ⟨C₀, C, hloc⟩ := n0_kcd_local hd hs0 hsd
  refine ⟨|C * R ^ C₀|, abs_nonneg _, fun i p ψ hψ hψc hsupp a Γ ha hΓ h0 h1 => ?_⟩
  have hb : 0 ≤ a + Real.sqrt d * Γ := by positivity
  obtain ⟨hS, hE0, hE1⟩ := n4b_sob_one' hψ hψc ha hΓ h0 h1
  have hint := n4a_interp_E_bound (kgOrder d s) (n4b_kgOrder_nonneg d s)
    (n0_kgOrder_le_one hsd) hS ha hb hE0 hE1
  have h2 := hloc i R hR p ψ hψ hψc hsupp p R le_rfl
  refine h2.trans ?_
  calc ENNReal.ofReal (C * R ^ C₀) * sobolevNormE (kgOrder d s) ψ
      ≤ ENNReal.ofReal |C * R ^ C₀| * ENNReal.ofReal (a ^ (1 - kgOrder d s) *
          (a + Real.sqrt d * Γ) ^ kgOrder d s) := by
        gcongr
        exact le_abs_self _
    _ = _ := by
        rw [← ENNReal.ofReal_mul (abs_nonneg _)]

end HRS.MS.UniqN4b
