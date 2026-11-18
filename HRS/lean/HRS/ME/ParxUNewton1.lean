import HRS.ME.ParxU
import HRS.Equilibrium.Parametrix.PX3aAuxR

/-!
# Packet P2 (part 1): uniform Newton chart in `β`

The Newton kernel scales like `(2ν)⁻¹`: `newtonKernel d ν = (1/(2ν)) · newtonKernel d (1/2)`
(`newtonKernel_scale`), hence `newtonChart d ν G = (1/(2ν)) · newtonChart d (1/2) G`
(`newtonChart_scale`) and, off the diagonal, `ofChart (newtonChart d ν (toChart F))` is
`(1/(2ν))` times the `ν = 1/2` chart (`ofChart_newtonChart_scale`).

For `ν = β⁻¹` in `[νm, νp]` the factor is at most `1/(2 νm)`, so the `β`-dependence of the
conormal constants of `newton_conormal_of_pot`, `newton_ofChart_general` is a scalar factor
which is bounded by a constant depending only on `νm`.  The uniform statements below have their
constants chosen before `β, V, ρ`, through the bundle `ParxU`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.ME.ParxU

open HRS.Parx

variable {d : ℕ} {s : ℝ} {N : ℕ} {νm νp c₀ Λ₀ : ℝ}

/-! ### Scaling of the Newton chart -/

/-- `Γ_ν = (1/(2ν)) Γ_{1/2}` for the Newton kernel. -/
theorem newtonKernel_scale (ν : ℝ) (z : Euc d) :
    newtonKernel d ν z = (1 / (2 * ν)) * newtonKernel d (1 / 2) z := by
  rw [newtonKernel_eq d ν z, newtonKernel_eq d (1 / 2) z]
  norm_num

/-- `newtonChart d ν G = (1/(2ν)) · newtonChart d (1/2) G`. -/
theorem newtonChart_scale (ν : ℝ) (G : Euc d × Euc d → ℝ) (p : Euc d × Euc d) :
    newtonChart d ν G p = (1 / (2 * ν)) * newtonChart d (1 / 2) G p := by
  have hint : ∫ w : Euc d, newtonKernel d ν (p.2 - w) * (chi d w * G (p.1, w)) =
      (1 / (2 * ν)) * ∫ w : Euc d, newtonKernel d (1 / 2) (p.2 - w) * (chi d w * G (p.1, w)) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    dsimp only
    rw [newtonKernel_scale ν (p.2 - w)]
    ring
  unfold newtonChart
  rw [hint]
  ring

/-- Off the diagonal the scaling passes to `ofChart`. -/
theorem ofChart_newtonChart_scale (ν : ℝ) (F : Torus d → Torus d → ℝ) :
    ofChart (newtonChart d ν (toChart F)) =
      fun x y => (1 / (2 * ν)) * ofChart (newtonChart d (1 / 2) (toChart F)) x y := by
  funext x y
  unfold ofChart
  split_ifs
  · simp
  · exact newtonChart_scale ν (toChart F) _

/-- Conormal bound for the chart with `ν = β⁻¹` from the `ν = 1/2` bound: the factor `1/(2ν)` is at
most `1/(2 νm)` when `νm ≤ ν`.  The constant `C₀ (2νm)⁻¹` depends only on `νm`. -/
theorem conormalL_ofChart_newton_scale {σ : ℝ} {b : ℕ → ℕ} {m : ℕ} {B C₀ νm ν : ℝ}
    (F : Torus d → Torus d → ℝ) (hνm : 0 < νm) (hν : νm ≤ ν) (hC0 : 0 ≤ C₀) (hB : 0 ≤ B)
    (h : ConormalL σ b m (C₀ * B) (ofChart (newtonChart d (1 / 2) (toChart F)))) :
    ConormalL σ b m (C₀ * (1 / (2 * νm)) * B) (ofChart (newtonChart d ν (toChart F))) := by
  have hν0 : 0 < ν := lt_of_lt_of_le hνm hν
  have hκ0 : 0 ≤ 1 / (2 * ν) := div_nonneg zero_le_one (by linarith)
  have hs := conormalL_smul h (1 / (2 * ν))
  rw [abs_of_nonneg hκ0] at hs
  rw [ofChart_newtonChart_scale ν F]
  have hX : 0 ≤ C₀ * B := mul_nonneg hC0 hB
  refine conormalL_mono_B hs (mul_nonneg hκ0 hX) ?_
  have hk : 1 / (2 * ν) ≤ 1 / (2 * νm) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  calc 1 / (2 * ν) * (C₀ * B) ≤ 1 / (2 * νm) * (C₀ * B) :=
        mul_le_mul_of_nonneg_right hk hX
    _ = C₀ * (1 / (2 * νm)) * B := by ring

/-! ### Uniform versions -/

/-- **Uniform version of `newton_conormal_of_pot`.** The constant depends only on `(d, s, N, νm, νp,
c₀, Λ₀, σ, b, m, b')`; the chart is `newtonChart d β⁻¹`, with `β` chosen after the constant. -/
theorem newton_conormal_of_pot_unif (hd : 2 ≤ d) {σ : ℝ} (hσ : σ < d) (b m : ℕ)
    (b' : ℕ → ℕ) (hb1 : ∀ c, b ≤ b' c) (hb2 : ∀ c, b' c ≤ b + 1) :
    ∃ Cq : ℝ, 0 ≤ Cq ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ (Cpot B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ Cpot → 0 ≤ B → Conormal σ b m B F →
      (∀ a c : ℕ, a + c ≤ m → ∀ r : ℝ, 0 < r → r < 1 / 8 → ∀ X z : Euc d, ‖z‖ = r →
        ∀ (u : Fin a → Euc d) (v : Fin c → Euc d),
        |iteratedFDeriv ℝ (a + c) (newtonPot d (fun q => chi d q.2 * toChart F q)) (X, z) (pat u v)| ≤
          Cpot * B * (1 + r ^ (-(σ - 2 + c)) * lw r ^ b' c) * ((∏ i, ‖u i‖) * ∏ j, ‖v j‖)) →
      ConormalL (σ - 2) b' m (Cq * Cpot * B) (ofChart (newtonChart d β⁻¹ (toChart F))) := by
  obtain ⟨Cq, hCq0, hCq⟩ := newton_conormal_of_pot hd (ν := 1 / 2) (by norm_num) hσ b m b' hb1 hb2
  refine ⟨Cq * (1 / (2 * max νm 0)), mul_nonneg hCq0
    (div_nonneg zero_le_one (mul_nonneg two_pos.le (le_max_right νm 0))),
    fun β V ρ U Cpot B F hCp hB hF hpot => ?_⟩
  have hνm : 0 < νm := U.F.hνm
  rw [max_eq_left hνm.le]
  have hνb : νm ≤ β⁻¹ := U.beta_bounds.1
  have hc := hCq Cpot B F hCp hB hF hpot
  have key := conormalL_ofChart_newton_scale (C₀ := Cq * Cpot) (B := B) F hνm hνb
    (mul_nonneg hCq0 hCp) hB hc
  have e : Cq * (1 / (2 * νm)) * Cpot * B = Cq * Cpot * (1 / (2 * νm)) * B := by ring
  rw [e]
  exact key

/-- **Uniform version of `newton_ofChart_general`.** The constant depends only on `(d, s, N, νm, νp,
c₀, Λ₀, σ, b, m)`; it is chosen before `β, V, ρ`. -/
theorem newton_ofChart_general_unif (hd : 2 ≤ d) {σ : ℝ} (hσ : σ < d) (b m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B → Conormal σ b m B F →
      ConormalL (σ - 2) (fun c => b + if σ - 2 + (c : ℝ) = 0 then 1 else 0) m (C * B)
        (ofChart (newtonChart d β⁻¹ (toChart F))) := by
  obtain ⟨Cn, hCn0, hCn⟩ := newton_ofChart_general hd (ν := 1 / 2) (by norm_num) hσ b m
  refine ⟨Cn * (1 / (2 * max νm 0)), mul_nonneg hCn0
    (div_nonneg zero_le_one (mul_nonneg two_pos.le (le_max_right νm 0))),
    fun β V ρ U B F hB hF => ?_⟩
  have hνm : 0 < νm := U.F.hνm
  rw [max_eq_left hνm.le]
  have hνb : νm ≤ β⁻¹ := U.beta_bounds.1
  have hc := hCn B F hB hF
  exact conormalL_ofChart_newton_scale (C₀ := Cn) (B := B) F hνm hνb hCn0 hB hc

end HRS.ME.ParxU

end
