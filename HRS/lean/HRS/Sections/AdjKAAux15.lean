import HRS.Sections.AdjKAAux14

/-!
# ADJKA part 15: the drift increment bound on finite-energy elements
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.AdjK

open HRS HRS.Uniform HRS.Uniform.Q54 HRS.Uniform.Q48b

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem adjka_norm_embed_mono {r a b : ℝ} (hra : r ≤ a) (hab : a ≤ b) (w : NegSobolev d r) :
    ‖NegSobolev.embed b w‖ ≤ ‖NegSobolev.embed a w‖ := by
  have h1 := adjka_norm_embed_sq (hra.trans hab) w
  have h2 := adjka_norm_embed_sq hra w
  have h3 : fsq b w ≤ fsq a w := fsq_le_of_le hra hab w
  refine le_of_sq_le_sq ?_ (norm_nonneg _)
  rw [h1, h2]; exact h3

theorem adjka_pow4_add_le (x y : ℝ≥0∞) : (x + y) ^ (4 : ℝ) ≤ 8 * (x ^ (4 : ℝ) + y ^ (4 : ℝ)) := by
  have := ENNReal.rpow_add_le_mul_rpow_add_rpow x y (p := 4) (by norm_num)
  have h2 : (2 : ℝ≥0∞) ^ ((4 : ℝ) - 1) = 8 := by
    rw [show (4 : ℝ) - 1 = (3 : ℕ) by norm_num, ENNReal.rpow_natCast]; norm_num
  rw [h2] at this
  exact this

/-- `‖(V^{t,s} - 1) F‖_{E_m}⁴ ≤ (C_A (t-s))⁴ ‖F‖⁴_{E_j}` for `F ∈ E_m` of finite `E_j`-energy. -/
theorem adjka_drift_bound {D : DynData d} {ρ : ℝ → Torus d → ℝ} {j m : ℝ} (hjm : j + 2 ≤ m)
    {Vj : ℝ → ℝ → NegSobolev d j →L[ℝ] NegSobolev d j}
    {Vm : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m}
    (hVj : IsDualEvolution D ρ j Vj) (hVm : IsDualEvolution D ρ m Vm) {CA : ℝ} (hCA : 0 ≤ CA)
    (hA2 : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ∀ z : NegSobolev d j,
      ‖NegSobolev.embed (j + 2) (Vj t u z - z)‖ ≤ CA * (t - u) * ‖z‖)
    {u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) (F : NegSobolev d m) (hF : adjkEnergy j m F ≠ ⊤) :
    ‖Vm t u F - F‖ₑ ^ (4 : ℝ) ≤ ENNReal.ofReal ((CA * (t - u)) ^ 4) * (adjkEnergy j m F) ^ 2 := by
  have hjm' : j ≤ m := by linarith
  obtain ⟨z, rfl⟩ := adjka_lift hjm' F hF
  have e1 : Vm t u (NegSobolev.embed m z) - NegSobolev.embed m z =
      NegSobolev.embed m (Vj t u z - z) := by
    rw [adjka_dual_embed hjm' hVj hVm hu hut z]
    have := (adjkEmb d hjm').map_sub (Vj t u z) z
    simpa [adjkEmb_apply] using this.symm
  rw [e1, adjka_energy_embed' hjm']
  have hn : ‖NegSobolev.embed m (Vj t u z - z)‖ ≤ CA * (t - u) * ‖z‖ :=
    (adjka_norm_embed_mono (by linarith : j ≤ j + 2) hjm _).trans (hA2 u t hu hut z)
  have hτ : 0 ≤ t - u := by linarith
  calc ‖NegSobolev.embed m (Vj t u z - z)‖ₑ ^ (4 : ℝ)
      ≤ (ENNReal.ofReal (CA * (t - u)) * ‖z‖ₑ) ^ (4 : ℝ) := by
        refine ENNReal.rpow_le_rpow ?_ (by norm_num)
        rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm z, ← ENNReal.ofReal_mul (mul_nonneg hCA hτ)]
        exact ENNReal.ofReal_le_ofReal hn
    _ = ENNReal.ofReal ((CA * (t - u)) ^ 4) * (‖z‖ₑ ^ 2) ^ 2 := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hCA hτ) (by norm_num)]
        congr 1
        · congr 1
          rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        · rw [← pow_mul, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]

end HRS.AdjK
