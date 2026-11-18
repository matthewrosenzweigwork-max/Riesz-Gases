import HRS.Uniform.Q45Cov7

/-!
# Q45 (Lemma 3.20): `L²`-convergence of functionals of Riemann sums along partitions
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q45

section Conv

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma isStochConv_tendsto {VE : ℝ → ℝ → E →L[ℝ] E} {j : H →L[ℝ] E} {G : ℝ → Ω → H} {t : ℝ}
    {Zt : Ω → E} (h : IsStochConv P VE j G 0 t Zt) (n : ℕ → ℕ) (r : ∀ N, Fin (n N + 1) → ℝ)
    (h0 : ∀ N, r N 0 = 0) (hl : ∀ N, r N (Fin.last _) = t) (hm : ∀ N, Monotone (r N))
    (hmesh : ∀ δ > 0, ∀ᶠ N in atTop, ∀ i : Fin (n N), r N i.succ - r N i.castSucc < δ) :
    Tendsto (fun N => ∫⁻ ω, ‖Zt ω - riemannSum VE j G t (r N) ω‖ₑ ^ 2 ∂P) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases htop : ε = ⊤
  · exact Eventually.of_forall fun N => by simp [htop]
  have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
  obtain ⟨δ, hδ, hconv⟩ := h ε.toReal hεr
  filter_upwards [hmesh δ hδ] with N hN
  have := hconv (n N) (r N) (h0 N) (hl N) (hm N) hN
  rw [ENNReal.ofReal_toReal htop] at this
  exact this.le

lemma functional_lintegral_le (ℓ : E →L[ℝ] ℝ) (Zt R : Ω → E) :
    ∫⁻ ω, ‖ℓ (R ω) - ℓ (Zt ω)‖ₑ ^ 2 ∂P ≤ ‖ℓ‖ₑ ^ 2 * ∫⁻ ω, ‖Zt ω - R ω‖ₑ ^ 2 ∂P := by
  have hpt : ∀ ω, ‖ℓ (R ω) - ℓ (Zt ω)‖ₑ ^ 2 ≤ ‖ℓ‖ₑ ^ 2 * ‖Zt ω - R ω‖ₑ ^ 2 := by
    intro ω
    have h1 := ℓ.le_opNorm_enorm (R ω - Zt ω)
    rw [map_sub] at h1
    have h2 : ‖R ω - Zt ω‖ₑ = ‖Zt ω - R ω‖ₑ := enorm_sub_rev _ _
    rw [h2] at h1
    calc ‖ℓ (R ω) - ℓ (Zt ω)‖ₑ ^ 2 ≤ (‖ℓ‖ₑ * ‖Zt ω - R ω‖ₑ) ^ 2 := pow_le_pow_left' h1 2
      _ = ‖ℓ‖ₑ ^ 2 * ‖Zt ω - R ω‖ₑ ^ 2 := by rw [mul_pow]
  calc ∫⁻ ω, ‖ℓ (R ω) - ℓ (Zt ω)‖ₑ ^ 2 ∂P ≤ ∫⁻ ω, ‖ℓ‖ₑ ^ 2 * ‖Zt ω - R ω‖ₑ ^ 2 ∂P :=
        lintegral_mono hpt
    _ = ‖ℓ‖ₑ ^ 2 * ∫⁻ ω, ‖Zt ω - R ω‖ₑ ^ 2 ∂P :=
        lintegral_const_mul' _ _ (ENNReal.pow_ne_top enorm_ne_top)

/-- The functional of the Riemann sums converges to the functional of the limit, in the sense of
`∫⁻ ‖·‖²` (a pure consequence of `IsStochConv` along partitions of vanishing mesh). -/
lemma functional_tendsto {VE : ℝ → ℝ → E →L[ℝ] E} {j : H →L[ℝ] E} {G : ℝ → Ω → H} {t : ℝ}
    {Zt : Ω → E} (h : IsStochConv P VE j G 0 t Zt) (ℓ : E →L[ℝ] ℝ) (n : ℕ → ℕ)
    (r : ∀ N, Fin (n N + 1) → ℝ)
    (h0 : ∀ N, r N 0 = 0) (hl : ∀ N, r N (Fin.last _) = t) (hm : ∀ N, Monotone (r N))
    (hmesh : ∀ δ > 0, ∀ᶠ N in atTop, ∀ i : Fin (n N), r N i.succ - r N i.castSucc < δ) :
    Tendsto (fun N => ∫⁻ ω, ‖ℓ (riemannSum VE j G t (r N) ω) - ℓ (Zt ω)‖ₑ ^ 2 ∂P) atTop (𝓝 0) := by
  have h1 := isStochConv_tendsto h n r h0 hl hm hmesh
  have h2 : Tendsto (fun N => ‖ℓ‖ₑ ^ 2 * ∫⁻ ω, ‖Zt ω - riemannSum VE j G t (r N) ω‖ₑ ^ 2 ∂P) atTop
      (𝓝 (‖ℓ‖ₑ ^ 2 * 0)) :=
    ENNReal.Tendsto.const_mul h1 (Or.inr (ENNReal.pow_ne_top enorm_ne_top))
  rw [mul_zero] at h2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun N => bot_le)
    (fun N => functional_lintegral_le ℓ Zt _)

end Conv

end HRS.Uniform.Q45
