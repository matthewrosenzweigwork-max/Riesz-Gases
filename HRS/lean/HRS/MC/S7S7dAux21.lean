import HRS.MC.S7S7dAux20

/-!
# Packet `s7_S7d_uniform_limits`, helper 21: the size of the tensor `Q_{v;fg}`

`|Q_{v;fg}| ≤ sup|f| sup|g| (1+G) Σ_j L_j / 2` for Lipschitz fields `v` with constants `L_j`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7d

open HRS HRS.Sec7 HRS.MC.SEdge HRS.StaticLimitAux

variable {d : ℕ} {s : ℝ}

theorem s7d_Qt_bound (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ (v : Fin d → Torus d → ℝ) {L : ℝ}, 0 < L →
      (∀ k, HRS.KernelGrad.IsLipschitz L (v k)) → (∀ j, Torus.IsSmooth (v j)) →
      ∀ {f g : Torus d → ℝ} {A₁ A₂ : ℝ}, Continuous f → Continuous g → (∀ x, |f x| ≤ A₁) →
        (∀ x, |g x| ≤ A₂) → |sed_Qt d s ρ v f g| ≤ A₁ * A₂ * ((1 + G) * (d * L) / 2) := by
  haveI hP : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  obtain ⟨G, hG0, hGb⟩ := HRS.MC.Sec7.S7c.s7c_L2_bound hd hs0 hs hρ
  refine ⟨G, hG0, fun v L hL hLip hv f g A₁ A₂ hf hg hfb hgb => ?_⟩
  have hsd : s < (d : ℝ) := by
    have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith
  have hvc : ∀ j, Continuous (v j) := fun j => HRS.Q66.q66_cont_of_smooth (hv j)
  have hmeas := HRS.Q66.q66_hv_measurable hsd hvc
  set μ := withDensityReal ρ with hμ
  set h := HRS.Q66.q66_hv d s v with hh
  have hint : Integrable (fun z : Torus d × Torus d => h z.1 z.2 ^ 2) (μ.prod μ) :=
    HRS.MC.SEdge.B2b.sed_B2b_hs_proof hd hs0 hs hρ hv
  set S : ℝ := d * L with hS
  have hSpos : 0 < S := by
    have : (0 : ℝ) < d := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    positivity
  have hG2 : ∫ x, ∫ y, h x y ^ 2 ∂μ ∂μ ≤ G * S ^ 2 := by
    have := hGb v (fun _ => L) (fun _ => hL.le) hLip hv
    simpa [hS, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this
  have hhm : Measurable (fun z : Torus d × Torus d => h z.1 z.2) := hmeas
  have hpt : ∀ z : Torus d × Torus d, |h z.1 z.2| ≤ (S + h z.1 z.2 ^ 2 / S) / 2 := by
    intro z
    have h1 : 0 ≤ (S - |h z.1 z.2|) ^ 2 := sq_nonneg _
    have h2 : h z.1 z.2 ^ 2 = |h z.1 z.2| ^ 2 := (sq_abs _).symm
    rw [h2, le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have : S + |h z.1 z.2| ^ 2 / S - 2 * |h z.1 z.2| = (S - |h z.1 z.2|) ^ 2 / S := by
      field_simp; ring
    have h3 : 0 ≤ (S - |h z.1 z.2|) ^ 2 / S := by positivity
    linarith
  have hbd : Integrable (fun z : Torus d × Torus d => (S + h z.1 z.2 ^ 2 / S) / 2) (μ.prod μ) :=
    ((integrable_const S).add (hint.div_const S)).div_const 2
  have hhi : Integrable (fun z : Torus d × Torus d => |h z.1 z.2|) (μ.prod μ) :=
    hbd.mono' hhm.abs.aestronglyMeasurable (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_abs]; exact hpt z)
  have hA₁ : 0 ≤ A₁ := (abs_nonneg _).trans (hfb (0 : Torus d))
  have hA₂ : 0 ≤ A₂ := (abs_nonneg _).trans (hgb (0 : Torus d))
  have hFm : Measurable (fun z : Torus d × Torus d => h z.1 z.2 * f z.1 * g z.2) :=
    (hhm.mul (hf.measurable.comp measurable_fst)).mul (hg.measurable.comp measurable_snd)
  have hFpt : ∀ z : Torus d × Torus d, |h z.1 z.2 * f z.1 * g z.2| ≤ A₁ * A₂ * |h z.1 z.2| := by
    intro z
    rw [abs_mul, abs_mul]
    calc |h z.1 z.2| * |f z.1| * |g z.2| ≤ |h z.1 z.2| * A₁ * A₂ :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hfb _) (abs_nonneg _)) (hgb _) (abs_nonneg _)
            (by positivity)
      _ = A₁ * A₂ * |h z.1 z.2| := by ring
  have hFi : Integrable (fun z : Torus d × Torus d => h z.1 z.2 * f z.1 * g z.2) (μ.prod μ) :=
    (hhi.const_mul (A₁ * A₂)).mono' hFm.aestronglyMeasurable (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact hFpt z)
  have e1 : sed_Qt d s ρ v f g = ∫ z : Torus d × Torus d, h z.1 z.2 * f z.1 * g z.2 ∂(μ.prod μ) := by
    unfold sed_Qt
    exact (integral_prod (fun z : Torus d × Torus d => h z.1 z.2 * f z.1 * g z.2) hFi).symm
  rw [e1]
  have e2 : ∫ z : Torus d × Torus d, h z.1 z.2 ^ 2 ∂(μ.prod μ) = ∫ x, ∫ y, h x y ^ 2 ∂μ ∂μ :=
    integral_prod (fun z : Torus d × Torus d => h z.1 z.2 ^ 2) hint
  calc |∫ z : Torus d × Torus d, h z.1 z.2 * f z.1 * g z.2 ∂(μ.prod μ)|
      ≤ ∫ z : Torus d × Torus d, |h z.1 z.2 * f z.1 * g z.2| ∂(μ.prod μ) := abs_integral_le_integral_abs
    _ ≤ ∫ z : Torus d × Torus d, A₁ * A₂ * ((S + h z.1 z.2 ^ 2 / S) / 2) ∂(μ.prod μ) :=
        integral_mono (hFi.abs) (hbd.const_mul _) fun z =>
          (hFpt z).trans (mul_le_mul_of_nonneg_left (hpt z) (by positivity))
    _ = A₁ * A₂ * ((S + (∫ z : Torus d × Torus d, h z.1 z.2 ^ 2 ∂(μ.prod μ)) / S) / 2) := by
        rw [integral_const_mul, integral_div, integral_add (integrable_const S) (hint.div_const S),
          integral_div, integral_const]
        simp
    _ ≤ A₁ * A₂ * ((1 + G) * S / 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [e2]
        have : (∫ x, ∫ y, h x y ^ 2 ∂μ ∂μ) / S ≤ G * S := by
          rw [div_le_iff₀ hSpos]; nlinarith
        linarith

end HRS.MC.Sec7.S7d

end
