import HRS.Uniform.Q45Mat

/-!
# Q45: the Hessian-pairing seminorm `ν_ρ`

For `ρ : ℝ^p → ℝ` (a seminorm-like gauge, in applications `u ↦ ‖L u‖`), `ν_ρ(Q) = sup |∑ Hₐᵦ Qₐᵦ|` over the matrices
`H` with `|u·Hv| ≤ ρ(u)ρ(v)`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators Matrix

namespace HRS.Uniform.Q45

open HRS HRS.LindebergAux

variable {p : ℕ}

/-- Matrices whose bilinear form is dominated by `ρ ⊗ ρ`. -/
def admForms (ρ : (Fin p → ℝ) → ℝ) : Set (Matrix (Fin p) (Fin p) ℝ) :=
  {H | ∀ u v : Fin p → ℝ, |u ⬝ᵥ (H.mulVec v)| ≤ ρ u * ρ v}

/-- The pairing seminorm `ν_ρ`. -/
def nuRho (ρ : (Fin p → ℝ) → ℝ) (Q : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  ⨆ H : admForms ρ, |∑ a, ∑ b, (H : Matrix (Fin p) (Fin p) ℝ) a b * Q a b|

section
variable {ρ : (Fin p → ℝ) → ℝ} {c : ℝ}

lemma admForms_zero (hρ : ∀ u, 0 ≤ ρ u) : (0 : Matrix (Fin p) (Fin p) ℝ) ∈ admForms ρ := by
  intro u v
  simp only [Matrix.zero_mulVec, dotProduct_zero, abs_zero]
  exact mul_nonneg (hρ u) (hρ v)

lemma term_le (hρ : ∀ u, 0 ≤ ρ u) (hc : ∀ u, ρ u ≤ c * Real.sqrt (u ⬝ᵥ u)) (hc0 : 0 ≤ c)
    (H : admForms ρ) (Q : Matrix (Fin p) (Fin p) ℝ) :
    |∑ a, ∑ b, (H : Matrix (Fin p) (Fin p) ℝ) a b * Q a b| ≤ c ^ 2 * traceNormMatrix Q := by
  refine trace_dual (H : Matrix (Fin p) (Fin p) ℝ) Q (c ^ 2) (sq_nonneg c) fun u v => ?_
  refine (H.2 u v).trans ?_
  calc ρ u * ρ v ≤ (c * Real.sqrt (u ⬝ᵥ u)) * (c * Real.sqrt (v ⬝ᵥ v)) :=
        mul_le_mul (hc u) (hc v) (hρ v) (by positivity)
    _ = c ^ 2 * Real.sqrt (u ⬝ᵥ u) * Real.sqrt (v ⬝ᵥ v) := by ring

lemma bddAbove_nu (hρ : ∀ u, 0 ≤ ρ u) (hc : ∀ u, ρ u ≤ c * Real.sqrt (u ⬝ᵥ u)) (hc0 : 0 ≤ c)
    (Q : Matrix (Fin p) (Fin p) ℝ) :
    BddAbove (Set.range fun H : admForms ρ => |∑ a, ∑ b, (H : Matrix (Fin p) (Fin p) ℝ) a b * Q a b|) :=
  ⟨c ^ 2 * traceNormMatrix Q, by rintro _ ⟨H, rfl⟩; exact term_le hρ hc hc0 H Q⟩

lemma nu_nonneg (Q : Matrix (Fin p) (Fin p) ℝ) : 0 ≤ nuRho ρ Q :=
  Real.iSup_nonneg fun _ => abs_nonneg _

lemma nu_le_s1 (hρ : ∀ u, 0 ≤ ρ u) (hc : ∀ u, ρ u ≤ c * Real.sqrt (u ⬝ᵥ u)) (hc0 : 0 ≤ c)
    (Q : Matrix (Fin p) (Fin p) ℝ) : nuRho ρ Q ≤ c ^ 2 * s1Norm Q :=
  Real.iSup_le (fun H => term_le hρ hc hc0 H Q) (by
    have := traceNormMatrix_nonneg Q
    positivity)

lemma nu_pair_le (H : admForms ρ) (hρ : ∀ u, 0 ≤ ρ u) (hc : ∀ u, ρ u ≤ c * Real.sqrt (u ⬝ᵥ u))
    (hc0 : 0 ≤ c) (Q : Matrix (Fin p) (Fin p) ℝ) :
    |∑ a, ∑ b, (H : Matrix (Fin p) (Fin p) ℝ) a b * Q a b| ≤ nuRho ρ Q :=
  le_ciSup (bddAbove_nu hρ hc hc0 Q) H

lemma nu_add_le (hρ : ∀ u, 0 ≤ ρ u) (hc : ∀ u, ρ u ≤ c * Real.sqrt (u ⬝ᵥ u)) (hc0 : 0 ≤ c)
    (Q Q' : Matrix (Fin p) (Fin p) ℝ) : nuRho ρ (Q + Q') ≤ nuRho ρ Q + nuRho ρ Q' := by
  refine Real.iSup_le (fun H => ?_) (add_nonneg (nu_nonneg Q) (nu_nonneg Q'))
  have e : ∑ a, ∑ b, (H : Matrix (Fin p) (Fin p) ℝ) a b * (Q + Q') a b =
      (∑ a, ∑ b, (H : Matrix (Fin p) (Fin p) ℝ) a b * Q a b) +
        ∑ a, ∑ b, (H : Matrix (Fin p) (Fin p) ℝ) a b * Q' a b := by
    simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  rw [e]
  exact (abs_add_le _ _).trans (add_le_add (nu_pair_le H hρ hc hc0 Q) (nu_pair_le H hρ hc hc0 Q'))

lemma nu_neg (Q : Matrix (Fin p) (Fin p) ℝ) : nuRho ρ (-Q) = nuRho ρ Q := by
  unfold nuRho
  refine iSup_congr fun H => ?_
  simp [Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib, abs_neg]

lemma abs_nu_sub_le (hρ : ∀ u, 0 ≤ ρ u) (hc : ∀ u, ρ u ≤ c * Real.sqrt (u ⬝ᵥ u)) (hc0 : 0 ≤ c)
    (Q Q' : Matrix (Fin p) (Fin p) ℝ) : nuRho ρ Q - nuRho ρ Q' ≤ nuRho ρ (Q - Q') := by
  have := nu_add_le hρ hc hc0 (Q - Q') Q'
  rw [sub_add_cancel] at this
  linarith

lemma continuous_nu (hρ : ∀ u, 0 ≤ ρ u) (hc : ∀ u, ρ u ≤ c * Real.sqrt (u ⬝ᵥ u)) (hc0 : 0 ≤ c) :
    Continuous (nuRho (p := p) ρ) := by
  rw [continuous_iff_continuousAt]
  intro Q'
  have hg : Continuous fun Q : Matrix (Fin p) (Fin p) ℝ => c ^ 2 * ∑ i, ∑ j, |(Q - Q') j i| := by
    fun_prop
  have hg' : Continuous fun Q : Matrix (Fin p) (Fin p) ℝ => c ^ 2 * ∑ i, ∑ j, |(Q' - Q) j i| := by
    fun_prop
  have h0 : Tendsto (fun Q : Matrix (Fin p) (Fin p) ℝ => c ^ 2 * ∑ i, ∑ j, |(Q - Q') j i|) (𝓝 Q') (𝓝 0) := by
    have := hg.tendsto Q'
    simpa using this
  have h0' : Tendsto (fun Q : Matrix (Fin p) (Fin p) ℝ => c ^ 2 * ∑ i, ∑ j, |(Q' - Q) j i|) (𝓝 Q') (𝓝 0) := by
    have := hg'.tendsto Q'
    simpa using this
  have hup : Tendsto (fun Q : Matrix (Fin p) (Fin p) ℝ => nuRho ρ Q' + c ^ 2 * ∑ i, ∑ j, |(Q - Q') j i|)
      (𝓝 Q') (𝓝 (nuRho ρ Q')) := by simpa using tendsto_const_nhds.add h0
  have hlo : Tendsto (fun Q : Matrix (Fin p) (Fin p) ℝ => nuRho ρ Q' - c ^ 2 * ∑ i, ∑ j, |(Q' - Q) j i|)
      (𝓝 Q') (𝓝 (nuRho ρ Q')) := by simpa using tendsto_const_nhds.sub h0'
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hup (fun Q => ?_) (fun Q => ?_)
  · have h1 := abs_nu_sub_le hρ hc hc0 Q' Q
    have h2 := nu_le_s1 hρ hc hc0 (Q' - Q)
    have h3 := s1Norm_le_sum (Q' - Q)
    have h4 : c ^ 2 * s1Norm (Q' - Q) ≤ c ^ 2 * ∑ i, ∑ j, |(Q' - Q) j i| :=
      mul_le_mul_of_nonneg_left h3 (sq_nonneg c)
    linarith
  · have h1 := abs_nu_sub_le hρ hc hc0 Q Q'
    have h2 := nu_le_s1 hρ hc hc0 (Q - Q')
    have h3 := s1Norm_le_sum (Q - Q')
    have h4 : c ^ 2 * s1Norm (Q - Q') ≤ c ^ 2 * ∑ i, ∑ j, |(Q - Q') j i| :=
      mul_le_mul_of_nonneg_left h3 (sq_nonneg c)
    linarith

lemma nu_jensen (hρ : ∀ u, 0 ≤ ρ u) (hc : ∀ u, ρ u ≤ c * Real.sqrt (u ⬝ᵥ u)) (hc0 : 0 ≤ c)
    (Qf : ℝ → Matrix (Fin p) (Fin p) ℝ) (a b : ℝ)
    (hent : ∀ i j, IntegrableOn (fun σ => Qf σ i j) (Set.Icc a b))
    (hs1 : IntegrableOn (fun σ => s1Norm (Qf σ)) (Set.Icc a b)) :
    nuRho ρ (covBlock Qf a b) ≤ ∫ σ in Set.Icc a b, nuRho ρ (Qf σ) := by
  have hcont := continuous_nu hρ hc hc0
  have hνint : IntegrableOn (fun σ => nuRho ρ (Qf σ)) (Set.Icc a b) := by
    refine Integrable.mono' (hs1.const_mul (c ^ 2)) ?_ (ae_of_all _ fun σ => ?_)
    · -- measurability: `Qf` entries are integrable, hence a.e. strongly measurable
      have hm : AEMeasurable Qf (volume.restrict (Set.Icc a b)) :=
        aemeasurable_pi_iff.2 fun i => aemeasurable_pi_iff.2 fun j =>
          (hent i j).aestronglyMeasurable.aemeasurable
      exact (hcont.measurable.comp_aemeasurable hm).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (nu_nonneg _)]
      exact nu_le_s1 hρ hc hc0 _
  refine Real.iSup_le (fun H => ?_) (setIntegral_nonneg measurableSet_Icc fun σ _ => nu_nonneg _)
  have e : ∀ Hm : Matrix (Fin p) (Fin p) ℝ, ∑ i, ∑ j, Hm i j * covBlock Qf a b i j =
      ∫ σ in Set.Icc a b, ∑ i, ∑ j, Hm i j * Qf σ i j := by
    intro Hm
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => (hent i j).const_mul (Hm i j))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => (hent i j).const_mul (Hm i j))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
    rfl
  rw [e (H : Matrix (Fin p) (Fin p) ℝ), ← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans ?_
  refine setIntegral_mono_on ?_ hνint measurableSet_Icc fun σ _ => ?_
  · exact (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hent i j).const_mul _).norm
  · rw [Real.norm_eq_abs]
    exact nu_pair_le H hρ hc hc0 (Qf σ)

/-- `ν_ρ` is a `PairNorm` whenever `ρ ≥ 0` is bounded by `c ‖u‖`. -/
lemma pairNorm_nu (hρ : ∀ u, 0 ≤ ρ u) (hc : ∀ u, ρ u ≤ c * Real.sqrt (u ⬝ᵥ u)) (hc0 : 0 ≤ c) :
    PairNorm (nuRho (p := p) ρ) (c ^ 2) where
  Cν_nonneg := sq_nonneg c
  nonneg := nu_nonneg
  le_s1 := nu_le_s1 hρ hc hc0
  cont := continuous_nu hρ hc hc0
  jensen := fun Qf a b hent hs1 => nu_jensen hρ hc hc0 Qf a b hent hs1

end

end HRS.Uniform.Q45
