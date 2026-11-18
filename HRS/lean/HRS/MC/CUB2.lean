import HRS.MC.CUB1
import HRS.Main.HeadlineEdgeworth
import HRS.Main.ThermLinFinal

/-!
# Cubic tensor uniqueness, part 2: agreement on evaluation functionals and the main proof

Two tensors satisfying `SatisfiesCubicFormula` agree on every product of evaluation functionals
`ℓ_{t,k}` (`t ∈ [0,T]`, `k` a nonzero frequency), provided the cross-covariance densities exist
(`CrossCovDensitiesExist`); the finite-rank form of `projPoly` then gives `P_L^{⊗3} K₁ = P_L^{⊗3} K₂`
and the strong convergence `P_L^{⊗3} → id` on `projTensor` gives `K₁ = K₂`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory

namespace HRS.MC.CUB

open HRS HRS.Sec7 HRS.Main HRS.MC.Sec7.S7PIC

set_option maxSynthPendingDepth 3

variable {d : ℕ}

/-- Existence of a witness `(ν, Ω', P', Z₀, Z)` for the cubic formula. -/
theorem witness_exists (S : PreparedData d) (β₀ m T a : ℝ) (hE : EdgeworthHyp S β₀ m)
    (hT : 0 < T) (ha : 0 ≤ a) :
    ∃ ν : Measure (NegSobolev d m), IsCenteredGaussianWithCov m ν (preparedCov d S.s β₀ S.μ0) ∧
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
        (Z₀ : Ω' → NegSobolev d m) (Z : ℝ → Ω' → NegSobolev d m), IsPreparedLinear S m (a + T) ν P' Z₀ Z := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hm := hE.m_gt
  obtain ⟨ν, hν, hνc⟩ := preparedGaussian_exists_proof S β₀ hE.β₀_nonneg m (by linarith)
  refine ⟨ν, hνc, ?_⟩
  have := hν
  obtain ⟨Ω', hΩ, P', hP', Z₀, Z, hZ⟩ :=
    preparedLinear_exists_proof S m (by linarith) (a + T) (by linarith) ν
  exact ⟨Ω', hΩ, P', hP', Z₀, Z, hZ⟩

theorem pathEval_eq_pathAt {m T : ℝ} (w : PathSpace d m T) (t : Set.Icc (0 : ℝ) T) :
    pathEval w (t : ℝ) = pathAt w (t : ℝ) := by
  unfold pathEval pathAt
  rw [dif_pos t.2]

/-- Two tensors with the cubic formula agree on products of evaluation functionals. -/
theorem agree_lf (S : PreparedData d) (β₀ m T a : ℝ) (hE : EdgeworthHyp S β₀ m)
    (hT : 0 < T) (ha : 0 ≤ a) (hχ : CrossCovDensitiesExist S β₀ m T a)
    (K₁ K₂ : projTensor (PathSpace d m T) 3)
    (h₁ : SatisfiesCubicFormula S β₀ m T a K₁) (h₂ : SatisfiesCubicFormula S β₀ m T a K₂)
    (n : Fin 3 → Set.Icc (0 : ℝ) T) (k : Fin 3 → NonzeroLattice d) :
    ((K₁ : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3)
        (prodFormN 3 (fun i => S7PIC_lf m T (n i) (k i))) =
      ((K₂ : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3)
        (prodFormN 3 (fun i => S7PIC_lf m T (n i) (k i))) := by
  obtain ⟨ν, hν, Ω', hΩ, P', hP', Z₀, Z, hZ⟩ := witness_exists S β₀ m T a hE hT ha
  set t : Fin 3 → ℝ := fun i => a + (n i : ℝ) with ht_def
  set φ : Fin 3 → Torus d → ℝ := fun i => Torus.realMode (k i) with hφ_def
  have ht : ∀ i, t i ∈ Set.Icc a (a + T) := fun i =>
    ⟨le_add_of_nonneg_right (n i).2.1, by linarith [(n i).2.2]⟩
  have hφ : ∀ i, Torus.IsSmooth (φ i) := fun i => FieldSingAux.isSmooth_realMode (k i)
  have hℓ : ∀ i w, S7PIC_lf m T (n i) (k i) w = NegSobolev.eval (pathEval w (t i - a)) (φ i) := by
    intro i w
    have : t i - a = (n i : ℝ) := by simp [ht_def]
    rw [this, pathEval_eq_pathAt, S7PIC_lf_eq_eval]
  obtain ⟨χ, hχs, hχc⟩ := hχ t φ ht hφ ν hν P' Z₀ Z hZ
  have e₁ := h₁ t φ ht hφ (fun i => S7PIC_lf m T (n i) (k i)) hℓ ν hν P' Z₀ Z hZ χ hχs hχc
  have e₂ := h₂ t φ ht hφ (fun i => S7PIC_lf m T (n i) (k i)) hℓ ν hν P' Z₀ Z hZ χ hχs hχc
  exact e₁.trans e₂.symm

theorem cubic_tensor_unique_proof (S : PreparedData d) (β₀ m T a : ℝ) (hE : EdgeworthHyp S β₀ m)
    (hT : 0 < T) (ha : 0 ≤ a) (hχ : CrossCovDensitiesExist S β₀ m T a)
    (K₁ K₂ : projTensor (PathSpace d m T) 3)
    (h₁ : SatisfiesCubicFormula S β₀ m T a K₁) (h₂ : SatisfiesCubicFormula S β₀ m T a K₂) :
    K₁ = K₂ := by
  obtain ⟨Pj, hPj, hnorm, hconv, hten⟩ := projection_strong_proof (d := d) m T hT
  refine Subtype.ext ?_
  refine eq_of_proj Pj _ _ (hten 3 _ K₁.2) (hten 3 _ K₂.2) (fun L => ?_)
  refine tensorPow_eq_of_agree 3 (Pj L)
    (fun a : Fin (2 ^ L + 1) × ↥(S7PIC_box d L) => S7PIC_lf m T (S7PIC_node T hT.le L a.1) a.2)
    (fun a => S7PIC_vpath m T L a.1 a.2) (fun w => ?_) _ _ (fun r => ?_)
  · rw [hPj, S7PIC_projPoly_eq_sum]
  · exact agree_lf S β₀ m T a hE hT ha hχ K₁ K₂ h₁ h₂ (fun i => S7PIC_node T hT.le L (r i).1)
      (fun i => (r i).2)

end HRS.MC.CUB
