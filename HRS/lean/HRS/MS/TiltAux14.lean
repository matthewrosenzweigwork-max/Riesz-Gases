import HRS.MS.TiltAux13

/-!
# S4.7 packet P9: `tilt_static` and `tilt_static_mean_field`

`tilt_static_proof`: the feature form `s47_conclusion` rewritten from `s47_P` to `modulatedGibbs g N γ μ₀`.
`tilt_static_mean_field_proof`: `Y_N = featureVec φ μ₀ X` differs from the exactly centred `X_N = featureVec φ ν X` by the
deterministic vector `b_j = √N (ν - μ₀)(φ_j)`, `‖b‖_{ℓ²} ≤ ‖b‖_{ℓ¹} ≤ √N C_s δ_N S` (`s47_bias`), and `F` is `D₁`-Lipschitz.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S47

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

/-- **S4.7, exactly centred part.** -/
theorem tilt_static_proof : type_of% @HRS.Whole.tilt_static := by
  intro d s hd hs0 hsd J hJ am ap βm βp γm γp ham hβm hγm εstar
  obtain ⟨C, Cs, hCs, h⟩ := s47_conclusion_unif hd hs0 hsd J hJ am ap βm βp γm γp ham hβm hγm εstar
  refine ⟨C, fun a ha β hβ γ hγ ε ψ hε hcb φ hφ N hN Zg hZg => ?_⟩
  obtain ⟨h1, -, hP, -⟩ := h a ha β hβ γ hγ ε ψ hε hcb φ hφ N hN Zg hZg
  rw [← hP]
  exact h1

/-- **S4.7, mean-field-centred part.** -/
theorem tilt_static_mean_field_proof : type_of% @HRS.Whole.tilt_static_mean_field := by
  intro d s hd hs0 hsd J hJ am ap βm βp γm γp ham hβm hγm εstar
  obtain ⟨C1, Cs, hCs, h⟩ := s47_conclusion_unif hd hs0 hsd J hJ am ap βm βp γm γp ham hβm hγm εstar
  refine ⟨max (max C1 Cs) 0, fun a ha β hβ γ hγ ε ψ hε hcb φ hφ N hN Zg hZg F hF D₁ D₂ hD₁ hD₂ => ?_⟩
  obtain ⟨hSFC, hbias, hP, hprob, hPprob⟩ := h a ha β hβ γ hγ ε ψ hε hcb φ hφ N hN Zg hZg
  rw [← hP]
  have hN1 : 1 ≤ N := by omega
  set ρ : Euc d → ℝ := perturbedDensity (thermalDensity d s a β) ε ψ with hρdef
  set P := s47_P d s ρ γ N with hPdef
  haveI : IsProbabilityMeasure P := hPprob
  haveI hμ : IsProbabilityMeasure (tiltedMeasure d s a β ε ψ) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hprob
  obtain ⟨hm1, hm2, hm3, hm4⟩ := hSFC
  haveI hν : IsProbabilityMeasure (s47_nu d s ρ γ N) := s47_nu_prob hN hPprob
  have hD₁0 : 0 ≤ D₁ := (norm_nonneg _).trans (hD₁ 0)
  have hD₂0 : 0 ≤ D₂ := (norm_nonneg _).trans (hD₂ 0)
  obtain ⟨i1, i2, i3⟩ := hm4 F hF D₁ D₂ hD₁ hD₂
  set S := featureSum J φ with hSdef
  have hS0 : 0 ≤ S := tsum_nonneg fun i => HRS.MS.Tc5.tc5_cb_nonneg J (φ i)
  set δ := HRS.deltaN d s N with hδdef
  have hδ0 : 0 ≤ δ := HRS.deltaN_nonneg s hN1
  have hδs : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg _
  have hsN : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  -- the difference of the two centred vectors
  set B : ℝ := Real.sqrt N * (Cs * δ) * S with hBdef
  have hdiff : ∀ X : EucConfig d N, ‖featureVec φ (tiltedMeasure d s a β ε ψ) X -
      featureVec φ (s47_nu d s ρ γ N) X‖ ≤ B := by
    intro X
    have hb : Summable fun j => Real.sqrt N * (Cs * δ) * cbNorm J (φ j) := hφ.2.mul_left _
    have h1 := s45_norm_le_tsum (z := featureVec φ (tiltedMeasure d s a β ε ψ) X -
      featureVec φ (s47_nu d s ρ γ N) X) hb (fun j => by
        have e1 : SeqL2.coord (featureVec φ (tiltedMeasure d s a β ε ψ) X) j =
            Real.sqrt N * (pair (empirical X) (φ j) - pair (tiltedMeasure d s a β ε ψ) (φ j)) := by
          unfold featureVec
          rw [s45_coord_ofSeq (s45_feature_memℓp hN1 hφ X)]
        have e2 : SeqL2.coord (featureVec φ (s47_nu d s ρ γ N) X) j =
            Real.sqrt N * (pair (empirical X) (φ j) - pair (s47_nu d s ρ γ N) (φ j)) := by
          unfold featureVec
          rw [s45_coord_ofSeq (s45_feature_memℓp hN1 hφ X)]
        have e3 : SeqL2.coord (featureVec φ (tiltedMeasure d s a β ε ψ) X -
            featureVec φ (s47_nu d s ρ γ N) X) j =
            SeqL2.coord (featureVec φ (tiltedMeasure d s a β ε ψ) X) j -
              SeqL2.coord (featureVec φ (s47_nu d s ρ γ N) X) j := rfl
        rw [e3, e1, e2]
        have hbj : ∀ x, |φ j x| ≤ cbNorm J (φ j) := fun x => by
          have := HRS.MS.Tc5.tc5_cb_sup_le (hφ.1 j) x
          rwa [Real.norm_eq_abs] at this
        have hb1 := hbias (φ j) (hφ.1 j).1.continuous.measurable (cbNorm J (φ j)) hbj
        have : Real.sqrt N * (pair (empirical X) (φ j) - pair (tiltedMeasure d s a β ε ψ) (φ j)) -
            Real.sqrt N * (pair (empirical X) (φ j) - pair (s47_nu d s ρ γ N) (φ j)) =
            Real.sqrt N * (pair (s47_nu d s ρ γ N) (φ j) - pair (tiltedMeasure d s a β ε ψ) (φ j)) := by
          ring
        rw [this, abs_mul, abs_of_nonneg hsN]
        calc Real.sqrt N * |pair (s47_nu d s ρ γ N) (φ j) - pair (tiltedMeasure d s a β ε ψ) (φ j)|
            ≤ Real.sqrt N * (cbNorm J (φ j) * (Cs * δ)) := mul_le_mul_of_nonneg_left hb1 hsN
          _ = _ := by ring)
    refine h1.trans (le_of_eq ?_)
    rw [tsum_mul_left]
    rw [hBdef, hSdef]
    unfold featureSum
    ring
  have hB0 : 0 ≤ B := by
    have : 0 ≤ Cs := hCs
    positivity
  -- `F` is `D₁`-Lipschitz
  have hFlip : ∀ z w : SeqL2, ‖F z - F w‖ ≤ D₁ * ‖z - w‖ := fun z w => by
    have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := F) (s := Set.univ) (x := w) (y := z)
      (fun y _ => (hF.differentiable (by norm_num)) y) (fun y _ => hD₁ y) convex_univ trivial trivial
    exact this
  have hpt : ∀ X : EucConfig d N,
      ‖F (featureVec φ (tiltedMeasure d s a β ε ψ) X) - F (featureVec φ (s47_nu d s ρ γ N) X)‖ ≤ D₁ * B :=
    fun X => (hFlip _ _).trans (mul_le_mul_of_nonneg_left (hdiff X) hD₁0)
  have hfmY : Measurable (featureVec φ (tiltedMeasure d s a β ε ψ) : EucConfig d N → SeqL2) :=
    s45_feature_measurable hN1 hφ
  have hgY : AEStronglyMeasurable (fun X => F (featureVec φ (tiltedMeasure d s a β ε ψ) X)) P :=
    (hF.continuous.measurable.comp hfmY).aestronglyMeasurable
  have hiY : Integrable (fun X => F (featureVec φ (tiltedMeasure d s a β ε ψ) X)) P := by
    refine Integrable.mono' (g := fun X => ‖F (featureVec φ (s47_nu d s ρ γ N) X)‖ + D₁ * B)
      (i1.norm.add (integrable_const _)) hgY (Filter.Eventually.of_forall fun X => ?_)
    have h := hpt X
    have := norm_le_norm_add_norm_sub' (F (featureVec φ (tiltedMeasure d s a β ε ψ) X))
      (F (featureVec φ (s47_nu d s ρ γ N) X))
    calc ‖F (featureVec φ (tiltedMeasure d s a β ε ψ) X)‖
        ≤ ‖F (featureVec φ (s47_nu d s ρ γ N) X)‖ +
          ‖F (featureVec φ (tiltedMeasure d s a β ε ψ) X) - F (featureVec φ (s47_nu d s ρ γ N) X)‖ := by
          have := norm_le_insert' (F (featureVec φ (tiltedMeasure d s a β ε ψ) X))
            (F (featureVec φ (s47_nu d s ρ γ N) X))
          linarith
      _ ≤ _ := by linarith
  refine ⟨hiY, i2, ?_⟩
  -- the comparison
  have hdI : |∫ X, F (featureVec φ (tiltedMeasure d s a β ε ψ) X) ∂P -
      ∫ X, F (featureVec φ (s47_nu d s ρ γ N) X) ∂P| ≤ D₁ * B := by
    rw [← integral_sub hiY i1]
    have := norm_integral_le_of_norm_le_const (μ := P)
      (f := fun X => F (featureVec φ (tiltedMeasure d s a β ε ψ) X) -
        F (featureVec φ (s47_nu d s ρ γ N) X)) (C := D₁ * B)
      (Filter.Eventually.of_forall hpt)
    simpa [Real.norm_eq_abs] using this
  have hmain : |∫ X, F (featureVec φ (tiltedMeasure d s a β ε ψ) X) ∂P - ∫ z, F z ∂Zg| ≤
      D₁ * B + C1 * Real.sqrt δ * (S * D₁ + S ^ 2 * D₂) := by
    calc _ = |(∫ X, F (featureVec φ (tiltedMeasure d s a β ε ψ) X) ∂P -
          ∫ X, F (featureVec φ (s47_nu d s ρ γ N) X) ∂P) +
          (∫ X, F (featureVec φ (s47_nu d s ρ γ N) X) ∂P - ∫ z, F z ∂Zg)| := by ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add hdI i3)
  refine hmain.trans ?_
  set C' : ℝ := max (max C1 Cs) 0 with hC'
  have hC1 : C1 ≤ C' := (le_max_left _ _).trans (le_max_left _ _)
  have hCsC : Cs ≤ C' := (le_max_right _ _).trans (le_max_left _ _)
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have x1 : 0 ≤ S * D₁ * (Real.sqrt N * δ) := by positivity
  have x2 : 0 ≤ S * D₁ * Real.sqrt δ := by positivity
  have x3 : 0 ≤ S ^ 2 * D₂ * Real.sqrt δ := by positivity
  have e1 : D₁ * B = Cs * (S * D₁ * (Real.sqrt N * δ)) := by rw [hBdef]; ring
  have e2 : C1 * Real.sqrt δ * (S * D₁ + S ^ 2 * D₂) = C1 * (S * D₁ * Real.sqrt δ + S ^ 2 * D₂ * Real.sqrt δ) := by
    ring
  have e3 : C' * (S * D₁ * (Real.sqrt N * δ + Real.sqrt δ) + S ^ 2 * D₂ * Real.sqrt δ) =
      C' * (S * D₁ * (Real.sqrt N * δ)) + C' * (S * D₁ * Real.sqrt δ + S ^ 2 * D₂ * Real.sqrt δ) := by ring
  rw [e1, e2, e3]
  exact add_le_add (mul_le_mul_of_nonneg_right hCsC x1) (mul_le_mul_of_nonneg_right hC1 (by positivity))

end S47

end
