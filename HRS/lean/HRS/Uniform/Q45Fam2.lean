import HRS.Uniform.Q45Fam1

/-!
# Q45 (Lemma 3.20): existence of the path tensor of a signed trace density restricted to a set
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

open Classical

namespace HRS.Uniform.Q45

section Spec

variable {H E : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The properties of the path tensor `𝒥_D(I)`. -/
def ObsFormula (S : EvolData H E) (T : ℝ) (D : ℝ → H →L[ℝ] H →L[ℝ] ℝ) (I : Set ℝ)
    (τ : ProjTensor2 (PathSp T E)) : Prop :=
  ∀ (t₁ t₂ : Set.Icc (0 : ℝ) T) (ℓ₁ ℓ₂ : E →L[ℝ] ℝ),
    tensorPairing (obsForm t₁ t₂ ℓ₁ ℓ₂) τ =
      ∫ r in I ∩ Set.Icc 0 (min (t₁ : ℝ) t₂), D r (pullbackVec S t₁ r ℓ₁) (pullbackVec S t₂ r ℓ₂)

def Spec (S : EvolData H E) (T C : ℝ) (D : ℝ → H →L[ℝ] H →L[ℝ] ℝ) (I : Set ℝ)
    (τ : ProjTensor2 (PathSp T E)) : Prop :=
  ‖τ‖ ≤ C * ∫ r in I ∩ Set.Icc 0 T, traceNormForm (D r) ∧
  (∀ Ψ : PathSp T E →L[ℝ] PathSp T E →L[ℝ] ℝ, tensorPairing Ψ τ = tensorPairing Ψ.flip τ) ∧
  ObsFormula S T D I τ

lemma tensorPairing_sub {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (Ψ : Y →L[ℝ] Y →L[ℝ] ℝ)
    (a b : ProjTensor2 Y) : tensorPairing Ψ (a - b) = tensorPairing Ψ a - tensorPairing Ψ b := by
  simp only [tensorPairing_eq, map_sub]

lemma obs_unique {S : EvolData H E} {T : ℝ} (hT : 0 < T) {D : ℝ → H →L[ℝ] H →L[ℝ] ℝ} {I : Set ℝ}
    {τ τ' : ProjTensor2 (PathSp T E)} (h : ObsFormula S T D I τ) (h' : ObsFormula S T D I τ') :
    τ = τ' := by
  have := obs_separate hT (τ - τ') (fun t₁ t₂ ℓ₁ ℓ₂ => by
    rw [tensorPairing_sub, h t₁ t₂ ℓ₁ ℓ₂, h' t₁ t₂ ℓ₁ ℓ₂, sub_self])
  exact sub_eq_zero.1 this

lemma exists_spec {S : EvolData H E} {T K C : ℝ} (hT : 0 < T) (hS : S.MaxHyp T K)
    (hg : ∀ Db : ℝ → H →L[ℝ] H →L[ℝ] ℝ, IsDetCovDensity T Db →
      ∃ τ : ProjTensor2 (PathSp T E),
        ‖τ‖ ≤ C * ∫ r in Set.Icc (0 : ℝ) T, traceNormForm (Db r) ∧
        (∀ Ψ : PathSp T E →L[ℝ] PathSp T E →L[ℝ] ℝ, tensorPairing Ψ τ = tensorPairing Ψ.flip τ) ∧
        (∀ (t₁ t₂ : Set.Icc (0 : ℝ) T) (ℓ₁ ℓ₂ : E →L[ℝ] ℝ),
          tensorPairing (obsForm t₁ t₂ ℓ₁ ℓ₂) τ =
            ∫ r in Set.Icc 0 (min (t₁ : ℝ) t₂), Db r (pullbackVec S t₁ r ℓ₁) (pullbackVec S t₂ r ℓ₂)))
    (hC0 : 0 ≤ C) {D : ℝ → H →L[ℝ] H →L[ℝ] ℝ} (hD : IsTraceDensityL1 T D) {I : Set ℝ}
    (hI : MeasurableSet I) : ∃ τ, Spec S T C D I τ := by
  obtain ⟨Dp, Dm, hDp, hDm, hsum, htr⟩ := jordan_density T D hD
  obtain ⟨τp, hp1, hp2, hp3⟩ := hg _ (isDetCov_ind hDp hI)
  obtain ⟨τm, hm1, hm2, hm3⟩ := hg _ (isDetCov_ind hDm hI)
  have hTpos : (0 : ℝ) ≤ T := hT.le
  refine ⟨τp - τm, ?_, ?_, ?_⟩
  · -- norm bound
    have e : ∀ Q : ℝ → H →L[ℝ] H →L[ℝ] ℝ,
        ∫ r in Set.Icc (0 : ℝ) T, traceNormForm (if r ∈ I then Q r else 0) =
          ∫ r in I ∩ Set.Icc 0 T, traceNormForm (Q r) := by
      intro Q
      have : (fun r => traceNormForm (if r ∈ I then Q r else (0 : H →L[ℝ] H →L[ℝ] ℝ))) =
          I.indicator (fun r => traceNormForm (Q r)) := by
        funext r
        by_cases h : r ∈ I <;> simp [h, traceNormForm_zero]
      rw [this, setIntegral_indicator hI, Set.inter_comm]
    rw [e] at hp1 hm1
    refine (norm_sub_le _ _).trans ?_
    have hJ : MeasurableSet (I ∩ Set.Icc (0 : ℝ) T) := hI.inter measurableSet_Icc
    have hiD : IntegrableOn (fun r => traceNormForm (D r)) (I ∩ Set.Icc 0 T) :=
      hD.2.2.2.mono_set Set.inter_subset_right
    have hip : IntegrableOn (fun r => traceNormForm (Dp r)) (I ∩ Set.Icc 0 T) :=
      hDp.int.mono_set Set.inter_subset_right
    have him : IntegrableOn (fun r => traceNormForm (Dm r)) (I ∩ Set.Icc 0 T) :=
      hDm.int.mono_set Set.inter_subset_right
    have h3 : (∫ r in I ∩ Set.Icc 0 T, traceNormForm (Dp r)) + (∫ r in I ∩ Set.Icc 0 T, traceNormForm (Dm r)) ≤
        ∫ r in I ∩ Set.Icc 0 T, traceNormForm (D r) := by
      rw [← integral_add hip him]
      refine setIntegral_mono_on (hip.add him) hiD hJ fun r hr => htr r hr.2
    nlinarith
  · intro Ψ
    rw [tensorPairing_sub, tensorPairing_sub, hp2, hm2]
  · intro t₁ t₂ ℓ₁ ℓ₂
    have hmin : Set.Icc (0 : ℝ) (min (t₁ : ℝ) t₂) ⊆ Set.Icc 0 T := Set.Icc_subset_Icc_right
      ((min_le_left _ _).trans t₁.2.2)
    rw [tensorPairing_sub, hp3, hm3]
    set J : Set ℝ := I ∩ Set.Icc 0 (min (t₁ : ℝ) t₂) with hJ
    have hJm : MeasurableSet J := hI.inter measurableSet_Icc
    have hind : ∀ Q : ℝ → H →L[ℝ] H →L[ℝ] ℝ,
        ∫ r in Set.Icc 0 (min (t₁ : ℝ) t₂), (if r ∈ I then Q r else 0) (pullbackVec S t₁ r ℓ₁) (pullbackVec S t₂ r ℓ₂) =
          ∫ r in J, Q r (pullbackVec S t₁ r ℓ₁) (pullbackVec S t₂ r ℓ₂) := by
      intro Q
      have : (fun r => (if r ∈ I then Q r else (0 : H →L[ℝ] H →L[ℝ] ℝ)) (pullbackVec S t₁ r ℓ₁) (pullbackVec S t₂ r ℓ₂)) =
          I.indicator (fun r => Q r (pullbackVec S t₁ r ℓ₁) (pullbackVec S t₂ r ℓ₂)) := by
        funext r
        by_cases h : r ∈ I <;> simp [h]
      rw [this, setIntegral_indicator hI, Set.inter_comm]
    rw [hind, hind]
    have hmem1 := obs_integrable hTpos hS hDp t₁.2 t₂.2 ℓ₁ ℓ₂
    have hmem2 := obs_integrable hTpos hS hDm t₁.2 t₂.2 ℓ₁ ℓ₂
    rw [← integral_sub (hmem1.mono_set Set.inter_subset_right) (hmem2.mono_set Set.inter_subset_right)]
    refine setIntegral_congr_fun hJm fun r hr => ?_
    have hrT : r ∈ Set.Icc 0 T := hmin hr.2
    simp only [hsum r hrT, ContinuousLinearMap.sub_apply]

end Spec

end HRS.Uniform.Q45
