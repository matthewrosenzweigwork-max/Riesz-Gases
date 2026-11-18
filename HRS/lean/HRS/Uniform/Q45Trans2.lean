import HRS.Uniform.Q45Trans1

/-!
# Q45 (Lemma 3.20): the covariance measure through an isometric embedding of a separable level
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

open Classical

namespace HRS.Uniform.Q45

theorem cov_transport (T K : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (H E E' : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
        [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
        [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [CompleteSpace E']
        [MeasurableSpace E'] [BorelSpace E'] [SecondCountableTopology E']
        (S : EvolData H E) (S' : EvolData H E') (_ : S'.MaxHyp T K) (ι : E' →ₗᵢ[ℝ] E)
        (_ : ∀ x, ι (S'.j x) = S.j x)
        (_ : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ∀ y, ι (S'.VE t r y) = S.VE t r (ι y)),
        ∃ J : (ℝ → H →L[ℝ] H →L[ℝ] ℝ) → VectorMeasure ℝ (ProjTensor2 (PathSp T E)),
          (∀ D, IsTraceDensityL1 T D →
            (∀ I, MeasurableSet I → J D I = J D (I ∩ Set.Icc 0 T)) ∧
            (∀ I, MeasurableSet I → ∀ Ψ : PathSp T E →L[ℝ] PathSp T E →L[ℝ] ℝ,
              tensorPairing Ψ (J D I) = tensorPairing Ψ.flip (J D I)) ∧
            (J D).variation (Set.Icc 0 T) ≤
              ENNReal.ofReal C * ∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (traceNormForm (D r)) ∧
            (∀ (t₁ t₂ : Set.Icc (0 : ℝ) T) (ℓ₁ ℓ₂ : E →L[ℝ] ℝ) (I : Set ℝ), MeasurableSet I →
              tensorPairing (obsForm t₁ t₂ ℓ₁ ℓ₂) (J D I) =
                ∫ r in I ∩ Set.Icc 0 (min (t₁ : ℝ) t₂), D r (pullbackVec S t₁ r ℓ₁) (pullbackVec S t₂ r ℓ₂)) ∧
            ContinuousOn (fun t => J D (Set.Icc 0 t)) (Set.Icc 0 T)) ∧
          (∀ D D', IsTraceDensityL1 T D → IsTraceDensityL1 T D' → ∀ a b : ℝ, ∀ I, MeasurableSet I →
            J (fun r => a • D r + b • D' r) I = a • J D I + b • J D' I) := by
  obtain ⟨C, hC0, hC⟩ := cov_family_sep T K hT
  refine ⟨C, hC0, ?_⟩
  intro H E E' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ S S' hS' ι hj hV
  obtain ⟨m', hm0, hm, hm5, hm4, hm6⟩ := hC H E' S' hS'
  set P : PathSp T E' →L[ℝ] PathSp T E := pathPush T ι.toContinuousLinearMap with hP
  have hP1 : ‖P‖ ≤ 1 := norm_pathPush_le ι
  let m : (ℝ → H →L[ℝ] H →L[ℝ] ℝ) → Set ℝ → ProjTensor2 (PathSp T E) := fun D I => tensorMap P (m' D I)
  have hT0 : (0 : ℝ) ≤ T := hT.le
  -- the pull-back identity
  have hpull : ∀ (t r : ℝ) (ℓ : E →L[ℝ] ℝ), pullbackVec S t r ℓ = pullbackVec S' t r (ℓ.comp ι.toContinuousLinearMap)
      ∨ ¬ (0 ≤ r ∧ r ≤ t ∧ t ≤ T) := by
    intro t r ℓ
    by_cases h : 0 ≤ r ∧ r ≤ t ∧ t ≤ T
    · left
      unfold pullbackVec
      congr 1
      ext x
      simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap]
      rw [hV r t h.1 h.2.1 h.2.2, hj]
    · right; exact h
  have hpull' : ∀ (t r : ℝ) (ℓ : E →L[ℝ] ℝ), 0 ≤ r → r ≤ t → t ≤ T →
      pullbackVec S t r ℓ = pullbackVec S' t r (ℓ.comp ι.toContinuousLinearMap) := by
    intro t r ℓ h1 h2 h3
    rcases hpull t r ℓ with h | h
    · exact h
    · exact absurd ⟨h1, h2, h3⟩ h
  have hobs : ∀ (t₁ t₂ : Set.Icc (0 : ℝ) T) (ℓ₁ ℓ₂ : E →L[ℝ] ℝ),
      (obsForm t₁ t₂ ℓ₁ ℓ₂).bilinearComp P P =
        obsForm t₁ t₂ (ℓ₁.comp ι.toContinuousLinearMap) (ℓ₂.comp ι.toContinuousLinearMap) := by
    intro t₁ t₂ ℓ₁ ℓ₂
    ext y y'
    simp only [ContinuousLinearMap.bilinearComp_apply, obsForm_apply, pcm_pathPush, hP,
      ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap]
  have hpair : ∀ (Ψ : PathSp T E →L[ℝ] PathSp T E →L[ℝ] ℝ) (τ : ProjTensor2 (PathSp T E')),
      tensorPairing Ψ (tensorMap P τ) = tensorPairing (Ψ.bilinearComp P P) τ := by
    intro Ψ τ
    rw [tensorPairing_eq, tensorPairing_eq, tensorPairing_tensorMap]
  have hmin : ∀ t₁ t₂ : Set.Icc (0 : ℝ) T, Set.Icc (0 : ℝ) (min (t₁ : ℝ) t₂) ⊆ Set.Icc 0 T :=
    fun t₁ t₂ => Set.Icc_subset_Icc_right ((min_le_left _ _).trans t₁.2.2)
  -- properties of `m`
  have hm_obs : ∀ D, IsTraceDensityL1 T D → ∀ I, MeasurableSet I →
      ∀ (t₁ t₂ : Set.Icc (0 : ℝ) T) (ℓ₁ ℓ₂ : E →L[ℝ] ℝ),
        tensorPairing (obsForm t₁ t₂ ℓ₁ ℓ₂) (m D I) =
          ∫ r in I ∩ Set.Icc 0 (min (t₁ : ℝ) t₂), D r (pullbackVec S t₁ r ℓ₁) (pullbackVec S t₂ r ℓ₂) := by
    intro D hD I hI t₁ t₂ ℓ₁ ℓ₂
    show tensorPairing _ (tensorMap P (m' D I)) = _
    rw [hpair, hobs, (hm D hD I hI).2.2 t₁ t₂ _ _]
    refine setIntegral_congr_fun (hI.inter measurableSet_Icc) fun r hr => ?_
    have hr' : 0 ≤ r ∧ r ≤ min (t₁ : ℝ) t₂ := hr.2
    rw [hpull' t₁ r ℓ₁ hr'.1 (hr'.2.trans (min_le_left _ _)) t₁.2.2,
      hpull' t₂ r ℓ₂ hr'.1 (hr'.2.trans (min_le_right _ _)) t₂.2.2]
  have hm_norm : ∀ D, IsTraceDensityL1 T D → ∀ I, MeasurableSet I →
      ‖m D I‖ ≤ C * ∫ r in I ∩ Set.Icc 0 T, traceNormForm (D r) := by
    intro D hD I hI
    refine (norm_tensorMap_le P _).trans ?_
    have : ‖P‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hP1
    exact (mul_le_of_le_one_left (norm_nonneg _) this).trans (hm D hD I hI).1
  have hm_add : ∀ D, IsTraceDensityL1 T D → ∀ I I', MeasurableSet I → MeasurableSet I' → Disjoint I I' →
      m D (I ∪ I') = m D I + m D I' := by
    intro D hD I I' hI hI' hd
    show tensorMap P (m' D (I ∪ I')) = tensorMap P (m' D I) + tensorMap P (m' D I')
    rw [hm4 D hD I I' hI hI' hd, map_add]
  -- the vector measures
  have hvm : ∀ D, IsTraceDensityL1 T D → ∃ v : VectorMeasure ℝ (ProjTensor2 (PathSp T E)),
      (∀ I, v I = m D I) ∧
      v.variation (Set.Icc 0 T) ≤ ENNReal.ofReal C * ∫⁻ r in Set.Icc 0 T, ENNReal.ofReal (traceNormForm (D r)) ∧
      ContinuousOn (fun t => v (Set.Icc 0 t)) (Set.Icc 0 T) := by
    intro D hD
    refine build_vm hC0 (tn := fun r => traceNormForm (D r)) (fun r => traceNormForm_nonneg _)
      hD.2.2.2 (m D) (fun I hI => ?_) (hm_norm D hD) (hm_add D hD)
    show tensorMap P (m' D I) = 0
    rw [hm0 D I hI, map_zero]
  let J : (ℝ → H →L[ℝ] H →L[ℝ] ℝ) → VectorMeasure ℝ (ProjTensor2 (PathSp T E)) := fun D =>
    if h : IsTraceDensityL1 T D then Classical.choose (hvm D h) else 0
  have hJ : ∀ D, IsTraceDensityL1 T D → ∀ I, J D I = m D I := by
    intro D hD I
    simp only [J, dif_pos hD]
    exact (Classical.choose_spec (hvm D hD)).1 I
  refine ⟨J, ?_, ?_⟩
  · intro D hD
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro I hI
      rw [hJ D hD, hJ D hD]
      show tensorMap P (m' D I) = tensorMap P (m' D (I ∩ Set.Icc 0 T))
      rw [hm5 D hD I hI]
    · intro I hI Ψ
      rw [hJ D hD]
      show tensorPairing Ψ (tensorMap P (m' D I)) = tensorPairing Ψ.flip (tensorMap P (m' D I))
      rw [hpair, hpair]
      have := (hm D hD I hI).2.1 (Ψ.bilinearComp P P)
      rw [this]
      congr 2
    · simp only [J, dif_pos hD]
      exact (Classical.choose_spec (hvm D hD)).2.1
    · intro t₁ t₂ ℓ₁ ℓ₂ I hI
      rw [hJ D hD]
      exact hm_obs D hD I hI t₁ t₂ ℓ₁ ℓ₂
    · simp only [J, dif_pos hD]
      exact (Classical.choose_spec (hvm D hD)).2.2
  · intro D D' hD hD' a b I hI
    have hl := isTraceDensityL1_lin hD hD' a b
    rw [hJ _ hl, hJ D hD, hJ D' hD']
    show tensorMap P (m' _ I) = a • tensorMap P (m' D I) + b • tensorMap P (m' D' I)
    rw [hm6 D D' hD hD' a b I hI, map_add, map_smul, map_smul]

end HRS.Uniform.Q45
