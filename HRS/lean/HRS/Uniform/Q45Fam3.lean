import HRS.Uniform.Q45Fam2

/-!
# Q45 (Lemma 3.20): the family of path tensors `𝒥_D(I)` in a separable space
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

open Classical

namespace HRS.Uniform.Q45

section Family

variable {H E : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma obs_integrable_D {S : EvolData H E} {T K : ℝ} (hT : 0 ≤ T) (hS : S.MaxHyp T K)
    {D : ℝ → H →L[ℝ] H →L[ℝ] ℝ} (hD : IsTraceDensityL1 T D)
    {t1 t2 : ℝ} (h1 : t1 ∈ Set.Icc (0 : ℝ) T) (h2 : t2 ∈ Set.Icc (0 : ℝ) T) (ℓ1 ℓ2 : E →L[ℝ] ℝ) :
    IntegrableOn (fun r => D r (pullbackVec S t1 r ℓ1) (pullbackVec S t2 r ℓ2)) (Set.Icc 0 (min t1 t2)) := by
  obtain ⟨Dp, Dm, hDp, hDm, hsum, -⟩ := jordan_density T D hD
  have hmin : Set.Icc (0 : ℝ) (min t1 t2) ⊆ Set.Icc 0 T := Set.Icc_subset_Icc_right
    ((min_le_left _ _).trans h1.2)
  have := (obs_integrable hT hS hDp h1 h2 ℓ1 ℓ2).sub (obs_integrable hT hS hDm h1 h2 ℓ1 ℓ2)
  refine this.congr_fun (fun r hr => ?_) measurableSet_Icc
  simp only [Pi.sub_apply, hsum r (hmin hr)]

theorem cov_family_sep (T K : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (H E : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
        [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
        [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
        (S : EvolData H E) (_ : S.MaxHyp T K),
        ∃ m : (ℝ → H →L[ℝ] H →L[ℝ] ℝ) → Set ℝ → ProjTensor2 (PathSp T E),
          (∀ D I, ¬ MeasurableSet I → m D I = 0) ∧
          (∀ D, IsTraceDensityL1 T D → ∀ I, MeasurableSet I → Spec S T C D I (m D I)) ∧
          (∀ D, IsTraceDensityL1 T D → ∀ I, MeasurableSet I → m D I = m D (I ∩ Set.Icc 0 T)) ∧
          (∀ D, IsTraceDensityL1 T D → ∀ I I', MeasurableSet I → MeasurableSet I' → Disjoint I I' →
            m D (I ∪ I') = m D I + m D I') ∧
          (∀ D D', IsTraceDensityL1 T D → IsTraceDensityL1 T D' → ∀ a b : ℝ, ∀ I, MeasurableSet I →
            m (fun r => a • D r + b • D' r) I = a • m D I + b • m D' I) := by
  obtain ⟨C, hC0, hC⟩ := gauss_tensor T K hT
  refine ⟨C, hC0, ?_⟩
  intro H E _ _ _ _ _ _ _ _ _ _ _ _ S hS
  have hg : ∀ Db : ℝ → H →L[ℝ] H →L[ℝ] ℝ, IsDetCovDensity T Db → ∃ τ : ProjTensor2 (PathSp T E),
      ‖τ‖ ≤ C * ∫ r in Set.Icc (0 : ℝ) T, traceNormForm (Db r) ∧
      (∀ Ψ : PathSp T E →L[ℝ] PathSp T E →L[ℝ] ℝ, tensorPairing Ψ τ = tensorPairing Ψ.flip τ) ∧
      (∀ (t₁ t₂ : Set.Icc (0 : ℝ) T) (ℓ₁ ℓ₂ : E →L[ℝ] ℝ),
        tensorPairing (obsForm t₁ t₂ ℓ₁ ℓ₂) τ =
          ∫ r in Set.Icc 0 (min (t₁ : ℝ) t₂), Db r (pullbackVec S t₁ r ℓ₁) (pullbackVec S t₂ r ℓ₂)) :=
    fun Db hDb => hC H E S hS Db hDb
  have hex : ∀ D, IsTraceDensityL1 T D → ∀ I, MeasurableSet I → ∃ τ, Spec S T C D I τ :=
    fun D hD I hI => exists_spec hT hS hg hC0 hD hI
  let m : (ℝ → H →L[ℝ] H →L[ℝ] ℝ) → Set ℝ → ProjTensor2 (PathSp T E) := fun D I =>
    if h : IsTraceDensityL1 T D ∧ MeasurableSet I then Classical.choose (hex D h.1 I h.2) else 0
  have hm : ∀ D, IsTraceDensityL1 T D → ∀ I, MeasurableSet I → Spec S T C D I (m D I) := by
    intro D hD I hI
    simp only [m, dif_pos (And.intro hD hI)]
    exact Classical.choose_spec (hex D hD I hI)
  have hT0 : (0 : ℝ) ≤ T := hT.le
  have hmin : ∀ t₁ t₂ : Set.Icc (0 : ℝ) T, Set.Icc (0 : ℝ) (min (t₁ : ℝ) t₂) ⊆ Set.Icc 0 T :=
    fun t₁ t₂ => Set.Icc_subset_Icc_right ((min_le_left _ _).trans t₁.2.2)
  refine ⟨m, ?_, hm, ?_, ?_, ?_⟩
  · intro D I hI
    simp only [m, dif_neg (fun h : IsTraceDensityL1 T D ∧ MeasurableSet I => hI h.2)]
  · intro D hD I hI
    refine obs_unique hT (hm D hD I hI).2.2 ?_
    intro t₁ t₂ ℓ₁ ℓ₂
    have := (hm D hD (I ∩ Set.Icc 0 T) (hI.inter measurableSet_Icc)).2.2 t₁ t₂ ℓ₁ ℓ₂
    rw [this]
    have e : I ∩ Set.Icc 0 T ∩ Set.Icc 0 (min (t₁ : ℝ) t₂) = I ∩ Set.Icc 0 (min (t₁ : ℝ) t₂) := by
      ext r; simp only [Set.mem_inter_iff]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hmin t₁ t₂ h.2⟩, h.2⟩⟩
    rw [e]
  · intro D hD I I' hI hI' hdisj
    refine obs_unique hT (hm D hD (I ∪ I') (hI.union hI')).2.2 ?_
    intro t₁ t₂ ℓ₁ ℓ₂
    have hint := obs_integrable_D hT0 hS hD t₁.2 t₂.2 ℓ₁ ℓ₂
    have hadd : tensorPairing (obsForm t₁ t₂ ℓ₁ ℓ₂) (m D I + m D I') =
        tensorPairing (obsForm t₁ t₂ ℓ₁ ℓ₂) (m D I) + tensorPairing (obsForm t₁ t₂ ℓ₁ ℓ₂) (m D I') := by
      simp only [tensorPairing_eq, map_add]
    rw [hadd, (hm D hD I hI).2.2 t₁ t₂ ℓ₁ ℓ₂, (hm D hD I' hI').2.2 t₁ t₂ ℓ₁ ℓ₂,
      Set.union_inter_distrib_right,
      setIntegral_union (hdisj.mono Set.inter_subset_left Set.inter_subset_left)
        (hI'.inter measurableSet_Icc) (hint.mono_set Set.inter_subset_right)
        (hint.mono_set Set.inter_subset_right)]
  · intro D D' hD hD' a b I hI
    refine obs_unique hT (hm _ (isTraceDensityL1_lin hD hD' a b) I hI).2.2 ?_
    intro t₁ t₂ ℓ₁ ℓ₂
    have hint := obs_integrable_D hT0 hS hD t₁.2 t₂.2 ℓ₁ ℓ₂
    have hint' := obs_integrable_D hT0 hS hD' t₁.2 t₂.2 ℓ₁ ℓ₂
    have hlin : tensorPairing (obsForm t₁ t₂ ℓ₁ ℓ₂) (a • m D I + b • m D' I) =
        a * tensorPairing (obsForm t₁ t₂ ℓ₁ ℓ₂) (m D I) + b * tensorPairing (obsForm t₁ t₂ ℓ₁ ℓ₂) (m D' I) := by
      simp only [tensorPairing_eq, map_add, map_smul, smul_eq_mul]
    rw [hlin, (hm D hD I hI).2.2 t₁ t₂ ℓ₁ ℓ₂, (hm D' hD' I hI).2.2 t₁ t₂ ℓ₁ ℓ₂]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [integral_add ((hint.mono_set Set.inter_subset_right).const_mul a)
      ((hint'.mono_set Set.inter_subset_right).const_mul b), integral_const_mul, integral_const_mul]

end Family

end HRS.Uniform.Q45
