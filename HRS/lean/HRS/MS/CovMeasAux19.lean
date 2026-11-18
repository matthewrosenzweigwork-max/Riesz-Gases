import HRS.MS.CovMeasAux18

/-!
# S10.1 (worker S101B), part 19: properties of the abstract covariance measure and a.e.-invariance

`S101Jprops T C0 J` collects the clauses of `HRS.Uniform.covariance_measure_proof` for the identity evolution on `𝒦`.
`s101_J_congr`: if two trace densities agree a.e. on `[0,T]` then the measures agree (the difference has total variation `0`).
`s101_edist_sum_le`: the total-variation bound for the cumulative function.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.CovMeas

open HRS HRS.Whole HRS.Uniform HRS.Uniform.Q45 HRS.MS.GenPath

variable {d : ℕ} {m T : ℝ}

/-- The clauses of the abstract covariance measure, for the identity evolution on `𝒦`. -/
structure S101Jprops (T C0 : ℝ)
    (J : (ℝ → KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ) → VectorMeasure ℝ (ProjTensor2 (PathSp T (KSpace d m T)))) :
    Prop where
  supp : ∀ D, IsTraceDensityL1 T D → ∀ I, MeasurableSet I → J D I = J D (I ∩ Icc 0 T)
  tv : ∀ D, IsTraceDensityL1 T D →
    (J D).variation (Icc 0 T) ≤ ENNReal.ofReal C0 * ∫⁻ r in Icc (0 : ℝ) T, ENNReal.ofReal (traceNormForm (D r))
  obs : ∀ D, IsTraceDensityL1 T D → ∀ (t₁ t₂ : Icc (0 : ℝ) T) (ℓ₁ ℓ₂ : KSpace d m T →L[ℝ] ℝ) (I : Set ℝ),
    MeasurableSet I → tensorPairing (obsForm t₁ t₂ ℓ₁ ℓ₂) (J D I) =
      ∫ r in I ∩ Icc 0 (min (t₁ : ℝ) t₂), D r (pullbackVec (s56_idEvol (KSpace d m T)) t₁ r ℓ₁)
        (pullbackVec (s56_idEvol (KSpace d m T)) t₂ r ℓ₂)
  cont : ∀ D, IsTraceDensityL1 T D → ContinuousOn (fun t => J D (Icc 0 t)) (Icc 0 T)
  lin : ∀ D D', IsTraceDensityL1 T D → IsTraceDensityL1 T D' → ∀ a b : ℝ, ∀ I, MeasurableSet I →
    J (fun r => a • D r + b • D' r) I = a • J D I + b • J D' I

theorem traceNormForm_zero_eq :
    traceNormForm (0 : KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ) = 0 := by
  refine le_antisymm ?_ (traceNormForm_nonneg _)
  unfold traceNormForm
  exact Real.iSup_le (fun p => by simp) le_rfl

theorem s101_J_congr {C0 : ℝ}
    {J : (ℝ → KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ) → VectorMeasure ℝ (ProjTensor2 (PathSp T (KSpace d m T)))}
    (hJ : S101Jprops T C0 J) {D₁ D₂ : ℝ → KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ}
    (h₁ : IsTraceDensityL1 T D₁) (h₂ : IsTraceDensityL1 T D₂)
    (hae : ∀ᵐ τ ∂(volume.restrict (Icc (0 : ℝ) T)), D₁ τ = D₂ τ) {I : Set ℝ} (hI : MeasurableSet I) :
    J D₁ I = J D₂ I := by
  set E : ℝ → KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ := fun r => (1 : ℝ) • D₁ r + (-1 : ℝ) • D₂ r with hE
  have hEr : ∀ r x y, E r x y = D₁ r x y - D₂ r x y := by
    intro r x y; simp [hE, sub_eq_add_neg]
  have hEae : ∀ᵐ τ ∂(volume.restrict (Icc (0 : ℝ) T)), E τ = 0 := by
    filter_upwards [hae] with τ hτ
    show (1 : ℝ) • D₁ τ + (-1 : ℝ) • D₂ τ = 0
    rw [hτ]
    ext u v
    simp
  have hEtd : IsTraceDensityL1 T E := by
    obtain ⟨s1, b1, m1, i1⟩ := h₁
    obtain ⟨s2, b2, m2, i2⟩ := h₂
    refine ⟨fun r x y => ?_, fun r hr => ?_, fun x y => ?_, ?_⟩
    · rw [hEr, hEr, s1, s2]
    · obtain ⟨c1, hc1⟩ := b1 r hr
      obtain ⟨c2, hc2⟩ := b2 r hr
      refine ⟨c1 + c2, ?_⟩
      rintro _ ⟨p, rfl⟩
      have e1 : ∑ i, |D₁ r (p.1.2.1 i) (p.1.2.2 i)| ≤ c1 := hc1 ⟨p, rfl⟩
      have e2 : ∑ i, |D₂ r (p.1.2.1 i) (p.1.2.2 i)| ≤ c2 := hc2 ⟨p, rfl⟩
      show ∑ i, |E r (p.1.2.1 i) (p.1.2.2 i)| ≤ c1 + c2
      calc ∑ i, |E r (p.1.2.1 i) (p.1.2.2 i)|
          ≤ ∑ i, (|D₁ r (p.1.2.1 i) (p.1.2.2 i)| + |D₂ r (p.1.2.1 i) (p.1.2.2 i)|) := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [hEr]; exact abs_sub _ _
        _ ≤ c1 + c2 := by rw [Finset.sum_add_distrib]; exact add_le_add e1 e2
    · have : (fun r => E r x y) = fun r => D₁ r x y - D₂ r x y := funext fun r => hEr r x y
      rw [this]; exact (m1 x y).sub (m2 x y)
    · have hm : Measurable fun r => traceNormForm (E r) := measurable_traceNormForm _ (fun x y => by
        have : (fun r => E r x y) = fun r => D₁ r x y - D₂ r x y := funext fun r => hEr r x y
        rw [this]; exact (m1 x y).sub (m2 x y))
      have h0 : (fun _ : ℝ => (0 : ℝ)) =ᵐ[volume.restrict (Icc (0 : ℝ) T)] fun r => traceNormForm (E r) := by
        filter_upwards [hEae] with τ hτ
        rw [hτ, traceNormForm_zero_eq]
      exact Integrable.congr (integrable_zero ℝ ℝ _) h0
  have hvar : (J E).variation (Icc 0 T) = 0 := by
    refine le_antisymm ?_ bot_le
    refine (hJ.tv E hEtd).trans ?_
    have : ∫⁻ r in Icc (0 : ℝ) T, ENNReal.ofReal (traceNormForm (E r)) = 0 := by
      rw [lintegral_congr_ae (g := fun _ => 0)]
      · simp
      · filter_upwards [hEae] with τ hτ
        rw [hτ, traceNormForm_zero_eq]; simp
    rw [this]; simp
  have hJE : J E I = 0 := by
    have h1 : ‖J E I‖ₑ ≤ (J E).variation (I ∩ Icc 0 T) := by
      rw [hJ.supp E hEtd I hI]
      exact VectorMeasure.enorm_measure_le_variation _ _
    have h2 : (J E).variation (I ∩ Icc 0 T) ≤ (J E).variation (Icc 0 T) :=
      measure_mono inter_subset_right
    rw [hvar] at h2
    have : ‖J E I‖ₑ = 0 := le_antisymm (h1.trans h2) bot_le
    simpa using this
  have hlin : J E I = (1 : ℝ) • J D₁ I + (-1 : ℝ) • J D₂ I := hJ.lin D₁ D₂ h₁ h₂ 1 (-1) I hI
  have : J E I = J D₁ I - J D₂ I := by
    rw [hlin]; simp [sub_eq_add_neg]
  rw [this] at hJE
  exact sub_eq_zero.1 hJE

end HRS.MS.CovMeas
