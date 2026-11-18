import HRS.MS.CovMeasAux22

/-!
# S10.1 (worker S101B), part 23: the push-forward `Jx` and its value on a product of two observations

`s101Jx hT J D I = s101Bri (tensorMap 𝒯 (J D I)) ∈ TensorDual (OscPath d m T) 2`.
`s101_Jx_four`: for `l₁, l₂` with `l_i(𝒯 y) = ⟨y(T),P_i⟩ + ⟨y(t_i),Q_i⟩`, `Jx D I (l₁⊗l₂)` is the sum of the four integrals
`∫_{I∩[0,T]} D(P_a,P_b) + ∫_{I∩[0,t_b]} D(P_a,Q_b) + ∫_{I∩[0,t_a]} D(Q_a,P_b) + ∫_{I∩[0,t_a∧t_b]} D(Q_a,Q_b)`.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.CovMeas

open HRS HRS.Whole HRS.MS.Go HRS.MS.FixEq HRS.Uniform HRS.Uniform.Q45 HRS.MS.GenPath HRS.MS.U9

variable {d : ℕ} {m T : ℝ}

/-- The push-forward of the covariance measure to `OscPath`, as an element of `TensorDual`. -/
def s101Jx (hT : 0 ≤ T)
    (J : (ℝ → KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ) → VectorMeasure ℝ (ProjTensor2 (PathSp T (KSpace d m T))))
    (D : ℝ → KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ) (I : Set ℝ) : TensorDual (OscPath d m T) 2 :=
  s101Bri (tensorMap (s56_reconCLM hT) (J D I))

lemma s101_Jx_apply (hT : 0 ≤ T)
    (J : (ℝ → KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ) → VectorMeasure ℝ (ProjTensor2 (PathSp T (KSpace d m T))))
    (D : ℝ → KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ) (I : Set ℝ)
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => OscPath d m T) ℝ) :
    s101Jx hT J D I M = tensorPairingL ((s101curry M).bilinearComp (s56_reconCLM hT) (s56_reconCLM hT)) (J D I) := by
  unfold s101Jx
  rw [s101Bri_apply, tensorPairing_tensorMap]

lemma s101_pullbackVec (v : KSpace d m T) (t r : ℝ) :
    pullbackVec (s56_idEvol (KSpace d m T)) t r (innerSL ℝ v) = v := by
  unfold pullbackVec
  have : (innerSL ℝ v).comp (((s56_idEvol (KSpace d m T)).VE t r).comp (s56_idEvol (KSpace d m T)).j) =
      innerSL ℝ v := rfl
  rw [this]
  exact (InnerProductSpace.toDual ℝ (KSpace d m T)).symm_apply_eq.2 rfl

lemma s101_obsForm_apply {t₁ t₂ : Icc (0 : ℝ) T} (v₁ v₂ : KSpace d m T) (y y' : PathSp T (KSpace d m T)) :
    obsForm t₁ t₂ (innerSL ℝ v₁) (innerSL ℝ v₂) y y' =
      inner ℝ v₁ (pcm y t₁) * inner ℝ v₂ (pcm y' t₂) := by
  unfold obsForm
  simp [ContinuousLinearMap.smulRight_apply, PathSp.eval, pcm]
  rfl

theorem s101_Jx_four (hT : 0 ≤ T) {C0 : ℝ}
    {J : (ℝ → KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ) → VectorMeasure ℝ (ProjTensor2 (PathSp T (KSpace d m T)))}
    (hJ : S101Jprops T C0 J) {D : ℝ → KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ}
    (hD : IsTraceDensityL1 T D) {I : Set ℝ} (hI : MeasurableSet I) {ta tb : ℝ}
    (hta : ta ∈ Icc (0 : ℝ) T) (htb : tb ∈ Icc (0 : ℝ) T) (Pa Qa Pb Qb : KSpace d m T)
    (l₁ l₂ : StrongDual ℝ (OscPath d m T))
    (h₁ : ∀ y : PathSp T (KSpace d m T), l₁ (s56_reconCLM hT y) =
      inner ℝ (pcm y ⟨T, hT, le_rfl⟩) Pa + inner ℝ (pcm y ⟨ta, hta⟩) Qa)
    (h₂ : ∀ y : PathSp T (KSpace d m T), l₂ (s56_reconCLM hT y) =
      inner ℝ (pcm y ⟨T, hT, le_rfl⟩) Pb + inner ℝ (pcm y ⟨tb, htb⟩) Qb) :
    s101Jx hT J D I ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap ![l₁, l₂]) =
      (∫ r in I ∩ Icc 0 T, D r Pa Pb) + (∫ r in I ∩ Icc 0 tb, D r Pa Qb) +
        (∫ r in I ∩ Icc 0 ta, D r Qa Pb) + ∫ r in I ∩ Icc 0 (min ta tb), D r Qa Qb := by
  set 𝒯 := s56_reconCLM hT with h𝒯
  set M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => OscPath d m T) ℝ :=
    (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap ![l₁, l₂] with hM
  set Tp : Icc (0 : ℝ) T := ⟨T, hT, le_rfl⟩ with hTp
  set ta' : Icc (0 : ℝ) T := ⟨ta, hta⟩
  set tb' : Icc (0 : ℝ) T := ⟨tb, htb⟩
  have hform : (s101curry M).bilinearComp 𝒯 𝒯 =
      obsForm Tp Tp (innerSL ℝ Pa) (innerSL ℝ Pb) + obsForm Tp tb' (innerSL ℝ Pa) (innerSL ℝ Qb) +
        obsForm ta' Tp (innerSL ℝ Qa) (innerSL ℝ Pb) + obsForm ta' tb' (innerSL ℝ Qa) (innerSL ℝ Qb) := by
    ext y y'
    simp only [ContinuousLinearMap.add_apply, s101_obsForm_apply, ContinuousLinearMap.bilinearComp_apply,
      s101curry_apply]
    have e1 : M ![𝒯 y, 𝒯 y'] = l₁ (𝒯 y) * l₂ (𝒯 y') := by
      simp [hM, Fin.prod_univ_two]
    rw [e1, h₁ y, h₂ y']
    simp only [real_inner_comm Pa, real_inner_comm Qa, real_inner_comm Pb, real_inner_comm Qb]
    ring
  rw [s101_Jx_apply, hform]
  rw [s101_tensorPairingL_add, s101_tensorPairingL_add, s101_tensorPairingL_add]
  have o : ∀ (t₁ t₂ : Icc (0 : ℝ) T) (v₁ v₂ : KSpace d m T),
      tensorPairingL (obsForm t₁ t₂ (innerSL ℝ v₁) (innerSL ℝ v₂)) (J D I) =
        ∫ r in I ∩ Icc 0 (min (t₁ : ℝ) t₂), D r v₁ v₂ := by
    intro t₁ t₂ v₁ v₂
    have := hJ.obs D hD t₁ t₂ (innerSL ℝ v₁) (innerSL ℝ v₂) I hI
    simp only [s101_pullbackVec] at this
    rw [← tensorPairing_eq]
    exact this
  rw [o Tp Tp, o Tp tb', o ta' Tp, o ta' tb']
  show (∫ r in I ∩ Icc 0 (min T T), D r Pa Pb) + (∫ r in I ∩ Icc 0 (min T tb), D r Pa Qb) +
    (∫ r in I ∩ Icc 0 (min ta T), D r Qa Pb) + (∫ r in I ∩ Icc 0 (min ta tb), D r Qa Qb) = _
  rw [min_self, min_eq_right htb.2, min_eq_left hta.2]

end HRS.MS.CovMeas
