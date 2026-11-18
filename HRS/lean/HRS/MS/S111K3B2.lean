import HRS.MS.S111K3B

/-!
# S11.1 continuation (S11K3), B03 part B2: localization, per-interval bound and interval functions of the push-forward

`k3_J_localize`: `J(1_I D)(I') = J(D)(I ∩ I')` (the observation formula determines the path tensor, `obs_unique`).
`k3_J_interval_bound`: `‖J(D)(I)‖ ≤ C0 ∫_{I∩[0,2T]} ‖D_r‖₁`.  `k3_Jx_four`: the value of the push-forward on two observations of
the shifted reconstruction.  Interval additivity and continuity of the cumulative push-forward.
-/

set_option autoImplicit false
noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4000

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S111K3

open HRS HRS.Whole HRS.Uniform HRS.Uniform.Q45 HRS.MS.GenPath HRS.MS.U9 HRS.MS.CovMeas HRS.MS.S52
open Classical

variable {d : ℕ} {m T : ℝ}

open Classical in
/-- The restriction `1_I D` of a trace density. -/
def k3Ind (I : Set ℝ) (D : ℝ → K3Bil d m T) : ℝ → K3Bil d m T := fun r => if r ∈ I then D r else 0

lemma k3Ind_apply (I : Set ℝ) (D : ℝ → K3Bil d m T) (r : ℝ) (x y : KSpace d m T) :
    k3Ind I D r x y = if r ∈ I then D r x y else 0 := by
  classical
  unfold k3Ind
  split_ifs <;> simp

lemma k3_ind_td {D : ℝ → K3Bil d m T} (hD : IsTraceDensityL1 (2 * T) D) {I : Set ℝ} (hI : MeasurableSet I) :
    IsTraceDensityL1 (2 * T) (k3Ind I D) := by
  classical
  obtain ⟨s, b, mm, i⟩ := hD
  have hmeas : ∀ x y : KSpace d m T, Measurable fun r => k3Ind I D r x y := by
    intro x y
    have : (fun r => k3Ind I D r x y) = fun r => if r ∈ I then D r x y else 0 :=
      funext fun r => k3Ind_apply I D r x y
    rw [this]
    exact Measurable.ite hI (mm x y) measurable_const
  refine ⟨fun r x y => ?_, fun r hr => ?_, hmeas, ?_⟩
  · rw [k3Ind_apply, k3Ind_apply]
    split_ifs
    · exact s r x y
    · rfl
  · by_cases h : r ∈ I
    · have e : k3Ind I D r = D r := by unfold k3Ind; rw [if_pos h]
      rw [e]; exact b r hr
    · have e : k3Ind I D r = 0 := by unfold k3Ind; rw [if_neg h]
      rw [e]
      refine ⟨0, ?_⟩
      rintro _ ⟨p, rfl⟩
      simp
  · have hm : Measurable fun r => traceNormForm (k3Ind I D r) := HRS.measurable_traceNormForm _ hmeas
    refine i.mono' hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (traceNormForm_nonneg _)]
    by_cases h : r ∈ I
    · have e : k3Ind I D r = D r := by unfold k3Ind; rw [if_pos h]
      rw [e]
    · have e : k3Ind I D r = 0 := by unfold k3Ind; rw [if_neg h]
      rw [e, traceNormForm_zero_eq]
      exact traceNormForm_nonneg _

lemma k3_set_int_ind (D : ℝ → K3Bil d m T) {I : Set ℝ} (hI : MeasurableSet I) (S : Set ℝ)
    (x y : ℝ → KSpace d m T) :
    ∫ r in S, k3Ind I D r (x r) (y r) = ∫ r in S ∩ I, D r (x r) (y r) := by
  have e : (fun r => k3Ind I D r (x r) (y r)) = I.indicator (fun r => D r (x r) (y r)) := by
    funext r
    rw [k3Ind_apply]
    by_cases h : r ∈ I <;> simp [h]
  rw [e, setIntegral_indicator hI]

theorem k3_J_localize {C0 : ℝ}
    {J : (ℝ → K3Bil d m T) → VectorMeasure ℝ (ProjTensor2 (PathSp (2 * T) (KSpace d m T)))}
    (hT : 0 < T) (hJ : K3Jprops T C0 J) {D : ℝ → K3Bil d m T} (hD : IsTraceDensityL1 (2 * T) D)
    {I I' : Set ℝ} (hI : MeasurableSet I) (hI' : MeasurableSet I') :
    J (k3Ind I D) I' = J D (I ∩ I') := by
  classical
  have hDI := k3_ind_td hD hI
  have hF : ObsFormula (s56_idEvol (KSpace d m T)) (2 * T) (k3Ind I D) I' (J (k3Ind I D) I') := by
    intro t₁ t₂ ℓ₁ ℓ₂
    exact hJ.obs _ hDI t₁ t₂ ℓ₁ ℓ₂ I' hI'
  have hF' : ObsFormula (s56_idEvol (KSpace d m T)) (2 * T) (k3Ind I D) I' (J D (I ∩ I')) := by
    intro t₁ t₂ ℓ₁ ℓ₂
    rw [hJ.obs D hD t₁ t₂ ℓ₁ ℓ₂ (I ∩ I') (hI.inter hI'),
      k3_set_int_ind D hI _ (fun r => pullbackVec (s56_idEvol (KSpace d m T)) (t₁ : ℝ) r ℓ₁)
        (fun r => pullbackVec (s56_idEvol (KSpace d m T)) (t₂ : ℝ) r ℓ₂)]
    have hs : (I ∩ I') ∩ Icc (0 : ℝ) (min (t₁ : ℝ) t₂) = (I' ∩ Icc (0 : ℝ) (min (t₁ : ℝ) t₂)) ∩ I := by
      ext r; simp only [mem_inter_iff]; tauto
    rw [hs]
  exact obs_unique (by linarith : (0 : ℝ) < 2 * T) hF hF'

theorem k3_J_interval_bound {C0 : ℝ}
    {J : (ℝ → K3Bil d m T) → VectorMeasure ℝ (ProjTensor2 (PathSp (2 * T) (KSpace d m T)))}
    (hT : 0 < T) (hJ : K3Jprops T C0 J) {D : ℝ → K3Bil d m T} (hD : IsTraceDensityL1 (2 * T) D)
    {I : Set ℝ} (hI : MeasurableSet I) :
    ‖J D I‖ₑ ≤ ENNReal.ofReal C0 * ∫⁻ r in I ∩ Icc 0 (2 * T), ENNReal.ofReal (traceNormForm (D r)) := by
  classical
  have hDI := k3_ind_td hD hI
  have h1 : J D I = J (k3Ind I D) (Icc 0 (2 * T)) := by
    rw [k3_J_localize hT hJ hD hI measurableSet_Icc, hJ.supp D hD I hI]
  rw [h1]
  refine (VectorMeasure.enorm_measure_le_variation _ _).trans ((hJ.tv _ hDI).trans ?_)
  refine mul_le_mul' le_rfl (le_of_eq ?_)
  have e : (fun r => ENNReal.ofReal (traceNormForm (k3Ind I D r))) =
      I.indicator (fun r => ENNReal.ofReal (traceNormForm (D r))) := by
    funext r
    by_cases h : r ∈ I
    · have e : k3Ind I D r = D r := by unfold k3Ind; rw [if_pos h]
      rw [e, Set.indicator_of_mem h]
    · have e : k3Ind I D r = 0 := by unfold k3Ind; rw [if_neg h]
      rw [e, traceNormForm_zero_eq, Set.indicator_of_notMem h]; simp
  rw [e, lintegral_indicator hI, Measure.restrict_restrict hI]

/-! ### The push-forward on intervals -/

/-- `Jx D I`: the push-forward to `OscPath` of the path tensor `J D I`. -/
def k3Jx (hT : 0 ≤ T)
    (J : (ℝ → K3Bil d m T) → VectorMeasure ℝ (ProjTensor2 (PathSp (2 * T) (KSpace d m T))))
    (D : ℝ → K3Bil d m T) (I : Set ℝ) : TensorDual (OscPath d m T) 2 :=
  k3Psi hT (J D I)

section Interval

variable (hT : 0 ≤ T)
  (J : (ℝ → K3Bil d m T) → VectorMeasure ℝ (ProjTensor2 (PathSp (2 * T) (KSpace d m T))))
  (D : ℝ → K3Bil d m T)

include hT in
lemma k3Jx_empty : k3Jx hT J D ∅ = 0 := by
  unfold k3Jx
  rw [VectorMeasure.empty]
  exact k3Psi_zero hT

include hT in
lemma k3Jx_union {A B : Set ℝ} (h : Disjoint A B) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    k3Jx hT J D (A ∪ B) = k3Jx hT J D A + k3Jx hT J D B := by
  unfold k3Jx
  rw [VectorMeasure.of_union h hA hB]
  exact k3Psi_add hT _ _

include hT in
lemma k3Jx_Ioc_add {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    k3Jx hT J D (Ioc a c) = k3Jx hT J D (Ioc a b) + k3Jx hT J D (Ioc b c) := by
  rw [← Set.Ioc_union_Ioc_eq_Ioc hab hbc]
  refine k3Jx_union hT J D ?_ measurableSet_Ioc measurableSet_Ioc
  rw [Set.disjoint_left]
  intro x hx hx'
  exact absurd hx.2 (not_le.2 hx'.1)

include hT in
lemma k3Jx_Ioc_self (a : ℝ) : k3Jx hT J D (Ioc a a) = 0 := by
  rw [Set.Ioc_self]; exact k3Jx_empty hT J D

include hT in
lemma k3Jx_Icc_split {u : ℝ} (hu : 0 ≤ u) :
    k3Jx hT J D (Icc 0 u) = k3Jx hT J D {0} + k3Jx hT J D (Ioc 0 u) := by
  have : Icc (0 : ℝ) u = {0} ∪ Ioc 0 u := by
    ext x
    simp only [mem_Icc, mem_union, mem_singleton_iff, mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      rcases h1.eq_or_lt with h | h
      · exact Or.inl h.symm
      · exact Or.inr ⟨h, h2⟩
    · rintro (h | h)
      · exact ⟨h.symm.le, h ▸ hu⟩
      · exact ⟨h.1.le, h.2⟩
  rw [this]
  refine k3Jx_union hT J D ?_ (measurableSet_singleton 0) measurableSet_Ioc
  rw [Set.disjoint_left]
  intro x hx hx'
  rw [mem_singleton_iff] at hx
  exact absurd hx (ne_of_gt hx'.1)

end Interval

theorem k3_Jx_Ioc0_cont (hT : 0 ≤ T) {C0 : ℝ}
    {J : (ℝ → K3Bil d m T) → VectorMeasure ℝ (ProjTensor2 (PathSp (2 * T) (KSpace d m T)))}
    (hJ : K3Jprops T C0 J) {D : ℝ → K3Bil d m T} (hD : IsTraceDensityL1 (2 * T) D) :
    ContinuousOn (fun u => k3Jx hT J D (Ioc 0 u)) (Icc 0 (2 * T)) := by
  have h1 : ContinuousOn (fun u => k3Psi hT (J D (Icc 0 u))) (Icc 0 (2 * T)) :=
    (lipschitz_k3Psi hT).continuous.comp_continuousOn (hJ.cont D hD)
  have h2 : ContinuousOn (fun u => k3Psi hT (J D (Icc 0 u)) - k3Jx hT J D {0}) (Icc 0 (2 * T)) :=
    h1.sub continuousOn_const
  refine h2.congr fun u hu => ?_
  have := k3Jx_Icc_split hT J D hu.1
  show k3Jx hT J D (Ioc 0 u) = k3Psi hT (J D (Icc 0 u)) - k3Jx hT J D {0}
  have e : k3Psi hT (J D (Icc 0 u)) = k3Jx hT J D (Icc 0 u) := rfl
  rw [e, this]; abel

/-- Per-interval bound for the push-forward. -/
theorem k3_Jx_interval_bound (hT : 0 < T) {C0 : ℝ}
    {J : (ℝ → K3Bil d m T) → VectorMeasure ℝ (ProjTensor2 (PathSp (2 * T) (KSpace d m T)))}
    (hJ : K3Jprops T C0 J) {D : ℝ → K3Bil d m T} (hD : IsTraceDensityL1 (2 * T) D)
    {I : Set ℝ} (hI : MeasurableSet I) :
    ‖k3Jx hT.le J D I‖ₑ ≤ ENNReal.ofReal ((3 + Real.sqrt T) ^ 2 * C0) *
      ∫⁻ r in I ∩ Icc 0 (2 * T), ENNReal.ofReal (traceNormForm (D r)) := by
  have h1 := norm_k3Psi_le hT.le (J D I)
  have hn : ‖(k3reconCLM hT.le : PathSp (2 * T) (KSpace d m T) →L[ℝ] OscPath d m T)‖ ^ 2 ≤
      (3 + Real.sqrt T) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (k3reconCLM_norm_le hT.le) 2
  have h2 : ‖k3Jx hT.le J D I‖ₑ ≤ ENNReal.ofReal ((3 + Real.sqrt T) ^ 2) * ‖J D I‖ₑ := by
    have h3 : ‖k3Jx hT.le J D I‖ ≤ (3 + Real.sqrt T) ^ 2 * ‖J D I‖ :=
      h1.trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
    have h4 : ‖k3Jx hT.le J D I‖ₑ ≤ ENNReal.ofReal ((3 + Real.sqrt T) ^ 2 * ‖J D I‖) := by
      rw [← ofReal_norm_eq_enorm]; exact ENNReal.ofReal_le_ofReal h3
    rwa [ENNReal.ofReal_mul (by positivity), ofReal_norm_eq_enorm] at h4
  refine h2.trans ?_
  have h5 := k3_J_interval_bound hT hJ hD hI
  calc ENNReal.ofReal ((3 + Real.sqrt T) ^ 2) * ‖J D I‖ₑ
      ≤ ENNReal.ofReal ((3 + Real.sqrt T) ^ 2) * (ENNReal.ofReal C0 *
          ∫⁻ r in I ∩ Icc 0 (2 * T), ENNReal.ofReal (traceNormForm (D r))) := mul_le_mul' le_rfl h5
    _ = ENNReal.ofReal ((3 + Real.sqrt T) ^ 2 * C0) * ∫⁻ r in I ∩ Icc 0 (2 * T),
          ENNReal.ofReal (traceNormForm (D r)) := by
        rw [← mul_assoc, ENNReal.ofReal_mul (by positivity)]

/-! ### The value on two observations -/

lemma k3_obsForm_apply {t₁ t₂ : Icc (0 : ℝ) (2 * T)} (v₁ v₂ : KSpace d m T)
    (y y' : PathSp (2 * T) (KSpace d m T)) :
    obsForm t₁ t₂ (innerSL ℝ v₁) (innerSL ℝ v₂) y y' =
      inner ℝ v₁ (pcm y t₁) * inner ℝ v₂ (pcm y' t₂) := by
  unfold obsForm
  simp [ContinuousLinearMap.smulRight_apply, PathSp.eval, pcm]
  rfl

theorem k3_Jx_four (hT : 0 < T) {C0 : ℝ}
    {J : (ℝ → K3Bil d m T) → VectorMeasure ℝ (ProjTensor2 (PathSp (2 * T) (KSpace d m T)))}
    (hJ : K3Jprops T C0 J) {D : ℝ → K3Bil d m T} (hD : IsTraceDensityL1 (2 * T) D) {I : Set ℝ}
    (hI : MeasurableSet I) {ta tb : Icc (0 : ℝ) T} (Pa Qa Pb Qb : KSpace d m T)
    (l₁ l₂ : StrongDual ℝ (OscPath d m T))
    (h₁ : ∀ y : PathSp (2 * T) (KSpace d m T), l₁ (k3reconCLM hT.le y) =
      inner ℝ (pcm y (k3pt hT.le)) Pa + inner ℝ (pcm y (k3sh hT.le ta)) Qa)
    (h₂ : ∀ y : PathSp (2 * T) (KSpace d m T), l₂ (k3reconCLM hT.le y) =
      inner ℝ (pcm y (k3pt hT.le)) Pb + inner ℝ (pcm y (k3sh hT.le tb)) Qb) :
    k3Jx hT.le J D I ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap ![l₁, l₂]) =
      (∫ r in I ∩ Icc 0 (2 * T), D r Pa Pb) + (∫ r in I ∩ Icc 0 (T + tb), D r Pa Qb) +
        (∫ r in I ∩ Icc 0 (T + ta), D r Qa Pb) + ∫ r in I ∩ Icc 0 (min (T + ta) (T + tb)), D r Qa Qb := by
  set 𝒯 := k3reconCLM hT.le with h𝒯
  set M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => OscPath d m T) ℝ :=
    (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap ![l₁, l₂] with hM
  set Tp : Icc (0 : ℝ) (2 * T) := k3pt hT.le with hTp
  set ta' : Icc (0 : ℝ) (2 * T) := k3sh hT.le ta with hta'
  set tb' : Icc (0 : ℝ) (2 * T) := k3sh hT.le tb with htb'
  have hform : (s101curry M).bilinearComp 𝒯 𝒯 =
      obsForm Tp Tp (innerSL ℝ Pa) (innerSL ℝ Pb) + obsForm Tp tb' (innerSL ℝ Pa) (innerSL ℝ Qb) +
        obsForm ta' Tp (innerSL ℝ Qa) (innerSL ℝ Pb) + obsForm ta' tb' (innerSL ℝ Qa) (innerSL ℝ Qb) := by
    ext y y'
    simp only [ContinuousLinearMap.add_apply, k3_obsForm_apply, ContinuousLinearMap.bilinearComp_apply,
      s101curry_apply]
    have e1 : M ![𝒯 y, 𝒯 y'] = l₁ (𝒯 y) * l₂ (𝒯 y') := by
      simp [hM, Fin.prod_univ_two]
    rw [e1, h₁ y, h₂ y']
    simp only [real_inner_comm Pa, real_inner_comm Qa, real_inner_comm Pb, real_inner_comm Qb]
    ring
  have hJx : k3Jx hT.le J D I M = tensorPairingL ((s101curry M).bilinearComp 𝒯 𝒯) (J D I) := by
    unfold k3Jx k3Psi
    rw [s101Bri_apply, tensorPairing_tensorMap]
  rw [hJx, hform]
  rw [s101_tensorPairingL_add, s101_tensorPairingL_add, s101_tensorPairingL_add]
  have o : ∀ (t₁ t₂ : Icc (0 : ℝ) (2 * T)) (v₁ v₂ : KSpace d m T),
      tensorPairingL (obsForm t₁ t₂ (innerSL ℝ v₁) (innerSL ℝ v₂)) (J D I) =
        ∫ r in I ∩ Icc 0 (min (t₁ : ℝ) t₂), D r v₁ v₂ := by
    intro t₁ t₂ v₁ v₂
    have := hJ.obs D hD t₁ t₂ (innerSL ℝ v₁) (innerSL ℝ v₂) I hI
    simp only [s101_pullbackVec] at this
    rw [← tensorPairing_eq]
    exact this
  rw [o Tp Tp, o Tp tb', o ta' Tp, o ta' tb']
  have e2 : (min ((Tp : ℝ)) (Tp : ℝ)) = 2 * T := by simp [hTp, k3pt]
  have e3 : (min ((Tp : ℝ)) (tb' : ℝ)) = T + tb := by
    simp only [hTp, htb', k3pt, k3sh]
    exact min_eq_right (by linarith [tb.2.2])
  have e4 : (min ((ta' : ℝ)) (Tp : ℝ)) = T + ta := by
    simp only [hTp, hta', k3pt, k3sh]
    exact min_eq_left (by linarith [ta.2.2])
  have e5 : (min ((ta' : ℝ)) (tb' : ℝ)) = min (T + ta) (T + tb) := by
    simp only [hta', htb', k3sh]
  rw [e2, e3, e4, e5]

end HRS.MS.S111K3
