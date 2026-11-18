import HRS.MS.GenPathAux10
import HRS.MS.Fp81S21UnitCov

/-!
# S2.1(iii), packet 15d-3: reconstruction adapter and congruence

Exact Lean types introduced here:

```lean
variable {d : ℕ} {m H : ℝ}

fp81s21_blockPsi {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
  (Rc : PathSp 1 K →L[ℝ] OscPath d m H)
  (τ : ProjTensor2 (PathSp 1 K)) : TensorDual (OscPath d m H) 2

fp81s21_blockPsi_add {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
  (Rc : PathSp 1 K →L[ℝ] OscPath d m H) (τ τ' : ProjTensor2 (PathSp 1 K)) :
  fp81s21_blockPsi Rc (τ + τ') = fp81s21_blockPsi Rc τ + fp81s21_blockPsi Rc τ'
fp81s21_blockPsi_smul {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
  (Rc : PathSp 1 K →L[ℝ] OscPath d m H) (a : ℝ) (τ : ProjTensor2 (PathSp 1 K)) :
  fp81s21_blockPsi Rc (a • τ) = a • fp81s21_blockPsi Rc τ
fp81s21_blockPsi_mem {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
  (Rc : PathSp 1 K →L[ℝ] OscPath d m H) (τ : ProjTensor2 (PathSp 1 K)) :
  fp81s21_blockPsi Rc τ ∈ projTensor (OscPath d m H) 2
fp81s21_blockPsi_norm_le {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
  (Rc : PathSp 1 K →L[ℝ] OscPath d m H) (Crec : ℝ) (hRc : ‖Rc‖ ≤ Crec)
  (τ : ProjTensor2 (PathSp 1 K)) :
  ‖fp81s21_blockPsi Rc τ‖ ≤ Crec ^ 2 * ‖τ‖

fp81s21_unitCov_congr {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
  [CompleteSpace K] [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
  {C0 : ℝ} {Q : (ℝ → K →L[ℝ] K →L[ℝ] ℝ) →
    VectorMeasure ℝ (ProjTensor2 (PathSp 1 K))}
  (hQ : fp81s21_UnitCovProps K C0 Q)
  {D₁ D₂ : ℝ → K →L[ℝ] K →L[ℝ] ℝ}
  (h₁ : IsTraceDensityL1 1 D₁) (h₂ : IsTraceDensityL1 1 D₂)
  (hae : ∀ᵐ τ ∂volume.restrict (Icc 0 1), D₁ τ = D₂ τ)
  {I : Set ℝ} (hI : MeasurableSet I) : Q D₁ I = Q D₂ I
```

`Rc` is an arbitrary bounded linear reconstruction. The concrete clock
reconstruction is intentionally supplied by the parallel packet.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.Uniform HRS.Uniform.Q45 HRS.MS.CovMeas HRS.MS.GenPath

variable {d : ℕ} {m H : ℝ}

/-- Push a unit-clock covariance tensor through an arbitrary bounded linear
reconstruction and then bridge to the projective tensor dual. -/
def fp81s21_blockPsi {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (Rc : PathSp 1 K →L[ℝ] OscPath d m H)
    (τ : ProjTensor2 (PathSp 1 K)) : TensorDual (OscPath d m H) 2 :=
  s101Bri (tensorMap Rc τ)

theorem fp81s21_blockPsi_add {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (Rc : PathSp 1 K →L[ℝ] OscPath d m H)
    (τ τ' : ProjTensor2 (PathSp 1 K)) :
    fp81s21_blockPsi Rc (τ + τ') = fp81s21_blockPsi Rc τ + fp81s21_blockPsi Rc τ' := by
  unfold fp81s21_blockPsi
  rw [map_add, s101Bri_add]

theorem fp81s21_blockPsi_smul {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (Rc : PathSp 1 K →L[ℝ] OscPath d m H) (a : ℝ)
    (τ : ProjTensor2 (PathSp 1 K)) :
    fp81s21_blockPsi Rc (a • τ) = a • fp81s21_blockPsi Rc τ := by
  unfold fp81s21_blockPsi
  rw [map_smul, s101Bri_smul]

theorem fp81s21_blockPsi_mem {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (Rc : PathSp 1 K →L[ℝ] OscPath d m H)
    (τ : ProjTensor2 (PathSp 1 K)) :
    fp81s21_blockPsi Rc τ ∈ projTensor (OscPath d m H) 2 := by
  exact s101Bri_mem _

theorem fp81s21_blockPsi_norm_le {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (Rc : PathSp 1 K →L[ℝ] OscPath d m H) (Crec : ℝ)
    (hRc : ‖Rc‖ ≤ Crec) (τ : ProjTensor2 (PathSp 1 K)) :
    ‖fp81s21_blockPsi Rc τ‖ ≤ Crec ^ 2 * ‖τ‖ := by
  unfold fp81s21_blockPsi
  calc
    ‖s101Bri (tensorMap Rc τ)‖ ≤ ‖tensorMap Rc τ‖ := norm_s101Bri_le _
    _ ≤ ‖Rc‖ ^ 2 * ‖τ‖ := norm_tensorMap_le _ _
    _ ≤ Crec ^ 2 * ‖τ‖ := by
      have hsq : ‖Rc‖ ^ 2 ≤ Crec ^ 2 := by nlinarith [norm_nonneg Rc, hRc]
      exact mul_le_mul_of_nonneg_right hsq (norm_nonneg τ)

private theorem fp81s21_traceNormForm_zero_eq {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℝ K] [CompleteSpace K] [MeasurableSpace K]
    [BorelSpace K] [SecondCountableTopology K] :
    traceNormForm (0 : K →L[ℝ] K →L[ℝ] ℝ) = 0 := by
  refine le_antisymm ?_ (traceNormForm_nonneg _)
  unfold traceNormForm
  exact Real.iSup_le (fun p => by simp) le_rfl

/-- Equality almost everywhere of two unit-clock trace densities forces their
associated vector measures to agree on every measurable set. -/
theorem fp81s21_unitCov_congr {K : Type} [NormedAddCommGroup K]
    [InnerProductSpace ℝ K] [CompleteSpace K] [MeasurableSpace K]
    [BorelSpace K] [SecondCountableTopology K] {C0 : ℝ}
    {Q : (ℝ → K →L[ℝ] K →L[ℝ] ℝ) →
      VectorMeasure ℝ (ProjTensor2 (PathSp 1 K))}
    (hQ : fp81s21_UnitCovProps K C0 Q)
    {D₁ D₂ : ℝ → K →L[ℝ] K →L[ℝ] ℝ}
    (h₁ : IsTraceDensityL1 1 D₁) (h₂ : IsTraceDensityL1 1 D₂)
    (hae : ∀ᵐ τ ∂(volume.restrict (Icc (0 : ℝ) 1)), D₁ τ = D₂ τ)
    {I : Set ℝ} (hI : MeasurableSet I) : Q D₁ I = Q D₂ I := by
  let E : ℝ → K →L[ℝ] K →L[ℝ] ℝ := fun r => (1 : ℝ) • D₁ r + (-1 : ℝ) • D₂ r
  have hEr : ∀ r x y, E r x y = D₁ r x y - D₂ r x y := by
    intro r x y
    simp [E, sub_eq_add_neg]
  have hEae : ∀ᵐ τ ∂(volume.restrict (Icc (0 : ℝ) 1)), E τ = 0 := by
    filter_upwards [hae] with τ hτ
    ext u v
    simp [E, hτ]
  have hEtd : IsTraceDensityL1 1 E := by
    obtain ⟨s1, b1, m1, i1⟩ := h₁
    obtain ⟨s2, b2, m2, i2⟩ := h₂
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro r x y
      rw [hEr, hEr, s1, s2]
    · intro r hr
      obtain ⟨c1, hc1⟩ := b1 r hr
      obtain ⟨c2, hc2⟩ := b2 r hr
      refine ⟨c1 + c2, ?_⟩
      rintro _ ⟨p, rfl⟩
      have e1 : ∑ i, |D₁ r (p.1.2.1 i) (p.1.2.2 i)| ≤ c1 := hc1 ⟨p, rfl⟩
      have e2 : ∑ i, |D₂ r (p.1.2.1 i) (p.1.2.2 i)| ≤ c2 := hc2 ⟨p, rfl⟩
      calc
        ∑ i, |E r (p.1.2.1 i) (p.1.2.2 i)|
            ≤ ∑ i, (|D₁ r (p.1.2.1 i) (p.1.2.2 i)| +
              |D₂ r (p.1.2.1 i) (p.1.2.2 i)|) := by
                refine Finset.sum_le_sum fun i _ => ?_
                rw [hEr]
                exact abs_sub _ _
        _ ≤ c1 + c2 := by
          rw [Finset.sum_add_distrib]
          exact add_le_add e1 e2
    · intro x y
      have he : (fun r => E r x y) = fun r => D₁ r x y - D₂ r x y :=
        funext fun r => hEr r x y
      rw [he]
      exact (m1 x y).sub (m2 x y)
    · have hm : Measurable fun r => traceNormForm (E r) :=
        measurable_traceNormForm _ (fun x y => by
          have he : (fun r => E r x y) = fun r => D₁ r x y - D₂ r x y :=
            funext fun r => hEr r x y
          rw [he]
          exact (m1 x y).sub (m2 x y))
      have h0 : (fun _ : ℝ => (0 : ℝ)) =ᵐ[volume.restrict (Icc (0 : ℝ) 1)]
          fun r => traceNormForm (E r) := by
        filter_upwards [hEae] with τ hτ
        rw [hτ, fp81s21_traceNormForm_zero_eq]
      exact Integrable.congr (integrable_zero ℝ ℝ _) h0
  have hvar : (Q E).variation (Icc 0 1) = 0 := by
    refine le_antisymm ?_ bot_le
    calc
      (Q E).variation (Icc 0 1) ≤
          ENNReal.ofReal C0 * ∫⁻ r in Icc (0 : ℝ) 1,
            ENNReal.ofReal (traceNormForm (E r)) := hQ.tv E hEtd
      _ = 0 := by
        have hInt : ∫⁻ r in Icc (0 : ℝ) 1,
            ENNReal.ofReal (traceNormForm (E r)) = 0 := by
          rw [lintegral_congr_ae (g := fun _ => 0)]
          · simp
          · filter_upwards [hEae] with τ hτ
            rw [hτ, fp81s21_traceNormForm_zero_eq]
            simp
        rw [hInt]
        simp
  have hQE : Q E I = 0 := by
    have h1 : ‖Q E I‖ₑ ≤ (Q E).variation (I ∩ Icc 0 1) := by
      rw [hQ.supp E hEtd I hI]
      exact VectorMeasure.enorm_measure_le_variation _ _
    have h2 : (Q E).variation (I ∩ Icc 0 1) ≤ (Q E).variation (Icc 0 1) :=
      measure_mono inter_subset_right
    rw [hvar] at h2
    have hz : ‖Q E I‖ₑ = 0 := le_antisymm (h1.trans h2) bot_le
    simpa using hz
  have hlin : Q E I = (1 : ℝ) • Q D₁ I + (-1 : ℝ) • Q D₂ I := by
    simpa [E] using hQ.lin D₁ D₂ h₁ h₂ 1 (-1) I hI
  have hsub : Q E I = Q D₁ I - Q D₂ I := by
    rw [hlin]
    simp [sub_eq_add_neg]
  rw [hsub] at hQE
  exact sub_eq_zero.mp hQE

#print axioms fp81s21_blockPsi_add
#print axioms fp81s21_blockPsi_smul
#print axioms fp81s21_blockPsi_mem
#print axioms fp81s21_blockPsi_norm_le
#print axioms fp81s21_unitCov_congr

end HRS.Fp81.S21

end
