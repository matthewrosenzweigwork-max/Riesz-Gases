import HRS.MS.Fp81S21BlockValue2

/-!
# S2.1(iii), packet 15d-4: block observation expansion

The first evaluation step is stated directly for the pushed unit-clock
covariance. It keeps the clipped clock arguments visible for the later
physical-time cancellation.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.Uniform HRS.Uniform.Q45 HRS.MS.CovMeas HRS.MS.GenPath

variable {d : ℕ} {m H : ℝ}

/-- Evaluation of the reconstruction on a finite combination of the
observation tests. The terminal `P` vector and the clipped-clock `Q` vector
are the actual coordinates of `fp81s21_blockRecon`. -/
theorem fp81s21_blockRecon_eval_combo (hH : 0 ≤ H) (a : ℝ) (k : ℕ)
    (y : PathSp 1 (KSpace d m H)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) H)
    (S : Finset (MultiIndex d)) (c : MultiIndex d → ℝ) :
    OscDual.eval (r2PathAt (fp81s21_blockRecon hH a k y) t)
        (fun x => ∑ α ∈ S, c α * oscTestFun m α x) =
      inner ℝ (pcm y fp81s21_unitClockEndpoint) (s101Pc m H t S c) +
        inner ℝ (pcm y (fp81s21_blockClock a k ⟨t, ht⟩)) (s101Qc m H S c) := by
  rw [s101_eval_combo]
  simp_rw [fp81s21_blockRecon_coord hH a k y ht]
  unfold s101Pc s101Qc
  rw [inner_sum, inner_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [inner_smul_right, inner_smul_right]
  ring

/-- Four-term observation expansion for the block pushforward. The four
integrals are over the unit clock clipped by their respective observation
times; no physical-time cutoff has yet been identified. -/
theorem fp81s21_blockPsi_four
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    [CompleteSpace K] [MeasurableSpace K] [BorelSpace K]
    [SecondCountableTopology K]
    {C0 : ℝ}
    {Q : (ℝ → K →L[ℝ] K →L[ℝ] ℝ) →
      VectorMeasure ℝ (ProjTensor2 (PathSp 1 K))}
    (hQ : fp81s21_UnitCovProps K C0 Q)
    {D : ℝ → K →L[ℝ] K →L[ℝ] ℝ}
    (hD : IsTraceDensityL1 1 D) {I : Set ℝ} (hI : MeasurableSet I)
    (Rc : PathSp 1 K →L[ℝ] OscPath d m H)

    {ta tb : Icc (0 : ℝ) 1} (Pa Qa Pb Qb : K)
    (l₁ l₂ : StrongDual ℝ (OscPath d m H))
    (h₁ : ∀ y, l₁ (Rc y) = inner ℝ (pcm y fp81s21_unitClockEndpoint) Pa +
      inner ℝ (pcm y ta) Qa)
    (h₂ : ∀ y, l₂ (Rc y) = inner ℝ (pcm y fp81s21_unitClockEndpoint) Pb +
      inner ℝ (pcm y tb) Qb) :
    fp81s21_blockPsi Rc (Q D I)
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap ![l₁, l₂]) =
      (∫ s in I ∩ Icc (0 : ℝ) 1, D s Pa Pb) +
        (∫ s in I ∩ Icc (0 : ℝ) (tb : ℝ), D s Pa Qb) +
        (∫ s in I ∩ Icc (0 : ℝ) (ta : ℝ), D s Qa Pb) +
          ∫ s in I ∩ Icc (0 : ℝ) (min (ta : ℝ) (tb : ℝ)), D s Qa Qb := by
  set M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => OscPath d m H) ℝ :=
    (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap ![l₁, l₂]
  have obs_apply : ∀ (t₁ t₂ : Icc (0 : ℝ) 1) (v₁ v₂ : K)
      (y y' : PathSp 1 K),
      obsForm t₁ t₂ (innerSL ℝ v₁) (innerSL ℝ v₂) y y' =
        inner ℝ v₁ (pcm y t₁) * inner ℝ v₂ (pcm y' t₂) := by
    intro t₁ t₂ v₁ v₂ y y'
    unfold obsForm
    simp [ContinuousLinearMap.smulRight_apply, PathSp.eval, pcm]
    rfl
  have hform : (s101curry M).bilinearComp Rc Rc =
      obsForm fp81s21_unitClockEndpoint fp81s21_unitClockEndpoint
          (innerSL ℝ Pa) (innerSL ℝ Pb) +
        obsForm fp81s21_unitClockEndpoint tb (innerSL ℝ Pa) (innerSL ℝ Qb) +
        obsForm ta fp81s21_unitClockEndpoint (innerSL ℝ Qa) (innerSL ℝ Pb) +
        obsForm ta tb (innerSL ℝ Qa) (innerSL ℝ Qb) := by
    ext y y'
    simp only [ContinuousLinearMap.add_apply,
      ContinuousLinearMap.bilinearComp_apply, s101curry_apply]
    rw [obs_apply, obs_apply, obs_apply, obs_apply]
    have e1 : M ![Rc y, Rc y'] = l₁ (Rc y) * l₂ (Rc y') := by
      simp [M, Fin.prod_univ_two]
    rw [e1, h₁ y, h₂ y']
    simp only [real_inner_comm Pa, real_inner_comm Qa,
      real_inner_comm Pb, real_inner_comm Qb]
    ring
  unfold fp81s21_blockPsi
  rw [s101Bri_apply, tensorPairing_tensorMap, hform,
    s101_tensorPairingL_add, s101_tensorPairingL_add,
    s101_tensorPairingL_add]
  have o : ∀ (t₁ t₂ : Icc (0 : ℝ) 1) (v₁ v₂ : K),
      tensorPairingL (obsForm t₁ t₂ (innerSL ℝ v₁) (innerSL ℝ v₂)) (Q D I) =
        ∫ s in I ∩ Icc (0 : ℝ) (min (t₁ : ℝ) (t₂ : ℝ)), D s v₁ v₂ := by
    intro t₁ t₂ v₁ v₂
    have ho := hQ.obs D hD t₁ t₂ (innerSL ℝ v₁) (innerSL ℝ v₂) I hI
    have hpull (t r : ℝ) (v : K) :
        pullbackVec (s56_idEvol K) t r (innerSL ℝ v) = v := by
      unfold pullbackVec
      have hcomp : (innerSL ℝ v).comp
          (((s56_idEvol K).VE t r).comp (s56_idEvol K).j) = innerSL ℝ v := rfl
      rw [hcomp]
      exact (InnerProductSpace.toDual ℝ K).symm_apply_eq.2 rfl
    simp only [hpull] at ho
    rw [← tensorPairing_eq]
    exact ho
  rw [o fp81s21_unitClockEndpoint fp81s21_unitClockEndpoint Pa Pb,
    o fp81s21_unitClockEndpoint tb Pa Qb,
    o ta fp81s21_unitClockEndpoint Qa Pb,
    o ta tb Qa Qb]
  simp [fp81s21_unitClockEndpoint, min_eq_right tb.property.2,
    min_eq_left ta.property.2]

#print axioms fp81s21_blockRecon_eval_combo
#print axioms fp81s21_blockPsi_four

end HRS.Fp81.S21

end
