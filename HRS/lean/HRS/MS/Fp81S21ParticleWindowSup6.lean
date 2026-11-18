import HRS.MS.Fp81S21ParticleWindowSup5

/-! A.e.-continuous paths are reduced to the everywhere-continuous bridge by
modification on a measurable null superset. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole

/-- The mode-to-path moment estimate remains valid when the path is continuous
only almost surely, as is the physical centered particle path. -/
theorem fp81s21_oscDual_path_sup_moment6_of_mode_moments_ae_cont
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (hd : 0 < d) (m a b K : ℝ) (hab : a ≤ b)
    (L : ℝ → Ω → OscDual d m) (w : MultiIndex d → ℝ)
    (hK : 0 ≤ K) (hw : ∀ α, 0 ≤ w α)
    (hwsq : Summable fun α : MultiIndex d => w α ^ 2)
    (hLmeas : ∀ t ∈ Icc a b, AEMeasurable (L t) P)
    (hLcont : ∀ᵐ ω ∂P, ContinuousOn (fun t => L t ω) (Icc a b))
    (hMom : ∀ α : MultiIndex d,
      fp81s21_Moment6 P (fun ω => ⨆ t : Icc a b,
        |OscDual.coord (L t ω) α|) ((K * w α) ^ 6)) :
    fp81s21_Moment6 P (fun ω => ⨆ t : Icc a b, ‖L t ω‖)
      ((K * Real.sqrt (∑' α : MultiIndex d, w α ^ 2)) ^ 6) := by
  classical
  let BadSet : Set Ω := {ω | ¬ ContinuousOn (fun t => L t ω) (Icc a b)}
  have hBadNull : P BadSet = 0 := by
    exact (ae_iff.mp hLcont)
  obtain ⟨Bad, hBadSub, hBadMeas, hBadNull'⟩ :=
    exists_measurable_superset_of_null hBadNull
  have hNotBad : ∀ᵐ ω ∂P, ω ∉ Bad := by
    rw [ae_iff]
    simpa using hBadNull'
  have hGood (ω : Ω) (hω : ω ∉ Bad) :
      ContinuousOn (fun t => L t ω) (Icc a b) := by
    by_contra hn
    exact hω (hBadSub hn)
  let L' : ℝ → Ω → OscDual d m := fun t ω => if ω ∈ Bad then 0 else L t ω
  have hL'eq (t : ℝ) : (fun ω => L' t ω) =ᵐ[P] L t := by
    filter_upwards [hNotBad] with ω hω
    simp [L', hω]
  have hL'meas : ∀ t ∈ Icc a b, AEMeasurable (L' t) P := by
    intro t ht
    exact (hLmeas t ht).congr (hL'eq t).symm
  have hL'cont : ∀ ω, ContinuousOn (fun t => L' t ω) (Icc a b) := by
    intro ω
    by_cases hω : ω ∈ Bad
    · simp [L', hω]
      exact continuousOn_const
    · simpa [L', hω] using hGood ω hω
  have hcoord : ∀ᵐ ω ∂P, ∀ α : MultiIndex d, ∀ t ∈ Icc a b,
      OscDual.coord (L' t ω) α = OscDual.coord (L t ω) α := by
    filter_upwards [hNotBad] with ω hω α t ht
    simp [L', hω]
  have hMom' : ∀ α : MultiIndex d,
      fp81s21_Moment6 P (fun ω => ⨆ t : Icc a b,
        |OscDual.coord (L' t ω) α|) ((K * w α) ^ 6) := by
    intro α
    let S : Ω → ℝ := fun ω => ⨆ t : Icc a b, |OscDual.coord (L t ω) α|
    let S' : Ω → ℝ := fun ω => ⨆ t : Icc a b, |OscDual.coord (L' t ω) α|
    have hSeq : S =ᵐ[P] S' := by
      filter_upwards [hcoord] with ω hω
      apply iSup_congr
      intro t
      exact congrArg abs (hω α t t.property).symm
    have hpow : (fun ω => ‖S ω‖ ^ (6 : ℕ)) =ᵐ[P]
        (fun ω => ‖S' ω‖ ^ (6 : ℕ)) := by
      filter_upwards [hSeq] with ω hω
      rw [hω]
    rcases hMom α with ⟨hm, hi, hbnd⟩
    refine ⟨?_, hi.congr hpow, ?_⟩
    · simpa [S, S'] using hm.congr hSeq
    · calc
        (∫ ω, ‖S' ω‖ ^ 6 ∂P) = ∫ ω, ‖S ω‖ ^ 6 ∂P := integral_congr_ae hpow.symm
        _ ≤ (K * w α) ^ 6 := hbnd
  have hMod := fp81s21_oscDual_path_sup_moment6_of_mode_moments
    P hd m a b K hab L' w hK hw hwsq hL'meas hL'cont hMom'
  let U : Ω → ℝ := fun ω => ⨆ t : Icc a b, ‖L t ω‖
  let U' : Ω → ℝ := fun ω => ⨆ t : Icc a b, ‖L' t ω‖
  have hUeq : U =ᵐ[P] U' := by
    filter_upwards [hNotBad] with ω hω
    apply iSup_congr
    intro t
    congr 1
    simp [L', hω]
  have hUpow : (fun ω => ‖U' ω‖ ^ (6 : ℕ)) =ᵐ[P]
      (fun ω => ‖U ω‖ ^ (6 : ℕ)) := by
    filter_upwards [hUeq] with ω hω
    rw [hω.symm]
  refine ⟨?_, hMod.2.1.congr hUpow, ?_⟩
  · simpa [U, U'] using hMod.1.congr hUeq.symm
  · calc
      (∫ ω, ‖U ω‖ ^ 6 ∂P) = ∫ ω, ‖U' ω‖ ^ 6 ∂P := integral_congr_ae hUpow.symm
      _ ≤ (K * Real.sqrt (∑' α : MultiIndex d, w α ^ 2)) ^ 6 := hMod.2.2

#print axioms HRS.Fp81.S21.fp81s21_oscDual_path_sup_moment6_of_mode_moments_ae_cont
end HRS.Fp81.S21
end
