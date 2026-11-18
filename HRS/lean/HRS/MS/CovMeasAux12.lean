import HRS.MS.CovMeasAux11

/-!
# S10.1 (worker S101B), part 12: `τ ↦ D_τ(W_{s,α}, W_{s',β})` is a.e.-measurable on `[0,T]`
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.CovMeas

open HRS HRS.Whole HRS.MS.Go HRS.MS.FixEq

variable {d : ℕ}

/-- The standing hypotheses on `(C, m, T, r, P, z)`. -/
structure S101Adm (C : WholeCoeff d) (m T : ℝ) (r : ℕ) (Pw : ℝ) (z : ℝ → (Euc d → ℝ) → ℝ) : Prop where
  hd : 1 ≤ d
  hP : (d : ℝ) < 2 * Pw
  horb : R2OrbitSummable C m T r
  hz : S101Lin r Pw T z
  hmeas : R2JIntegrandMeas C m T z

variable {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {Pw : ℝ} {z : ℝ → (Euc d → ℝ) → ℝ}

lemma s101_Wf_lt {τ s : ℝ} (h : τ < s) (α : MultiIndex d) :
    s101Wf C m τ s α = propagatorW C τ s (oscTestFun m α) := by
  simp [s101Wf, h]

lemma s101_Wf_ge {τ s : ℝ} (h : s ≤ τ) (α : MultiIndex d) :
    s101Wf C m τ s α = s101Wf C m τ τ α := by
  simp [s101Wf, not_lt.2 h]

lemma s101_D_W_lt (A : S101Adm C m T r Pw z) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) {s s' : ℝ}
    (hs : s ∈ Icc (0 : ℝ) T) (hs' : s' ∈ Icc (0 : ℝ) T) (h1 : τ < s) (h2 : τ < s') (α β : MultiIndex d) :
    s101D C m T z τ (s101W m T s α) (s101W m T s' β) =
      2 * C.ν * z τ (fun x => inner ℝ (gradient (propagatorW C τ s (oscTestFun m α)) x)
        (gradient (propagatorW C τ s' (oscTestFun m β)) x)) := by
  rw [s101_D_W A.hd A.hP A.horb A.hz hτ hs hs', s101_Wf_lt h1, s101_Wf_lt h2]

lemma s101_D_W_left (A : S101Adm C m T r Pw z) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) {s s' : ℝ}
    (hs : s ∈ Icc (0 : ℝ) T) (hs' : s' ∈ Icc (0 : ℝ) T) (h : s ≤ τ) (α β : MultiIndex d) :
    s101D C m T z τ (s101W m T s α) (s101W m T s' β) =
      s101D C m T z τ (s101W m T τ α) (s101W m T s' β) := by
  rw [s101_D_W A.hd A.hP A.horb A.hz hτ hs hs', s101_D_W A.hd A.hP A.horb A.hz hτ hτ hs',
    s101_Wf_ge h]

lemma s101_D_W_right (A : S101Adm C m T r Pw z) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) {s s' : ℝ}
    (hs : s ∈ Icc (0 : ℝ) T) (hs' : s' ∈ Icc (0 : ℝ) T) (h : s' ≤ τ) (α β : MultiIndex d) :
    s101D C m T z τ (s101W m T s α) (s101W m T s' β) =
      s101D C m T z τ (s101W m T s α) (s101W m T τ β) := by
  rw [s101_D_W A.hd A.hP A.horb A.hz hτ hs hs', s101_D_W A.hd A.hP A.horb A.hz hτ hs hτ,
    s101_Wf_ge h]

/-- On `τ < s ∧ τ < s'` the pairing is a.e.-measurable (hypothesis `R2JIntegrandMeas`). -/
lemma s101_aem_lt (A : S101Adm C m T r Pw z) {s s' : ℝ} (hs : s ∈ Icc (0 : ℝ) T)
    (hs' : s' ∈ Icc (0 : ℝ) T) (α β : MultiIndex d) {E : Set ℝ} (hE : MeasurableSet E)
    (hsub : E ⊆ Icc 0 T ∩ Iio s ∩ Iio s') :
    AEMeasurable (fun τ => s101D C m T z τ (s101W m T s α) (s101W m T s' β)) (volume.restrict E) := by
  have h := A.hmeas s s' (oscTestFun m α) (oscTestFun m β) (s101_isCombo_single m α)
    (s101_isCombo_single m β) hs hs'
  have h2 : AEMeasurable (fun τ => 2 * C.ν * z τ (fun x => inner ℝ
      (gradient (propagatorW C τ s (oscTestFun m α)) x)
      (gradient (propagatorW C τ s' (oscTestFun m β)) x))) (volume.restrict (Icc 0 (min s s'))) :=
    h.const_mul _
  have hE' : E ⊆ Icc 0 (min s s') := fun τ hτ => by
    obtain ⟨⟨h1, h2⟩, h3⟩ := hsub hτ
    exact ⟨h1.1, le_min h2.le h3.le⟩
  refine (h2.mono_measure (Measure.restrict_mono hE' le_rfl)).congr ?_
  refine (ae_restrict_iff' hE).2 (Eventually.of_forall fun τ hτ => ?_)
  obtain ⟨⟨h1, h2⟩, h3⟩ := hsub hτ
  exact (s101_D_W_lt A h1 hs hs' h2 h3 α β).symm

end HRS.MS.CovMeas
