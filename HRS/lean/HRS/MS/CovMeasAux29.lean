import HRS.MS.CovMeasAux28

/-!
# S10.1 (worker S101B), part 29: assembly of `r2_covariance_measure`

`s101Jm` is `Jm z a a' = (Ψ ∘ J D'_z)((a,a'])` for weakly admissible `z` (`S101Lin`, `R2JIntegrandMeas`, `S101Tr`), `0` otherwise.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.CovMeas

open HRS HRS.Whole HRS.MS.Go HRS.MS.FixEq HRS.Uniform HRS.Uniform.Q45 HRS.MS.GenPath HRS.MS.U9
open Classical

variable {d : ℕ}

/-- Weak admissibility. -/
def S101AdmP (C : WholeCoeff d) (m T : ℝ) (r : ℕ) (Pw : ℝ) (z : ℝ → (Euc d → ℝ) → ℝ) : Prop :=
  S101Lin r Pw T z ∧ R2JIntegrandMeas C m T z ∧ S101Tr C m T z

def s101Jm {m T : ℝ} (hT : 0 ≤ T)
    (J : (ℝ → KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ) → VectorMeasure ℝ (ProjTensor2 (PathSp T (KSpace d m T))))
    (C : WholeCoeff d) (r : ℕ) (Pw : ℝ) (z : ℝ → (Euc d → ℝ) → ℝ) (a a' : ℝ) :
    projTensor (OscPath d m T) 2 :=
  if h : S101AdmP C m T r Pw z then
    ⟨s101Jx hT J (s101Dm C m T z) (Ioc a a'), s101Psi_mem hT _⟩ else 0

section Final

variable {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {Pw : ℝ} {z z' : ℝ → (Euc d → ℝ) → ℝ}

lemma s101Jm_coe {hT : 0 ≤ T}
    {J : (ℝ → KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ) → VectorMeasure ℝ (ProjTensor2 (PathSp T (KSpace d m T)))}
    (h : S101AdmP C m T r Pw z) (a a' : ℝ) :
    ((s101Jm hT J C r Pw z a a' : projTensor (OscPath d m T) 2) : TensorDual (OscPath d m T) 2) =
      s101Jx hT J (s101Dm C m T z) (Ioc a a') := by
  unfold s101Jm; rw [dif_pos h]

lemma S101AdmP.adm (hd : 1 ≤ d) (hP : (d : ℝ) < 2 * Pw) (horb : R2OrbitSummable C m T r)
    (h : S101AdmP C m T r Pw z) : S101Adm C m T r Pw z := ⟨hd, hP, horb, h.1, h.2.1⟩

lemma S101AdmP.add (hd : 1 ≤ d) (hP : (d : ℝ) < 2 * Pw) (horb : R2OrbitSummable C m T r) (hT : 0 ≤ T)
    (h : S101AdmP C m T r Pw z) (h' : S101AdmP C m T r Pw z') : S101AdmP C m T r Pw (z + z') :=
  ⟨h.1.add h'.1, s101_meas_add h.2.1 h'.2.1,
    S101Tr.add (h.adm hd hP horb) (h'.adm hd hP horb) hT h.2.2 h'.2.2⟩

lemma S101AdmP.smul (hd : 1 ≤ d) (hP : (d : ℝ) < 2 * Pw) (horb : R2OrbitSummable C m T r) (hT : 0 ≤ T)
    (c : ℝ) (h : S101AdmP C m T r Pw z) : S101AdmP C m T r Pw (c • z) :=
  ⟨h.1.smul c, s101_meas_smul c h.2.1, S101Tr.smul c (h.adm hd hP horb) hT h.2.2⟩

lemma s101_admP_of_L1F (hd : 1 ≤ d) (hP : (d : ℝ) < 2 * Pw) (horb : R2OrbitSummable C m T r) (hT : 0 ≤ T)
    (hz : IsR2L1F r Pw T z) (hm : R2JIntegrandMeas C m T z) : S101AdmP C m T r Pw z :=
  ⟨hz.1, hm, s101_htr_of_L1F ⟨hd, hP, horb, hz.1, hm⟩ hT hz⟩

theorem s101_Dm_trace_bound' (A : S101Adm C m T r Pw z) (hT : 0 ≤ T) {K0 : ℝ}
    (hKb : ∀ τ ∈ Icc (0 : ℝ) T, ENNReal.ofReal (HRS.traceNormForm (s101D C m T z τ)) ≤
      ENNReal.ofReal |2 * C.ν| * dualNormE r Pw (z τ) * ENNReal.ofReal K0) :
    ∀ τ ∈ Icc (0 : ℝ) T, ENNReal.ofReal (HRS.traceNormForm (s101Dm C m T z τ)) ≤
      ENNReal.ofReal |2 * C.ν| * ENNReal.ofReal K0 * dualNormE r Pw (z τ) := by
  intro τ hτ
  rcases s101_Dm_cases A hT τ with h | h
  · rw [h]; refine (hKb τ hτ).trans (le_of_eq ?_); ring
  · rw [h]
    have : HRS.traceNormForm (0 : KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ) ≤ 0 := traceNormForm_zero_le
    rw [ENNReal.ofReal_of_nonpos this]; exact bot_le

end Final

end HRS.MS.CovMeas
