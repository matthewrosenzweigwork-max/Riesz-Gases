import HRS.Whole.AppendixAAdjoint
import HRS.MS.UniqM1Fin
import HRS.MS.UniqM1Moll

/-!
# S.A.12 U2b: the weak initial condition gives an a.e.-zero initial slice

A zero-datum weak solution whose initial slice has finite `H⁰_uloc` norm vanishes almost everywhere
at time `0`: the slice is locally integrable (local mass) and pairs to zero against every `C_c^∞` test.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.SA12BD

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

theorem sa12_initial_zero (d : ℕ) (hd : 1 ≤ d) (χ : Euc d → ℝ)
    (hχ : IsUlocCutoff χ) (C : WholeCoeff d) (t : ℝ) (ht : 0 ≤ t)
    (F : ℝ → Euc d → ℝ)
    (hF : IsForwardSolutionRd C t (fun _ => 0) F)
    (h0 : ulocNormE 0 χ (F 0) < ⊤) :
    F 0 =ᵐ[volume] 0 := by
  have h0t : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨le_rfl, ht⟩
  set B : ℝ := (ulocNormE 0 χ (F 0)).toReal with hB
  have hle : ulocNormE 0 χ (F 0) ≤ ENNReal.ofReal B := by
    rw [hB, ENNReal.ofReal_toReal h0.ne]
  have hfm := HRS.MS.UniqM1.locMass_of_ulocNormE hχ ENNReal.toReal_nonneg hle
  have hli : LocallyIntegrable (F 0) volume := hfm.locallyIntegrable
  have key := ae_eq_zero_of_integral_contDiff_smul_eq_zero hli (fun g hg hgc => ?_)
  · filter_upwards [key] with x hx
    simpa using hx
  · have h := hF.eq g ⟨hg, hgc⟩ 0 h0t
    simp only [zero_mul, integral_zero, Set.Icc_self, zero_add] at h
    simpa [smul_eq_mul, mul_comm] using h

end HRS.MS.SA12BD
