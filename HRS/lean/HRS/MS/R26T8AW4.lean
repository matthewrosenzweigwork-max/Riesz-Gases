import HRS.MS.R26T8AP16a
import HRS.MS.R26T8AW3
import HRS.MS.R26T8AZ7d

/-!
# S8.2 T8A W4 (= P16b same-k): the conormal half of the half-order defect (`r26t8a_defect_half_order`)
`r26t8a_defect_half_order_conormal_same`: `newtonDefect` is `Conormal k 0 (M+2) (σ - 1/2)` for `F` with `Conormal (k+2) 0 M σ A F` (every `σ < d`).
Proof: `newtonDefect = (newtonDefect - pairJ Q) + pairJ Q`; P15 gives the first part of order `σ-2`, P13 the second of order `σ - d/2 ≤ σ - 1`
(degree `2`), then `r26t8a_conormal_lower`.  The `CanonicalPair` conclusion of the Pro contract is NOT proved here (see handoff).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

theorem r26t8a_defect_half_order_conormal_same (d : ℕ) (hd : 2 ≤ d) (k : ℕ)
    (a beta M sigma : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M) (hsigma : sigma < d)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ F : Euc d → Euc d → ℝ, ∀ A : ℝ, 0 ≤ A →
      Conormal (k + 2) 0 M sigma A F →
      Conormal k 0 (M + 2) (sigma - 1 / 2) (C * A)
        (newtonDefect (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi F) := by
  obtain ⟨C1, hC10, hC1⟩ := r26t8a_local_defect_bound_same d hd k a beta M sigma ha hbeta hM hsigma chi hchi
  obtain ⟨C2, hC20, hC2⟩ := r26t8a_newton_nonlocal_bound_same d hd k 0 a beta M sigma ha hbeta hM hsigma chi hchi
  obtain ⟨c, hc1, hc⟩ := r26t8a_conormal_lower (d := d) k 2 (M + 2) (sigma - 1)
  refine ⟨c * (C1 + C2), by positivity, fun rho hrho F A hA hF => ?_⟩
  have hT := hC1 rho hrho F A hA hF
  have hP := hC2 rho hrho F A hA hF
  have hT' : Conormal k 2 (M + 2) (sigma - 1) (C1 * A)
      (fun x y => newtonDefect (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi F x y -
        pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho)
          (localNewton (HRS.Whole.withDensityReal rho) beta⁻¹ chi F) x y) :=
    r26t8a_conormal_mono_sA (by positivity) le_rfl (by linarith)
      (r26t8a_conormal_mono_b (by positivity) (by norm_num : 1 ≤ 2) hT)
  have hcrit : (1 : ℝ) ≤ criticalS d := by
    unfold criticalS
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hP' : Conormal k (0 + 2) (M + 2) (sigma - 1) (C2 * A)
      (pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho)
        (localNewton (HRS.Whole.withDensityReal rho) beta⁻¹ chi F)) :=
    r26t8a_conormal_mono_sA (by positivity) le_rfl (by linarith) hP
  have hsum := r26t8a_conormal_add hchi hT' hP'
  have hsum' : Conormal k 2 (M + 2) (sigma - 1) ((C1 + C2) * A)
      (newtonDefect (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi F) := by
    refine r26t8a_conormal_congr (fun x y _ => ?_)
      (r26t8a_conormal_mono_sA (by positivity) (le_of_eq (by ring)) le_rfl hsum)
    ring
  have := hc ((C1 + C2) * A) (by positivity) hsum'
  refine r26t8a_conormal_mono_sA (by positivity) (le_of_eq (by ring)) (le_of_eq (by ring)) this

end HRS.MS.R26T8A
