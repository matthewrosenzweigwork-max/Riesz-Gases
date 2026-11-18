import HRS.MS.SA12C4

/-!
# S.A.12(c), packet E7.06 (part 3): the integrated rate of one jet over the period box

For an `L`-periodic smooth `F`, periodic `C^{m+1}` drift `b` with bounded derivatives `1 ≤ k ≤ m+1` and smooth `G`:
`∫_{Q_L} 2 ∂^α F ∂^α(νΔF + b·∇F + G) ≤ -2ν ∑_i ∫_{Q_L}(∂_i∂^α F)² + K ∫_{Q_L} Y + ∫_{Q_L} 2 ∂^αF ∂^αG`
with `K = d C_b + 1 + (d C_b 2^m)² c_T` (periodic integration by parts: no cutoff, exact diffusion coefficient `2ν`;
the transport term uses only `div b` and the commutator uses only derivatives of `b`).
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12C

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MH.AdjointRd.Phase2SA12Construction HRS.MH.AdjointRd.Phase2SA12Near HRS.MS.UniqT3

variable {d : ℕ}

/-- Diffusion term of one jet, by periodic integration by parts. -/
theorem sa12c_diffusion_idx {L : ℝ} (hL : 0 < L) {W : Euc d → ℝ} (hWi : ContDiff ℝ ∞ W)
    (hWp : ∀ (x : Euc d) (k : Fin d → ℤ), W (x + L • latticePt k) = W x) (i : Fin d) :
    ∫ x in periodBox d L, 2 * (W x * D1 i (D1 i W) x) = -(2 * ∫ x in periodBox d L, (D1 i W x) ^ 2) := by
  set e : Euc d := EuclideanSpace.single i (1 : ℝ) with he
  have hu1 : ContDiff ℝ 1 (D1 i W) := sa12z3_cd_of_inf (sa12y_D1_contDiff hWi i) 1
  have hw1 : ContDiff ℝ 1 W := sa12z3_cd_of_inf hWi 1
  have hup : ∀ (x : Euc d) (k : Fin d → ℤ), D1 i W (x + L • latticePt k) = D1 i W x :=
    fun x k => sa12v_fderiv_periodic L hWp e x k
  have h := sa12v_per_ibp L hL hu1 hw1 hup hWp i
  have e1 : ∀ z, D1 i W z = fderiv ℝ W z e := fun z => rfl
  have e2 : ∀ z, D1 i (D1 i W) z = fderiv ℝ (D1 i W) z e := fun z => rfl
  have h' : ∫ z in periodBox d L, D1 i (D1 i W) z * W z = -∫ z in periodBox d L, (D1 i W z) ^ 2 := by
    simp_rw [e2, e1] at *
    simpa [sq] using h
  have hc : ∫ x in periodBox d L, 2 * (W x * D1 i (D1 i W) x) =
      2 * ∫ x in periodBox d L, D1 i (D1 i W) x * W x := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    ring
  rw [hc, h']
  ring

end HRS.MH.AdjointRd.Phase2SA12C
