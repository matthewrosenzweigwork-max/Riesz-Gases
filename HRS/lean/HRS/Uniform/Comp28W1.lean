import HRS.Uniform.Comparison
import HRS.Uniform.Comp28Aux8
import HRS.Uniform.Q07cAux5
import HRS.Uniform.Q07cAux11
import HRS.Uniform.RelativeCoupling
import HRS.Uniform.RelativeCov
import HRS.Main.GFB1Aux3
import HRS.Uniform.Q48dAux2

/-!
# COMP-28, Wasserstein part, W1: Itô integrals are Hilbert martingales; `bures2 ≤ traceNorm` in every universe
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Comp28

open HRS HRS.Uniform

section Ito

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {κ : Type*} [Countable κ]

/-- An `H`-valued Itô integral of a Hilbert-Schmidt integrand (on every finite horizon) is a Hilbert martingale with
covariation density `hsCovForm Φ`. -/
theorem isHM_of_hilbertIto {W : ℝ≥0 → Ω → κ → ℝ} (hW : IsCylindricalBrownian P ℱ W)
    {Φ : ℝ → Ω → κ → H} (hΦ : ∀ T : ℝ, IsHSIntegrand P ℱ T Φ) {M : ℝ → Ω → H}
    (hM : IsHilbertItoIntegral P ℱ W Φ M) (t : ℝ) :
    IsHilbertMartingaleWithCovariation P ℱ t M (fun r ω => hsCovForm (Φ r ω)) := by
  refine HRS.Uniform.Q07c.isHM_of_ito hW hΦ hM.cont (fun τ => hM.adapted τ) hM.zero ?_ t
  intro x
  refine ⟨fun τ ω => inner ℝ (M τ ω) x, ⟨?_, ?_, ?_, ?_⟩, fun τ _ => Filter.EventuallyEq.rfl⟩
  · exact fun ω => (hM.cont ω).inner continuous_const
  · exact fun τ => (hM.adapted τ).inner measurable_const
  · intro τ hτ ω
    simp [hM.zero τ hτ ω]
  · intro τ hτ
    exact hM.approx τ hτ x

end Ito

section Bures

open HRS.Uniform

/-- `bures2 ≤ traceNormForm (C - D)` in every universe (copy of `HRS.GF.gf_bures2_le_traceNorm_proof` at `H : Type*`). -/
theorem bures2_le_traceNorm_any {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (C D : H →L[ℝ] H →L[ℝ] ℝ) (hC : IsTraceClassCov C) (hD : IsTraceClassCov D) :
    bures2 C D ≤ traceNormForm (C - D) := by
  classical
  obtain ⟨ι, -, e, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := H)
  set R := HRS.Uniform.formSqrt C with hRdef
  set Sq := HRS.Uniform.formSqrt D with hSdef
  have hR : IsSqrtOfForm R C := HRS.Uniform.RelCov.formSqrt_spec hC
  have hS : IsSqrtOfForm Sq D := HRS.Uniform.RelCov.formSqrt_spec hD
  have hRs := HRS.Uniform.RelCov.summable_sqrt_diag e hR hC
  have hSs := HRS.Uniform.RelCov.summable_sqrt_diag e hS hD
  obtain ⟨tC, hCt, -⟩ := hC.hasSum_basis e
  obtain ⟨tD, hDt, -⟩ := hD.hasSum_basis e
  have hnC : traceNormForm C = tC :=
    le_antisymm ((traceNormForm_le_basis_trace hC e).trans hCt.tsum_eq.le)
      (hCt.tsum_eq ▸ hC.tsum_basis_le e)
  have hnD : traceNormForm D = tD :=
    le_antisymm ((traceNormForm_le_basis_trace hD e).trans hDt.tsum_eq.le)
      (hDt.tsum_eq ▸ hD.tsum_basis_le e)
  -- the Bures bound in terms of the cross term (`q14_bures2_le` with the square roots)
  have hbures := HRS.Uniform.Q14.q14_bures2_le e hC hD R Sq hR.sq hS.sq
  -- summability of the cross term
  have hsumI : Summable (fun j => inner ℝ (R (e j)) (Sq (e j))) := by
    refine Summable.of_norm_bounded ((hRs.add hSs).mul_left (1 / 2)) fun j => ?_
    have h1 := abs_real_inner_le_norm (R (e j)) (Sq (e j))
    have h2 : ‖R (e j)‖ * ‖Sq (e j)‖ ≤ (‖R (e j)‖ ^ 2 + ‖Sq (e j)‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖R (e j)‖ - ‖Sq (e j)‖)]
    rw [Real.norm_eq_abs]
    linarith
  -- the Powers–Størmer bound for the difference of the square roots
  obtain ⟨hPs, hPle⟩ := HRS.powers_stormer e hR hS hC hD hCt.summable hDt.summable
  -- expansion of the squared difference
  have hR2 : ∀ j, ‖R (e j)‖ ^ 2 = C (e j) (e j) := fun j => by
    rw [← real_inner_self_eq_norm_sq, hR.sq]
  have hS2 : ∀ j, ‖Sq (e j)‖ ^ 2 = D (e j) (e j) := fun j => by
    rw [← real_inner_self_eq_norm_sq, hS.sq]
  have hterm : ∀ j, ‖(R - Sq) (e j)‖ ^ 2 =
      ‖R (e j)‖ ^ 2 + ‖Sq (e j)‖ ^ 2 - 2 * inner ℝ (R (e j)) (Sq (e j)) := fun j => by
    rw [ContinuousLinearMap.sub_apply, norm_sub_sq_real]
    ring
  have hP : ∑' j, ‖(R - Sq) (e j)‖ ^ 2 = tC + tD - 2 * ∑' j, inner ℝ (R (e j)) (Sq (e j)) := by
    rw [tsum_congr hterm, Summable.tsum_sub (hRs.add hSs) (hsumI.mul_left 2),
      Summable.tsum_add hRs hSs, tsum_mul_left, tsum_congr hR2, tsum_congr hS2,
      hCt.tsum_eq, hDt.tsum_eq]
  have hb := hbures
  rw [hnC, hnD] at hb
  linarith [hPle, hP, hb]


end Bures

end HRS.Uniform.Comp28
