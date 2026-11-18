import HRS.MS.SA12W2H
import HRS.MS.Ker1Aux3
import HRS.PDE.MeanFieldOneLe

/-!
# S.A.12 C5 (SA12W2 worker), part I: periodic and torus convolutions on the unit cube

* `sa12w2_perConv_torus`: `perConv L γ k (L y) = L^{d-s} ∫_{[0,1)^d} g(y-w) k(L w) dw` for `γ` a periodic Riesz kernel
  (`g = periodicRiesz ∘ mk`; uses `γ = γ_L` off the lattice, `ker1_eq_gam`);
* `sa12w2_conv_cube`: the native `∑_j ∂_j g * H_j` (cancellation convention) as the same cube integral of `g(y-w)∑_j∂_jH_j`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ComplexConjugate ContDiff

namespace HRS.PDE.SA12W2

variable {d : ℕ}

open HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12Construction

theorem sa12w2_mk_sub (x y : Euc d) : Torus.mk x - Torus.mk y = Torus.mk (x - y) := by
  have h := Torus.mk_add (x - y) y
  rw [sub_add_cancel] at h
  rw [h]
  abel

theorem sa12w2_perConv_torus (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {L : ℝ} (hL : 0 < L)
    {γ : Euc d → ℝ} (hγ : IsPeriodicRieszKernel d s L γ) (k : Euc d → ℝ) (y' : Euc d) :
    perConv L γ k (L • y') = L ^ d * L ^ (-s) *
      ∫ w in HRS.MC.CepP3.cubeE d, HRS.MS.Ker1.ker1_g1 d s (y' - w) * k (L • w) := by
  have hbox := sa12w2_cube_box hL (fun z : Euc d => γ (L • y' - z) * k z)
  have e1 : perConv L γ k (L • y') = L ^ d * ∫ w in HRS.MC.CepP3.cubeE d, γ (L • (y' - w)) * k (L • w) := by
    have h1 : ∫ z in periodBox d L, γ (L • y' - z) * k z =
        L ^ d * ∫ w in HRS.MC.CepP3.cubeE d, γ (L • y' - L • w) * k (L • w) := by
      rw [hbox]
      simp only [smul_eq_mul]
      rw [← mul_assoc, mul_inv_cancel₀ (pow_pos hL d).ne', one_mul]
    unfold perConv
    rw [h1]
    simp only [smul_sub]
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hnull : ∀ᵐ w ∂(volume.restrict (HRS.MC.CepP3.cubeE d)), ∀ z' : Fin d → ℤ, y' - w ≠ latticePt z' := by
    refine ae_restrict_of_ae ?_
    have hc : (Set.range fun z' : Fin d → ℤ => y' - latticePt z').Countable := Set.countable_range _
    filter_upwards [hc.ae_notMem (volume : Measure (Euc d))] with w hw z' h
    exact hw ⟨z', by show y' - latticePt z' = w; rw [← h]; abel⟩
  have e2 : ∫ w in HRS.MC.CepP3.cubeE d, γ (L • (y' - w)) * k (L • w) =
      L ^ (-s) * ∫ w in HRS.MC.CepP3.cubeE d, HRS.MS.Ker1.ker1_g1 d s (y' - w) * k (L • w) := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hnull] with w hw
    have := HRS.MS.Ker1.ker1_eq_gam hd hs0 hsd hL hγ (L • (y' - w)) (fun z' h => by
      exact hw z' (smul_right_injective _ hL.ne' h))
    rw [this]
    simp only [HRS.MS.Ker1.ker1_gam, inv_smul_smul₀ hL.ne']
    ring
  rw [e1, e2]
  ring

/-- The native cancellation-convention nonlocal term as a cube integral. -/
theorem sa12w2_conv_cube (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (H : Fin d → Torus d → ℝ)
    (hH : ∀ j, Torus.IsCk 1 (H j)) (y' : Euc d) :
    ∑ j, (convGradConv (periodicRieszGrad d s) (H j) (Torus.mk y')) j =
      ∫ w in HRS.MC.CepP3.cubeE d, HRS.MS.Ker1.ker1_g1 d s (y' - w) *
        ∑ j, Torus.partialDeriv j (H j) (Torus.mk w) := by
  rw [HRS.PDE.MFOneLe.sum_convGradConv_eq hd s hs0 hsd H hH]
  show ∫ y, periodicRiesz d s (Torus.mk y' - y) * ∑ j, Torus.partialDeriv j (H j) y = _
  have hDc : Continuous fun y => ∑ j, Torus.partialDeriv j (H j) y :=
    continuous_finsetSum _ fun j _ => continuous_partialDeriv j _ (hH j)
  have h1 : AEStronglyMeasurable (periodicRiesz d s) volume :=
    (HRS.PDE.MFOneLe.integrable_periodicRiesz hd s hs0 hsd).aestronglyMeasurable
  have h2 : AEStronglyMeasurable (fun v : Torus d => periodicRiesz d s (Torus.mk y' - v)) volume :=
    h1.comp_quasiMeasurePreserving
      (Measure.measurePreserving_sub_left (volume : Measure (Torus d)) (Torus.mk y')).quasiMeasurePreserving
  have hm : AEStronglyMeasurable (fun y : Torus d => periodicRiesz d s (Torus.mk y' - y) *
      ∑ j, Torus.partialDeriv j (H j) y) volume := h2.mul hDc.aestronglyMeasurable
  rw [sa12w2_torus_int_cube _ hm]
  refine setIntegral_congr_fun HRS.MC.CepP3.measurableSet_cubeE fun w _ => ?_
  simp only [sa12w2_mk_sub, HRS.MS.Ker1.ker1_g1]

end HRS.PDE.SA12W2
