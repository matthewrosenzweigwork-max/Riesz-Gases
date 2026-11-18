import HRS.MS.SA12W2N
import HRS.Kernel.GradD1

/-!
# S.A.12 C5 (SA12W2 worker), part O: the drift bridge (`R26-T5.T05`, drift half)

`sa12w2_drift_bridge`: `convGradConvL L (∇γ) μ (L y) = L^{-s-1} ∇g * (L^d μ(L·)) (mk y)`, comparing the Euclidean-ball cutoff
(radius `1/4` in `x`) with the torus cube cutoff (radius `1/4` in `y`); the difference is the odd annulus integral
`sa12w2_Q_int_zero`.
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

theorem sa12w2_drift_bridge (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {L : ℝ} (hL : 0 < L)
    {γ : Euc d → ℝ} (hγ : IsPeriodicRieszKernel d s L γ) {μt : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μt)
    (hμp : ∀ (x : Euc d) (z : Fin d → ℤ), μt (x + L • latticePt z) = μt x) (y' : Euc d) :
    convGradConvL L (gradient γ) μt (L • y') =
      (L ^ (-s - 1)) • convGradConv (periodicRieszGrad d s) (sa12w2_dens L μt) (Torus.mk y') := by
  obtain ⟨C, hG⟩ := HRS.KernelGradD1.goodKernel_periodicRieszGrad_of_one_le hd hs0 hsd
  set G : Torus d → Euc d := periodicRieszGrad d s with hGdef
  set ρ' : Torus d → ℝ := sa12w2_dens L μt with hρ'
  set X : Torus d := Torus.mk y' with hX
  set x : Euc d := L • y' with hx
  have hρ1 : Torus.IsCk 1 ρ' :=
    sa12w2_contDiff_desc (f := fun x => L ^ d * μt x) (fun x z => by rw [hμp x z]) hL.ne'
      (contDiff_const.mul (hμ.of_le (by simp)))
  obtain ⟨B, hB0, hB⟩ := HRS.KernelGrad.isCk_bounded hρ1
  obtain ⟨Lip, hLip0, hLip⟩ := HRS.KernelGrad.isLipschitz_of_isCk hρ1
  have hρc : Continuous ρ' := HRS.KernelGrad.isCk_continuous hρ1
  -- the Euclidean side as an integral over the centred box
  set Ψ : Euc d → Euc d := fun z => if ‖z‖ ≤ 1 / 4 then (μt (x - z) - μt x) • gradient γ z
    else μt (x - z) • gradient γ z with hΨ
  have e1 : convGradConvL L (gradient γ) μt x = ∫ z in centeredBox d L, Ψ z := by
    unfold convGradConvL
    have hset : {y : Euc d | ∀ i, -(L / 2) ≤ (x - y) i ∧ (x - y) i < L / 2} =
        (fun y => x - y) ⁻¹' centeredBox d L := rfl
    rw [hset]
    have := (Measure.measurePreserving_sub_left (volume : Measure (Euc d)) x).setIntegral_preimage_emb
      (MeasurableEquiv.subLeft x).measurableEmbedding Ψ (centeredBox d L)
    refine Eq.trans ?_ this
    refine setIntegral_congr_fun (sa12w2_measurableSet_cb L |>.preimage (measurable_const.sub measurable_id))
      fun y _ => ?_
    simp only [hΨ, sub_sub_cancel]
  have e2 : ∫ z in centeredBox d L, Ψ z = L ^ d • ∫ w in sa12w2_cubeC d, Ψ (L • w) := by
    have := sa12w2_set_smul hL (sa12w2_measurableSet_cb L) Ψ
    rw [sa12w2_cb_preimage hL] at this
    rw [this, smul_smul, mul_inv_cancel₀ (pow_pos hL d).ne', one_smul]
  set K₁ : Euc d → Euc d := fun w => if ‖L • w‖ ≤ 1 / 4 then (ρ' (X - Torus.mk w) - ρ' X) • G (Torus.mk w)
    else ρ' (X - Torus.mk w) • G (Torus.mk w) with hK₁
  set K₂ : Euc d → Euc d := fun w => HRS.KernelGrad.kern G ρ' X (Torus.mk w) with hK₂
  have hpt : ∀ w, K₁ w = K₂ w + ρ' X • sa12w2_Q L G w := by
    intro w
    simp only [hK₁, hK₂, HRS.KernelGrad.kern, sa12w2_Q]
    split_ifs <;> simp [sub_smul] <;> abel
  set c : ℝ := (L ^ d)⁻¹ * L ^ (-s - 1) with hc
  have hnull : ∀ᵐ w ∂(volume.restrict (sa12w2_cubeC d)), (Torus.mk w : Torus d) ≠ 0 := by
    have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    refine ae_restrict_of_ae ?_
    have hcnt : (Set.range fun z : Lattice d => Lattice.toEuc z).Countable := Set.countable_range _
    filter_upwards [hcnt.ae_notMem (volume : Measure (Euc d))] with w hw h0
    obtain ⟨n, hn⟩ := HRS.MS.Ker1.ker1_mk_eq_zero h0
    exact hw ⟨n, hn.symm⟩
  have hae : ∀ᵐ w ∂(volume.restrict (sa12w2_cubeC d)), Ψ (L • w) = c • K₁ w := by
    filter_upwards [hnull] with w hw
    have hx1 : μt (x - L • w) = (L ^ d)⁻¹ * ρ' (X - Torus.mk w) := by
      have h := sa12w2_dens_lift hμp (y' - w)
      have e : x - L • w = L • (y' - w) := by rw [hx, smul_sub]
      rw [e, sa12w2_mk_sub] at *
      simp only [hρ'] at *
      show μt (L • (y' - w)) = (L ^ d)⁻¹ * (Torus.lift (sa12w2_dens L μt) (y' - w))
      rw [h]
      field_simp
    have hx2 : μt x = (L ^ d)⁻¹ * ρ' X := by
      have h := sa12w2_dens_lift hμp y'
      show μt x = (L ^ d)⁻¹ * (Torus.lift (sa12w2_dens L μt) y')
      rw [h, hx]
      field_simp
    have hx3 := sa12w2_grad_gamma hd hs0 hsd hL hγ hw
    simp only [hΨ, hK₁]
    rw [hx1, hx2, hx3]
    split_ifs
    · rw [smul_smul, hc, ← mul_sub, smul_smul]
      congr 1
      ring
    · rw [smul_smul, hc, smul_smul]
      congr 1
      ring
  have e3 : ∫ w in sa12w2_cubeC d, Ψ (L • w) = c • ∫ w in sa12w2_cubeC d, K₁ w := by
    rw [integral_congr_ae hae, integral_smul]
  have hkern := HRS.KernelGrad.integrable_kern hG hρc.measurable hB hLip hLip0 hB0 X
  have hK2int : Integrable K₂ (volume.restrict (sa12w2_cubeC d)) :=
    ((sa12w2_mk_mp_cubeC (d := d)).integrable_comp hkern.aestronglyMeasurable).2 hkern
  have hQint : Integrable (fun w => ρ' X • sa12w2_Q L G w) (volume.restrict (sa12w2_cubeC d)) :=
    (sa12w2_Q_integrable hL hd hG (L := L)).smul (ρ' X)
  have e4 : ∫ w in sa12w2_cubeC d, K₁ w = ∫ w in sa12w2_cubeC d, K₂ w := by
    simp_rw [hpt]
    rw [integral_add hK2int hQint, integral_smul, sa12w2_Q_int_zero hG, smul_zero, add_zero]
  have e5 : convGradConv G ρ' X = ∫ w in sa12w2_cubeC d, K₂ w := by
    rw [HRS.KernelGrad.convGradConv_eq_integral_kern]
    exact sa12w2_torus_int_cubeC _ (HRS.KernelGrad.measurable_kern hG hρc.measurable X).aestronglyMeasurable
  rw [e1, e2, e3, e4, ← e5, smul_smul, hc, ← mul_assoc, mul_inv_cancel₀ (pow_pos hL d).ne', one_mul]

end HRS.PDE.SA12W2
