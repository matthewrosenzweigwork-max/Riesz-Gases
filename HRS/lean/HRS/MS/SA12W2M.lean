import HRS.MS.SA12W2L
import HRS.Kernel.GradSmooth
import HRS.Kernel.D1

/-!
# S.A.12 C5 (SA12W2 worker), part M: gradient of the unit-period kernel and of `γ`

* `sa12w2_grad_g1`: `∇(periodicRiesz ∘ mk)(y) = periodicRieszGrad (mk y)` off the lattice, for every `d ≥ 1`
  (`d ≥ 2` from `periodicRieszGrad_hasGradientAt`; `d = 1` from `KernelD1Aux.hasDerivAt_g_ev`);
* `sa12w2_grad_gamma`: `∇γ (L w) = L^{-s-1} ∇g (mk w)` for `γ` a periodic Riesz kernel and `mk w ≠ 0`.
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

theorem sa12w2_grad_g1 (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {y : Euc d}
    (hy : Torus.mk y ≠ 0) :
    HasGradientAt (HRS.MS.Ker1.ker1_g1 d s) (periodicRieszGrad d s (Torus.mk y)) y := by
  rcases Nat.lt_or_ge d 2 with h | h
  · obtain rfl : d = 1 := by omega
    have hs1 : s < 1 := by simpa using hsd
    have hoff := HRS.KernelD1Aux.off_int_of_mk_ne hy
    have hder := HRS.KernelD1Aux.hasDerivAt_g_ev hs0 hs1 (y0 := y 0) hoff
    have hyev : y = HRS.KernelD1Aux.ev (y 0) := HRS.KernelD1Aux.ev_eq y
    have hgrad : periodicRieszGrad 1 s (Torus.mk y) =
        HRS.KernelD1Aux.ev ((periodicRieszGrad 1 s (Torus.mk (HRS.KernelD1Aux.ev (y 0)))) 0) := by
      rw [← hyev]; exact HRS.KernelD1Aux.ev_eq _
    rw [hasGradientAt_iff_hasFDerivAt]
    have hp : HasFDerivAt (fun z : Euc 1 => z 0) (EuclideanSpace.proj (0 : Fin 1) : Euc 1 →L[ℝ] ℝ) y :=
      (EuclideanSpace.proj (0 : Fin 1) : Euc 1 →L[ℝ] ℝ).hasFDerivAt
    have h2 := HasFDerivAt.comp y hder.hasFDerivAt hp
    have hfun : (HRS.MS.Ker1.ker1_g1 1 s) = fun z : Euc 1 =>
        (fun t : ℝ => periodicRiesz 1 s (Torus.mk (HRS.KernelD1Aux.ev t))) (z 0) := by
      funext z
      simp only [HRS.MS.Ker1.ker1_g1]
      rw [← HRS.KernelD1Aux.ev_eq z]
    rw [hfun]
    refine h2.congr_fderiv ?_
    ext v
    rw [hgrad]
    simp [InnerProductSpace.toDual_apply_apply, PiLp.inner_apply, HRS.KernelD1Aux.ev, mul_comm]
  · exact HRS.KernelGrad.periodicRieszGrad_hasGradientAt h hs0 hsd hy y rfl

theorem sa12w2_grad_gamma (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {L : ℝ} (hL : 0 < L)
    {γ : Euc d → ℝ} (hγ : IsPeriodicRieszKernel d s L γ) {w : Euc d} (hw : Torus.mk w ≠ 0) :
    gradient γ (L • w) = (L ^ (-s - 1)) • periodicRieszGrad d s (Torus.mk w) := by
  have hV : IsOpen {x : Euc d | Torus.mk (L⁻¹ • x) ≠ 0} :=
    HRS.KernelGrad.isOpen_mk_ne_zero.preimage (continuous_const_smul L⁻¹)
  have hmem : L • w ∈ {x : Euc d | Torus.mk (L⁻¹ • x) ≠ 0} := by
    simpa [inv_smul_smul₀ hL.ne'] using hw
  have hev : γ =ᶠ[𝓝 (L • w)] HRS.MS.Ker1.ker1_gam d s L := by
    filter_upwards [hV.mem_nhds hmem] with x hx
    refine HRS.MS.Ker1.ker1_eq_gam hd hs0 hsd hL hγ x (fun z hz => hx ?_)
    have : L⁻¹ • x = Lattice.toEuc z := by
      rw [hz, inv_smul_smul₀ hL.ne']; rfl
    rw [this]; exact HRS.MS.Ker1.ker1_mk_toEuc z
  have h1 := hasGradientAt_iff_hasFDerivAt.1 (sa12w2_grad_g1 hd hs0 hsd hw)
  have h1' : HasFDerivAt (HRS.MS.Ker1.ker1_g1 d s)
      ((InnerProductSpace.toDual ℝ (Euc d)) (periodicRieszGrad d s (Torus.mk w))) (L⁻¹ • (L • w)) := by
    rwa [inv_smul_smul₀ hL.ne']
  have h2 := (h1'.comp (L • w) ((hasFDerivAt_id (L • w)).const_smul L⁻¹)).const_mul (L ^ (-s))
  have h3 : HasGradientAt (HRS.MS.Ker1.ker1_gam d s L)
      ((L ^ (-s - 1)) • periodicRieszGrad d s (Torus.mk w)) (L • w) := by
    rw [hasGradientAt_iff_hasFDerivAt]
    refine h2.congr_fderiv ?_
    ext v
    have : L ^ (-s - 1) = L ^ (-s) * L⁻¹ := by
      rw [Real.rpow_sub hL, Real.rpow_one]; ring
    simp [this, InnerProductSpace.toDual_apply_apply, inner_smul_left]
    ring
  have h4 := h3.gradient
  have h5 : gradient γ (L • w) = gradient (HRS.MS.Ker1.ker1_gam d s L) (L • w) := by
    unfold gradient
    rw [hev.fderiv_eq]
  rw [h5, h4]

end HRS.PDE.SA12W2
