import HRS.MC.E213Defs
import HRS.MC.E213U16b
import HRS.MC.E213U13g
import HRS.MC.E213Q1
import HRS.MC.E213Q2
import HRS.MC.E213U4
import HRS.MC.E213U5b
import HRS.MC.L2C0
import HRS.MC.S7PIS1Eval
import HRS.MC.S7PIS1Path2
import HRS.MC.S7PIECont

/-!
# Packet e213u16, file c: Gaussian infrastructure for the limit field

* `u16_fdd`: finite-dimensional Gaussianity of the Fourier coordinates of `η` (`FddGaussian`);
* `u16_slice_gauss`: a finite sum of continuous linear functionals of time slices of `η` is a centred real Gaussian.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false

noncomputable section

namespace HRS.MC.E213U16

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Q HRS.MC.E213U13 HRS.MC.E213Plan

variable {d : ℕ}

section Fdd

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

/-- Finite-dimensional Gaussianity of the Fourier coordinates of the limit field `η`. -/
theorem u16_fdd : FddGaussian gd.P₀ gd.η (Set.Ici 0) := by
  classical
  intro ι _ τ hτ J
  have hF := eta_gaussFam S β₀ (rLvl d) gd.P₀ gd.η gd.limit
  set N := Fintype.card (ι × J) with hN
  let e : ι × J ≃ Fin N := Fintype.equivFin _
  let f : Fin N → KIdx d := fun a => (⟨τ (e.symm a).1, hτ _⟩, (e.symm a).2)
  have h1 := hF.fdd N f
  refine ⟨?_, fun p => hF.mean (⟨⟨τ p.1, hτ _⟩, p.2⟩ : KIdx d)⟩
  let L : (Fin N → ℝ) →L[ℝ] (ι × J → ℝ) :=
    ContinuousLinearMap.pi fun p => (ContinuousLinearMap.proj (e p) : (Fin N → ℝ) →L[ℝ] ℝ)
  have h2 := h1.map_fun L
  convert h2 using 1
  funext ω p
  simp [L, f, etaCoef]

theorem u16_fdd_Icc (H : ℝ) : FddGaussian gd.P₀ gd.η (Set.Icc 0 H) := fun ι _ τ hτ J =>
  u16_fdd gd ι τ (fun i => (hτ i).1) J

/-- A finite sum of continuous linear functionals of finitely many time slices of `η` (times in `[0,H]`) is a centred
real Gaussian. -/
theorem u16_slice_gauss (H : ℝ) {ι : Type} [Fintype ι] (t : ι → ℝ) (ht : ∀ i, t i ∈ Set.Icc 0 H)
    (L : ι → StrongDual ℝ (NegSobolev d (rLvl d))) :
    ∃ v : ℝ≥0, gd.P₀.map (fun ω => ∑ i, L i (gd.η (t i) ω)) = gaussianReal 0 v := by
  obtain ⟨Y₀, -, hlin⟩ := gd.limit
  have hmeas : ∀ s, Measurable (gd.η s) := fun s => (hlin s).meas s
  refine e213q_lin_gaussian (u16_fdd_Icc gd H) t ht L _ ?_ (Eventually.of_forall fun ω => rfl)
  exact (Finset.measurable_sum _ fun i _ => (L i).continuous.measurable.comp (hmeas (t i))).aemeasurable

end Fdd

end HRS.MC.E213U16

end
