import HRS.MS.R2WinErrNL2
import HRS.MS.R2GenInitAux38

/-!
# S10.4, nonlinear branch, part 3: measurability of the centered pair functional with a parameter dependent kernel and density

`s104n_cpf_meas`: for a measurable parameter space `Θ`, a jointly measurable kernel `K θ x y` and a jointly measurable family of probability
densities `ρ' θ`, the map `(θ, Z) ↦ centeredPairFunctional (K θ) Z (ρ' θ dx)` is measurable on `Θ × EucConfig d N`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2WinErr

open HRS HRS.Whole HRS.MP.RdRem

variable {d N : ℕ} {Θ : Type*} [MeasurableSpace Θ]

theorem s104n_kernel_meas_of (s : ℝ) {v : Θ → Euc d → Euc d} (hv : Measurable fun q : Θ × Euc d => v q.1 q.2) :
    Measurable fun q : Θ × Euc d × Euc d => commutatorKernel d s (v q.1) q.2.1 q.2.2 := by
  have hgr : Measurable (rieszKernelGrad d s) := by
    unfold rieszKernelGrad gradient
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.measurable.comp (measurable_fderiv ℝ _)
  have h1 : Measurable fun q : Θ × Euc d × Euc d => v q.1 q.2.1 :=
    hv.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have h2 : Measurable fun q : Θ × Euc d × Euc d => v q.1 q.2.2 :=
    hv.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have h3 : Measurable fun q : Θ × Euc d × Euc d => rieszKernelGrad d s (q.2.1 - q.2.2) :=
    hgr.comp ((measurable_fst.comp measurable_snd).sub (measurable_snd.comp measurable_snd))
  exact (h1.sub h2).inner h3

set_option maxHeartbeats 3200000 in
theorem s104n_cpf_meas {K : Θ → Euc d → Euc d → ℝ}
    (hK : Measurable fun q : Θ × Euc d × Euc d => K q.1 q.2.1 q.2.2)
    {ρ' : Θ → Euc d → ℝ} (hρm : Measurable fun q : Θ × Euc d => ρ' q.1 q.2)
    (hρp : ∀ θ, HRS.Whole.IsProbDensity (ρ' θ)) :
    Measurable fun p : Θ × EucConfig d N =>
      centeredPairFunctional (K p.1) p.2 (HRS.Whole.withDensityReal (ρ' p.1)) := by
  unfold centeredPairFunctional
  have t1 : Measurable fun p : Θ × EucConfig d N => ∑ i, ∑ j ∈ Finset.univ.erase i, K p.1 (p.2 i) (p.2 j) := by
    refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
    have hmap : Measurable fun p : Θ × EucConfig d N => ((p.1, p.2 i, p.2 j) : Θ × Euc d × Euc d) :=
      measurable_fst.prodMk (((measurable_pi_apply i).comp measurable_snd).prodMk
        ((measurable_pi_apply j).comp measurable_snd))
    have hc := hK.comp hmap
    simpa only [Function.comp_def] using hc
  have t2 : ∀ i : Fin N, Measurable fun p : Θ × EucConfig d N =>
      ∫ y, K p.1 (p.2 i) y ∂(HRS.Whole.withDensityReal (ρ' p.1)) := by
    intro i
    have e : (fun p : Θ × EucConfig d N => ∫ y, K p.1 (p.2 i) y ∂(HRS.Whole.withDensityReal (ρ' p.1))) =
        fun p => ∫ y, ρ' p.1 y * K p.1 (p.2 i) y := by
      funext p
      exact mrr_integral_withDensityReal (ρ' p.1) (hρp p.1).measurable (hρp p.1).nonneg
        (fun y => K p.1 (p.2 i) y)
    rw [e]
    have hρs : Measurable fun q : (Θ × EucConfig d N) × Euc d => ρ' q.1.1 q.2 :=
      hρm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    have hmap : Measurable fun q : (Θ × EucConfig d N) × Euc d =>
        ((q.1.1, q.1.2 i, q.2) : Θ × Euc d × Euc d) :=
      (measurable_fst.comp measurable_fst).prodMk
        (((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
    have hKq : Measurable fun q : (Θ × EucConfig d N) × Euc d => K q.1.1 (q.1.2 i) q.2 := by
      have hc := hK.comp hmap
      simpa only [Function.comp_def] using hc
    exact ((hρs.mul hKq).stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  have t3 : Measurable fun θ : Θ => ∫ x, ∫ y, K θ x y ∂(HRS.Whole.withDensityReal (ρ' θ))
      ∂(HRS.Whole.withDensityReal (ρ' θ)) := by
    have e : (fun θ : Θ => ∫ x, ∫ y, K θ x y ∂(HRS.Whole.withDensityReal (ρ' θ))
        ∂(HRS.Whole.withDensityReal (ρ' θ))) = fun θ => ∫ x, ρ' θ x * ∫ y, ρ' θ y * K θ x y := by
      funext θ
      rw [mrr_integral_withDensityReal (ρ' θ) (hρp θ).measurable (hρp θ).nonneg
        (fun x => ∫ y, K θ x y ∂(HRS.Whole.withDensityReal (ρ' θ)))]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show ρ' θ x * _ = ρ' θ x * _
      rw [mrr_integral_withDensityReal (ρ' θ) (hρp θ).measurable (hρp θ).nonneg (fun y => K θ x y)]
    rw [e]
    have hρs : Measurable fun q : (Θ × Euc d) × Euc d => ρ' q.1.1 q.2 :=
      hρm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    have hmap : Measurable fun q : (Θ × Euc d) × Euc d => ((q.1.1, q.1.2, q.2) : Θ × Euc d × Euc d) :=
      (measurable_fst.comp measurable_fst).prodMk ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    have hKq : Measurable fun q : (Θ × Euc d) × Euc d => K q.1.1 q.1.2 q.2 := by
      have hc := hK.comp hmap
      simpa only [Function.comp_def] using hc
    have h2 : StronglyMeasurable fun q : (Θ × Euc d) × Euc d => ρ' q.1.1 q.2 * K q.1.1 q.1.2 q.2 :=
      (hρs.mul hKq).stronglyMeasurable
    have h3 : StronglyMeasurable fun q : Θ × Euc d => ρ' q.1 q.2 * ∫ y, ρ' q.1 y * K q.1 q.2 y :=
      hρm.stronglyMeasurable.mul (h2.integral_prod_right' (ν := volume))
    exact (h3.integral_prod_right' (ν := volume)).measurable
  exact (((measurable_const.mul t1).sub (measurable_const.mul (measurable_const.mul
    (Finset.measurable_sum _ fun i _ => t2 i)))).add (t3.comp measurable_fst))

end HRS.MS.R2WinErr
