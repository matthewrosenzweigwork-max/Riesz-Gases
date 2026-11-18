import HRS.MS.R2GenInitAux37

/-!
# S10.5 window comparison, packet E4: measurability on the original probability space of the commutator forcing integral
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2GenInit

open HRS HRS.Whole HRS.MP.RdRem HRS.MS.GenPath

variable {d : ℕ}

theorem s105_grad_meas (C : WholeCoeff d) {t : ℝ} (ht : 0 ≤ t) {φ : Euc d → ℝ}
    (hcl : IsClassicalAdjointW C t φ (fun r => propagatorW C r t φ)) (a : Fin d) :
    Measurable fun p : ℝ × Euc d => gradComp a (propagatorW C (mrrClamp t p.1) t φ) p.2 := by
  refine s56_carath (fun (z : Euc d) (r : ℝ) => gradComp a (propagatorW C (mrrClamp t r) t φ) z) (fun r => ?_)
    (fun z => ?_)
  · exact s56_gradComp_cont ((hcl.c2 _ (mrrClamp_mem ht r)).of_le (by norm_num)) a
  · exact ((s56_gradComp_cont_r hcl a z).comp_continuous (continuous_mrrClamp t)
      (fun r => mrrClamp_mem ht r)).measurable

set_option maxHeartbeats 800000 in
theorem s105_kernel_meas (s : ℝ) (C : WholeCoeff d) {t : ℝ} (ht : 0 ≤ t) {φ : Euc d → ℝ}
    (hcl : IsClassicalAdjointW C t φ (fun r => propagatorW C r t φ)) :
    Measurable fun q : ℝ × Euc d × Euc d =>
      commutatorKernel d s (fun x => gradient (propagatorW C (mrrClamp t q.1) t φ) x) q.2.1 q.2.2 := by
  have hgr : Measurable (rieszKernelGrad d s) := by
    unfold rieszKernelGrad gradient
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.measurable.comp (measurable_fderiv ℝ _)
  have hv : Measurable fun p : ℝ × Euc d => gradient (propagatorW C (mrrClamp t p.1) t φ) p.2 := by
    have e : (fun p : ℝ × Euc d => gradient (propagatorW C (mrrClamp t p.1) t φ) p.2) =
        fun p => (WithLp.toLp 2 fun a => gradComp a (propagatorW C (mrrClamp t p.1) t φ) p.2 : Euc d) := by
      funext p; ext a; rfl
    rw [e]
    exact (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.2 fun a => s105_grad_meas C ht hcl a)
  have h1 : Measurable fun q : ℝ × Euc d × Euc d => gradient (propagatorW C (mrrClamp t q.1) t φ) q.2.1 :=
    hv.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have h2 : Measurable fun q : ℝ × Euc d × Euc d => gradient (propagatorW C (mrrClamp t q.1) t φ) q.2.2 :=
    hv.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have h3 : Measurable fun q : ℝ × Euc d × Euc d => rieszKernelGrad d s (q.2.1 - q.2.2) :=
    hgr.comp ((measurable_fst.comp measurable_snd).sub (measurable_snd.comp measurable_snd))
  exact (h1.sub h2).inner h3

set_option maxHeartbeats 1600000 in
theorem s105_cpf_term2 (s : ℝ) (C : WholeCoeff d) {t : ℝ} (ht : 0 ≤ t) {φ : Euc d → ℝ}
    (hcl : IsClassicalAdjointW C t φ (fun r => propagatorW C r t φ)) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) {N : ℕ} (i : Fin N) :
    Measurable fun p : ℝ × EucConfig d N => ∫ y, commutatorKernel d s
      (fun x => gradient (propagatorW C (mrrClamp t p.1) t φ) x) (p.2 i) y ∂(HRS.Whole.withDensityReal ρ) := by
  have hK := s105_kernel_meas s C ht hcl
  have e : (fun p : ℝ × EucConfig d N => ∫ y, commutatorKernel d s
      (fun x => gradient (propagatorW C (mrrClamp t p.1) t φ) x) (p.2 i) y ∂(HRS.Whole.withDensityReal ρ)) =
      fun p => ∫ y, ρ y * commutatorKernel d s
        (fun x => gradient (propagatorW C (mrrClamp t p.1) t φ) x) (p.2 i) y := by
    funext p
    exact mrr_integral_withDensityReal ρ hρ.measurable hρ.nonneg (fun y => commutatorKernel d s
      (fun x => gradient (propagatorW C (mrrClamp t p.1) t φ) x) (p.2 i) y)
  rw [e]
  have hρs : Measurable fun q : (ℝ × EucConfig d N) × Euc d => ρ q.2 := hρ.measurable.comp measurable_snd
  have hmap : Measurable fun q : (ℝ × EucConfig d N) × Euc d => ((q.1.1, q.1.2 i, q.2) : ℝ × Euc d × Euc d) :=
    (measurable_fst.comp measurable_fst).prodMk
      (((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
  have hKq : Measurable fun q : (ℝ × EucConfig d N) × Euc d => commutatorKernel d s
      (fun x => gradient (propagatorW C (mrrClamp t q.1.1) t φ) x) (q.1.2 i) q.2 := by
    have hc := hK.comp hmap
    simpa only [Function.comp_def] using hc
  have hsm : StronglyMeasurable fun q : (ℝ × EucConfig d N) × Euc d => ρ q.2 * commutatorKernel d s
      (fun x => gradient (propagatorW C (mrrClamp t q.1.1) t φ) x) (q.1.2 i) q.2 :=
    (hρs.mul hKq).stronglyMeasurable
  exact (hsm.integral_prod_right' (ν := volume)).measurable

set_option maxHeartbeats 1600000 in
theorem s105_cpf_term3 (s : ℝ) (C : WholeCoeff d) {t : ℝ} (ht : 0 ≤ t) {φ : Euc d → ℝ}
    (hcl : IsClassicalAdjointW C t φ (fun r => propagatorW C r t φ)) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) :
    Measurable fun r : ℝ => ∫ x, ∫ y, commutatorKernel d s
      (fun z => gradient (propagatorW C (mrrClamp t r) t φ) z) x y ∂(HRS.Whole.withDensityReal ρ)
        ∂(HRS.Whole.withDensityReal ρ) := by
  have hK := s105_kernel_meas s C ht hcl
  have e : (fun r : ℝ => ∫ x, ∫ y, commutatorKernel d s
      (fun z => gradient (propagatorW C (mrrClamp t r) t φ) z) x y ∂(HRS.Whole.withDensityReal ρ)
        ∂(HRS.Whole.withDensityReal ρ)) =
      fun r => ∫ x, ρ x * ∫ y, ρ y * commutatorKernel d s
        (fun z => gradient (propagatorW C (mrrClamp t r) t φ) z) x y := by
    funext r
    rw [mrr_integral_withDensityReal ρ hρ.measurable hρ.nonneg (fun x => ∫ y, commutatorKernel d s
      (fun z => gradient (propagatorW C (mrrClamp t r) t φ) z) x y ∂(HRS.Whole.withDensityReal ρ))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ρ x * _ = ρ x * _
    rw [mrr_integral_withDensityReal ρ hρ.measurable hρ.nonneg (fun y => commutatorKernel d s
      (fun z => gradient (propagatorW C (mrrClamp t r) t φ) z) x y)]
  rw [e]
  have hρs : Measurable fun q : (ℝ × Euc d) × Euc d => ρ q.2 := hρ.measurable.comp measurable_snd
  have hmap : Measurable fun q : (ℝ × Euc d) × Euc d => ((q.1.1, q.1.2, q.2) : ℝ × Euc d × Euc d) :=
    (measurable_fst.comp measurable_fst).prodMk ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hKq : Measurable fun q : (ℝ × Euc d) × Euc d => commutatorKernel d s
      (fun z => gradient (propagatorW C (mrrClamp t q.1.1) t φ) z) q.1.2 q.2 := by
    have hc := hK.comp hmap
    simpa only [Function.comp_def] using hc
  have h2 : StronglyMeasurable (fun q : (ℝ × Euc d) × Euc d => ρ q.2 * commutatorKernel d s
      (fun z => gradient (propagatorW C (mrrClamp t q.1.1) t φ) z) q.1.2 q.2) := (hρs.mul hKq).stronglyMeasurable
  have h3 : StronglyMeasurable (fun q : ℝ × Euc d => ρ q.2 * ∫ y, ρ y * commutatorKernel d s
      (fun z => gradient (propagatorW C (mrrClamp t q.1) t φ) z) q.2 y) :=
    (hρ.measurable.comp measurable_snd).stronglyMeasurable.mul (h2.integral_prod_right' (ν := volume))
  exact (h3.integral_prod_right' (ν := volume)).measurable

set_option maxHeartbeats 1600000 in
theorem s105_force_meas (s : ℝ) (C : WholeCoeff d) {t : ℝ} (ht : 0 ≤ t) {φ : Euc d → ℝ}
    (hcl : IsClassicalAdjointW C t φ (fun r => propagatorW C r t φ)) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) {N : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ mΩ)
    (X : ℝ≥0 → Ω → EucConfig d N) (hprog : IsProgressive ℱ (ofNNRealTime X)) :
    Measurable (fun ζ => ∫ r in Set.Icc (0 : ℝ) t, centeredPairFunctional
      (commutatorKernel d s (fun x => gradient (propagatorW C r t φ) x)) (X (Real.toNNReal r) ζ)
      (HRS.Whole.withDensityReal ρ)) := by
  have hK := s105_kernel_meas s C ht hcl
  have hF : Measurable fun p : ℝ × EucConfig d N => centeredPairFunctional
      (commutatorKernel d s (fun x => gradient (propagatorW C (mrrClamp t p.1) t φ) x)) p.2
      (HRS.Whole.withDensityReal ρ) := by
    unfold centeredPairFunctional
    refine Measurable.add (Measurable.sub ?_ ?_) ?_
    · refine measurable_const.mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_)
      have hmap : Measurable fun p : ℝ × EucConfig d N => ((p.1, p.2 i, p.2 j) : ℝ × Euc d × Euc d) :=
        measurable_fst.prodMk (((measurable_pi_apply i).comp measurable_snd).prodMk
          ((measurable_pi_apply j).comp measurable_snd))
      have hc := hK.comp hmap
      simpa only [Function.comp_def] using hc
    · exact measurable_const.mul (measurable_const.mul (Finset.measurable_sum _ fun i _ =>
        s105_cpf_term2 s C ht hcl hρ i))
    · exact (s105_cpf_term3 s C ht hcl hρ).comp measurable_fst
  have hX := mrr_prog_meas ℱ X hprog ht
  have hG : Measurable fun p : Ω × ℝ => centeredPairFunctional
      (commutatorKernel d s (fun x => gradient (propagatorW C (mrrClamp t p.2) t φ) x))
      (X (Real.toNNReal (mrrClamp t p.2)) p.1) (HRS.Whole.withDensityReal ρ) := by
    have hc := hF.comp (measurable_snd.prodMk (hX.comp measurable_swap))
    simpa only [Function.comp_def, Prod.fst_swap, Prod.snd_swap] using hc
  have e : (fun ζ : Ω => ∫ r in Set.Icc (0 : ℝ) t, centeredPairFunctional
      (commutatorKernel d s (fun x => gradient (propagatorW C r t φ) x)) (X (Real.toNNReal r) ζ)
      (HRS.Whole.withDensityReal ρ)) = fun ζ => ∫ r in Set.Icc (0 : ℝ) t, centeredPairFunctional
      (commutatorKernel d s (fun x => gradient (propagatorW C (mrrClamp t r) t φ) x))
      (X (Real.toNNReal (mrrClamp t r)) ζ) (HRS.Whole.withDensityReal ρ) := by
    funext ζ
    exact setIntegral_congr_fun measurableSet_Icc (fun r hr => by simp only [mrrClamp_of_mem hr])
  rw [e]
  exact (hG.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) t))).measurable

end HRS.MS.R2GenInit
