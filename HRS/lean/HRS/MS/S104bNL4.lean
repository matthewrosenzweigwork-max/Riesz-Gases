import HRS.MS.S104bNL3

/-!
# S10.5 (nonlinear), packet S104b-NL4: measurability of the moving-reference commutator forcing integral

Moving analogue of `s105_force_meas` (R2GenInitAux38): for a classical adjoint orbit `U^{·,t}φ`, a moving density `ρ` with measurable clamped
joint dependence and a progressive particle path `X`, `ζ ↦ ∫_0^t centeredPairFunctional (commutatorKernel (∇U^{r,t}φ)) (X_r ζ) (ρ_r dx) dr` is measurable.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S104b

open HRS HRS.Whole HRS.MP.RdRem HRS.MS.GenPath HRS.MS.R2GenInit

variable {d : ℕ}

set_option maxHeartbeats 1600000 in
theorem s104b_cpf_term2 (s : ℝ) (C : WholeCoeff d) {t : ℝ} (ht : 0 ≤ t) {φ : Euc d → ℝ}
    (hcl : IsClassicalAdjointW C t φ (fun r => propagatorW C r t φ)) {ρc : ℝ → Euc d → ℝ}
    (hρ : ∀ r, HRS.Whole.IsProbDensity (ρc r)) (hρm : Measurable fun p : ℝ × Euc d => ρc p.1 p.2)
    {N : ℕ} (i : Fin N) :
    Measurable fun p : ℝ × EucConfig d N => ∫ y, commutatorKernel d s
      (fun x => gradient (propagatorW C (mrrClamp t p.1) t φ) x) (p.2 i) y ∂(HRS.Whole.withDensityReal (ρc p.1)) := by
  have hK := s105_kernel_meas s C ht hcl
  have e : (fun p : ℝ × EucConfig d N => ∫ y, commutatorKernel d s
      (fun x => gradient (propagatorW C (mrrClamp t p.1) t φ) x) (p.2 i) y ∂(HRS.Whole.withDensityReal (ρc p.1))) =
      fun p => ∫ y, ρc p.1 y * commutatorKernel d s
        (fun x => gradient (propagatorW C (mrrClamp t p.1) t φ) x) (p.2 i) y := by
    funext p
    exact mrr_integral_withDensityReal (ρc p.1) (hρ p.1).measurable (hρ p.1).nonneg (fun y => commutatorKernel d s
      (fun x => gradient (propagatorW C (mrrClamp t p.1) t φ) x) (p.2 i) y)
  rw [e]
  have hρs : Measurable fun q : (ℝ × EucConfig d N) × Euc d => ρc q.1.1 q.2 :=
    hρm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hmap : Measurable fun q : (ℝ × EucConfig d N) × Euc d => ((q.1.1, q.1.2 i, q.2) : ℝ × Euc d × Euc d) :=
    (measurable_fst.comp measurable_fst).prodMk
      (((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
  have hKq : Measurable fun q : (ℝ × EucConfig d N) × Euc d => commutatorKernel d s
      (fun x => gradient (propagatorW C (mrrClamp t q.1.1) t φ) x) (q.1.2 i) q.2 := by
    have hc := hK.comp hmap
    simpa only [Function.comp_def] using hc
  have hsm : StronglyMeasurable fun q : (ℝ × EucConfig d N) × Euc d => ρc q.1.1 q.2 * commutatorKernel d s
      (fun x => gradient (propagatorW C (mrrClamp t q.1.1) t φ) x) (q.1.2 i) q.2 :=
    (hρs.mul hKq).stronglyMeasurable
  exact (hsm.integral_prod_right' (ν := volume)).measurable

set_option maxHeartbeats 1600000 in
theorem s104b_cpf_term3 (s : ℝ) (C : WholeCoeff d) {t : ℝ} (ht : 0 ≤ t) {φ : Euc d → ℝ}
    (hcl : IsClassicalAdjointW C t φ (fun r => propagatorW C r t φ)) {ρc : ℝ → Euc d → ℝ}
    (hρ : ∀ r, HRS.Whole.IsProbDensity (ρc r)) (hρm : Measurable fun p : ℝ × Euc d => ρc p.1 p.2) :
    Measurable fun r : ℝ => ∫ x, ∫ y, commutatorKernel d s
      (fun z => gradient (propagatorW C (mrrClamp t r) t φ) z) x y ∂(HRS.Whole.withDensityReal (ρc r))
        ∂(HRS.Whole.withDensityReal (ρc r)) := by
  have hK := s105_kernel_meas s C ht hcl
  have e : (fun r : ℝ => ∫ x, ∫ y, commutatorKernel d s
      (fun z => gradient (propagatorW C (mrrClamp t r) t φ) z) x y ∂(HRS.Whole.withDensityReal (ρc r))
        ∂(HRS.Whole.withDensityReal (ρc r))) =
      fun r => ∫ x, ρc r x * ∫ y, ρc r y * commutatorKernel d s
        (fun z => gradient (propagatorW C (mrrClamp t r) t φ) z) x y := by
    funext r
    rw [mrr_integral_withDensityReal (ρc r) (hρ r).measurable (hρ r).nonneg (fun x => ∫ y, commutatorKernel d s
      (fun z => gradient (propagatorW C (mrrClamp t r) t φ) z) x y ∂(HRS.Whole.withDensityReal (ρc r)))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ρc r x * _ = ρc r x * _
    rw [mrr_integral_withDensityReal (ρc r) (hρ r).measurable (hρ r).nonneg (fun y => commutatorKernel d s
      (fun z => gradient (propagatorW C (mrrClamp t r) t φ) z) x y)]
  rw [e]
  have hρs : Measurable fun q : (ℝ × Euc d) × Euc d => ρc q.1.1 q.2 :=
    hρm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hmap : Measurable fun q : (ℝ × Euc d) × Euc d => ((q.1.1, q.1.2, q.2) : ℝ × Euc d × Euc d) :=
    (measurable_fst.comp measurable_fst).prodMk ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hKq : Measurable fun q : (ℝ × Euc d) × Euc d => commutatorKernel d s
      (fun z => gradient (propagatorW C (mrrClamp t q.1.1) t φ) z) q.1.2 q.2 := by
    have hc := hK.comp hmap
    simpa only [Function.comp_def] using hc
  have h2 : StronglyMeasurable (fun q : (ℝ × Euc d) × Euc d => ρc q.1.1 q.2 * commutatorKernel d s
      (fun z => gradient (propagatorW C (mrrClamp t q.1.1) t φ) z) q.1.2 q.2) := (hρs.mul hKq).stronglyMeasurable
  have h3 : StronglyMeasurable (fun q : ℝ × Euc d => ρc q.1 q.2 * ∫ y, ρc q.1 y * commutatorKernel d s
      (fun z => gradient (propagatorW C (mrrClamp t q.1) t φ) z) q.2 y) :=
    hρm.stronglyMeasurable.mul (h2.integral_prod_right' (ν := volume))
  exact (h3.integral_prod_right' (ν := volume)).measurable

set_option maxHeartbeats 1600000 in
theorem s104b_force_meas (s : ℝ) (C : WholeCoeff d) {t : ℝ} (ht : 0 ≤ t) {φ : Euc d → ℝ}
    (hcl : IsClassicalAdjointW C t φ (fun r => propagatorW C r t φ)) {ρ : ℝ → Euc d → ℝ}
    (hρ : ∀ r ∈ Set.Icc (0 : ℝ) t, HRS.Whole.IsProbDensity (ρ r))
    (hρm : Measurable fun p : ℝ × Euc d => ρ (mrrClamp t p.1) p.2) {N : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (ℱ : Filtration ℝ mΩ) (X : ℝ≥0 → Ω → EucConfig d N) (hprog : IsProgressive ℱ (ofNNRealTime X)) :
    Measurable (fun ζ => ∫ r in Set.Icc (0 : ℝ) t, centeredPairFunctional
      (commutatorKernel d s (fun x => gradient (propagatorW C r t φ) x)) (X (Real.toNNReal r) ζ)
      (HRS.Whole.withDensityReal (ρ r))) := by
  have hK := s105_kernel_meas s C ht hcl
  have hρc : ∀ r, HRS.Whole.IsProbDensity (ρ (mrrClamp t r)) := fun r => hρ _ (mrrClamp_mem ht r)
  have hF : Measurable fun p : ℝ × EucConfig d N => centeredPairFunctional
      (commutatorKernel d s (fun x => gradient (propagatorW C (mrrClamp t p.1) t φ) x)) p.2
      (HRS.Whole.withDensityReal (ρ (mrrClamp t p.1))) := by
    unfold centeredPairFunctional
    refine Measurable.add (Measurable.sub ?_ ?_) ?_
    · refine measurable_const.mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_)
      have hmap : Measurable fun p : ℝ × EucConfig d N => ((p.1, p.2 i, p.2 j) : ℝ × Euc d × Euc d) :=
        measurable_fst.prodMk (((measurable_pi_apply i).comp measurable_snd).prodMk
          ((measurable_pi_apply j).comp measurable_snd))
      have hc := hK.comp hmap
      simpa only [Function.comp_def] using hc
    · exact measurable_const.mul (measurable_const.mul (Finset.measurable_sum _ fun i _ =>
        s104b_cpf_term2 s C ht hcl (ρc := fun r => ρ (mrrClamp t r)) hρc hρm i))
    · exact (s104b_cpf_term3 s C ht hcl (ρc := fun r => ρ (mrrClamp t r)) hρc hρm).comp measurable_fst
  have hX := mrr_prog_meas ℱ X hprog ht
  have hG : Measurable fun p : Ω × ℝ => centeredPairFunctional
      (commutatorKernel d s (fun x => gradient (propagatorW C (mrrClamp t p.2) t φ) x))
      (X (Real.toNNReal (mrrClamp t p.2)) p.1) (HRS.Whole.withDensityReal (ρ (mrrClamp t p.2))) := by
    have hc := hF.comp (measurable_snd.prodMk (hX.comp measurable_swap))
    simpa only [Function.comp_def, Prod.fst_swap, Prod.snd_swap] using hc
  have e : (fun ζ : Ω => ∫ r in Set.Icc (0 : ℝ) t, centeredPairFunctional
      (commutatorKernel d s (fun x => gradient (propagatorW C r t φ) x)) (X (Real.toNNReal r) ζ)
      (HRS.Whole.withDensityReal (ρ r))) = fun ζ => ∫ r in Set.Icc (0 : ℝ) t, centeredPairFunctional
      (commutatorKernel d s (fun x => gradient (propagatorW C (mrrClamp t r) t φ) x))
      (X (Real.toNNReal (mrrClamp t r)) ζ) (HRS.Whole.withDensityReal (ρ (mrrClamp t r))) := by
    funext ζ
    exact setIntegral_congr_fun measurableSet_Icc (fun r hr => by simp only [mrrClamp_of_mem hr])
  rw [e]
  exact (hG.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) t))).measurable

end HRS.MS.S104b
