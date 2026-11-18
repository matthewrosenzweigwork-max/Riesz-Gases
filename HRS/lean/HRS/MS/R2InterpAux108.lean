import HRS.MS.R2InterpAux107

/-!
# S10.2 (worker S10R), part 108 (packet M2d): `R2JIntegrandMeas` for `η_N` along a continuous particle path
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}

theorem s102_gradient_sum {ι : Type*} (S : Finset ι) (c : ι → ℝ) (g : ι → Euc d → ℝ)
    (hg : ∀ i ∈ S, Differentiable ℝ (g i)) (x : Euc d) :
    gradient (fun y => ∑ i ∈ S, c i * g i y) x = ∑ i ∈ S, c i • gradient (g i) x := by
  have hd : HasFDerivAt (fun y => ∑ i ∈ S, c i * g i y) (∑ i ∈ S, c i • fderiv ℝ (g i) x) x := by
    refine HasFDerivAt.fun_sum (fun i hi => ?_)
    exact ((hg i hi x).hasFDerivAt.const_mul (c i))
  unfold gradient
  rw [hd.fderiv, map_sum]
  simp [map_smul]

theorem s102_prop_sum (hlin : S102Lin C m T) {u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) (htT : t ≤ T)
    (S : Finset (MultiIndex d)) (cc : MultiIndex d → ℝ) :
    propagatorW C u t (fun x => ∑ α ∈ S, cc α * oscTestFun m α x) =
      fun x => ∑ α ∈ S, cc α * propagatorW C u t (oscTestFun m α) x := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact s102_U_zero hlin hu hut htT
  | insert a S ha ih =>
    have h := hlin u t hu hut htT (fun x => ∑ α ∈ S, cc α * oscTestFun m α x) (oscTestFun m a) (cc a)
      ⟨S, cc, rfl⟩ (s102_isCombo_osc m a)
    have e : (fun x => ∑ α ∈ insert a S, cc α * oscTestFun m α x) =
        (fun x => ∑ α ∈ S, cc α * oscTestFun m α x) + cc a • oscTestFun m a := by
      funext x
      simp only [Finset.sum_insert ha, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e, h, ih]
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_insert ha]
    ring

/-- The gradient of the propagated combination, as a joint function of `(u,x)`. -/
theorem s102_grad_comb (hS : S102Std C m T r c) (hlin : S102Lin C m T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (Sa : Finset (MultiIndex d)) (ca : MultiIndex d → ℝ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) t) (x : Euc d) :
    gradient (propagatorW C u t (fun y => ∑ α ∈ Sa, ca α * oscTestFun m α y)) x =
      ∑ α ∈ Sa, ca α • (if u ∈ Icc (0 : ℝ) t then gradient (propagatorW C u t (oscTestFun m α)) x else 0) := by
  rw [s102_prop_sum hlin hu.1 hu.2 ht.2 Sa ca, s102_gradient_sum Sa ca]
  · refine Finset.sum_congr rfl fun α _ => ?_
    rw [if_pos hu]
  · intro α _
    exact ((s102_propagator_classical (hS.hcls α t ht)).c2 u hu).differentiable (by norm_num)

theorem s102_eta_JMeas (hS : S102Std C m T r c) (hlin : S102Lin C m T) {N : ℕ} (hN : 0 < N) {Ω : Type}
    (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (X : ℝ≥0 → Ω → EucConfig d N) (ζ : Ω)
    (hcz : ∀ k, Continuous fun t : ℝ≥0 => X t ζ k) : R2JIntegrandMeas C m T (s102_etaf μ X ζ) := by
  intro ta tb φa φb ⟨Sa, ca, hφa⟩ ⟨Sb, cb, hφb⟩ hta htb
  subst hφa hφb
  set G : ℝ × Euc d → ℝ := fun p => inner ℝ
    (∑ α ∈ Sa, ca α • (if p.1 ∈ Icc (0 : ℝ) ta then gradient (propagatorW C p.1 ta (oscTestFun m α)) p.2 else 0))
    (∑ α ∈ Sb, cb α • (if p.1 ∈ Icc (0 : ℝ) tb then gradient (propagatorW C p.1 tb (oscTestFun m α)) p.2 else 0))
    with hG
  have hGm : Measurable G := by
    refine Measurable.inner ?_ ?_
    · refine Finset.measurable_sum _ fun α _ => ?_
      exact (s102_gradJoint_meas (s102_propagator_classical (hS.hcls α ta hta))).const_smul (ca α)
    · refine Finset.measurable_sum _ fun α _ => ?_
      exact (s102_gradJoint_meas (s102_propagator_classical (hS.hcls α tb htb))).const_smul (cb α)
  set F : ℝ → ℝ := fun u => Real.sqrt N * ((N : ℝ)⁻¹ * ∑ k, G (u, X u.toNNReal ζ k) - ∫ x, G (u, x) ∂μ) with hF
  have hFm : Measurable F := by
    refine (((measurable_const.mul (Finset.measurable_sum _ fun k _ => ?_)).sub ?_)).const_mul _
    · exact hGm.comp (measurable_id.prodMk (((hcz k).comp continuous_real_toNNReal).measurable))
    · exact (hGm.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable
  refine hFm.aemeasurable.congr ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun u hu => ?_)
  have hua : u ∈ Icc (0 : ℝ) ta := ⟨hu.1, hu.2.trans (min_le_left _ _)⟩
  have hub : u ∈ Icc (0 : ℝ) tb := ⟨hu.1, hu.2.trans (min_le_right _ _)⟩
  have hg : (fun x => inner ℝ (gradient (propagatorW C u ta (fun y => ∑ α ∈ Sa, ca α * oscTestFun m α y)) x)
      (gradient (propagatorW C u tb (fun y => ∑ α ∈ Sb, cb α * oscTestFun m α y)) x)) = fun x => G (u, x) := by
    funext x
    simp only [hG]
    rw [s102_grad_comb hS hlin hta Sa ca hua x, s102_grad_comb hS hlin htb Sb cb hub x]
  show F u = _
  simp only [hF, s102_etaf, HRS.Whole.pair_empirical hN, hg]
  rfl

end HRS.MS.R2Interp

end
