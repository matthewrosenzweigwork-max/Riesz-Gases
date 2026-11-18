import HRS.MC.S7PIDefs

/-!
# Packet piS3, part 4: `s7_PIH_heat_cont` (joint continuity of the finite-dimensional heat function)
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace HRS.MC.Sec7.S7PIS3

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI

variable {d : ℕ}

/-- Bound of the derivatives of a `C_b^k` function. -/
theorem S7PIS3_cb_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {G : E → ℝ} {k : ℕ}
    (hG : MemCb k G) {j : ℕ} (hj : j ≤ k) (x : E) :
    ‖iteratedFDeriv ℝ j G x‖ ≤ ⨆ z, ‖iteratedFDeriv ℝ j G z‖ :=
  le_ciSup (f := fun z => ‖iteratedFDeriv ℝ j G z‖) (hG.2 j hj) x

/-- Differentiation under the integral sign for a probability measure on `ℝ^q`. -/
theorem S7PIS3_heat_deriv {q : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin q))) [IsProbabilityMeasure ν]
    {G : EuclideanSpace ℝ (Fin q) → ℝ} {k : ℕ} (hG : MemCb k G) {j : ℕ} (hj : j ≤ k)
    (c : EuclideanSpace ℝ (Fin q)) :
    iteratedFDeriv ℝ j (fun y => ∫ x, G (y + x) ∂ν) c = ∫ x, iteratedFDeriv ℝ j G (c + x) ∂ν := by
  have hGc : ∀ m : ℕ, m ≤ k → Continuous (iteratedFDeriv ℝ m G) := fun m hm =>
    hG.1.continuous_iteratedFDeriv (by exact_mod_cast hm)
  rcases Nat.eq_zero_or_pos j with h0 | h0
  · subst h0
    have hint : Integrable (fun x => G (c + x)) ν := by
      refine Integrable.of_bound (C := ⨆ z, ‖iteratedFDeriv ℝ 0 G z‖) ?_ ?_
      · have : Continuous G := by simpa using hG.1.continuous
        exact (this.comp (by fun_prop : Continuous fun z => c + z)).aestronglyMeasurable
      · refine Filter.Eventually.of_forall fun x => ?_
        have := S7PIS3_cb_bound hG (j := 0) (Nat.zero_le _) (c + x)
        simpa using this
    have e1 : iteratedFDeriv ℝ 0 (fun y => ∫ x, G (y + x) ∂ν) c =
        (continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin q)) ℝ).symm (∫ x, G (c + x) ∂ν) := by
      rw [iteratedFDeriv_zero_eq_comp]; rfl
    rw [e1]
    have := ContinuousLinearEquiv.integral_comp_comm (μ := ν)
      (continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin q)) ℝ).symm.toContinuousLinearEquiv
      (fun x => G (c + x))
    refine this.symm.trans ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [iteratedFDeriv_zero_eq_comp]
  · have hcd : ∀ z : EuclideanSpace ℝ (Fin q), ContDiff ℝ ((j : ℕ) : WithTop ℕ∞) (fun y => G (y + z)) :=
      fun z => by
        have := (hG.1.of_le (by exact_mod_cast hj : ((j : ℕ) : WithTop ℕ∞) ≤ k)).comp
          (contDiff_id.add (contDiff_const (c := z)))
        simpa [Function.comp_def] using this
    have key := contDiff_integral_dominated (B := EuclideanSpace ℝ (Fin q)) ν
      (fun z y => G (y + z)) j h0 hcd
      (fun x => by
        have hGcont : Continuous G := by simpa using hG.1.continuous
        refine Integrable.of_bound (C := ⨆ z, ‖iteratedFDeriv ℝ 0 G z‖) ?_ ?_
        · exact (hGcont.comp (by fun_prop : Continuous fun z => x + z)).aestronglyMeasurable
        · refine Filter.Eventually.of_forall fun z => ?_
          have := S7PIS3_cb_bound hG (j := 0) (Nat.zero_le _) (x + z)
          simpa using this)
      (fun m hm x => by
        have h : (fun z => iteratedFDeriv ℝ m (fun y => G (y + z)) x) =
            fun z => iteratedFDeriv ℝ m G (x + z) := by
          funext z; exact iteratedFDeriv_comp_add_right m z x
        rw [h]
        exact ((hGc m (hm.trans hj)).comp (by fun_prop : Continuous fun z => x + z)).aestronglyMeasurable)
      (fun m _ => ⨆ z, ‖iteratedFDeriv ℝ m G z‖) (fun m _ _ => integrable_const _)
      (fun m _ hmj z x => by
        rw [iteratedFDeriv_comp_add_right]
        exact S7PIS3_cb_bound hG (hmj.trans hj) _)
    have e := key.2 j le_rfl c
    simp_rw [iteratedFDeriv_comp_add_right] at e
    exact e

/-- Continuity in `(u, c)` of a Gaussian average of a bounded continuous function, for a covariance
depending continuously on `u` (through the continuity of the PSD square root). -/
theorem S7PIS3_gauss_cont {q : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (T : ℝ)
    (S : ℝ → Matrix (Fin q) (Fin q) ℝ)
    (hS : ∀ i j, ContinuousOn (fun u => S u i j) (Set.Icc 0 T))
    (hSpsd : ∀ u ∈ Set.Icc 0 T, (S u).PosSemidef)
    {H : EuclideanSpace ℝ (Fin q) → X} (hH : Continuous H) {C : ℝ} (hC : ∀ x, ‖H x‖ ≤ C) :
    ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin q) =>
      ∫ x, H (p.2 + x) ∂(multivariateGaussian 0 (S p.1))) (Set.Icc 0 T ×ˢ Set.univ) := by
  have hSmat : ContinuousOn S (Set.Icc 0 T) :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => hS i j
  have hsq : ContinuousOn (fun u => CFC.sqrt (S u)) (Set.Icc 0 T) :=
    CFC.continuousOn_sqrt.comp hSmat (fun u hu => (hSpsd u hu).nonneg)
  have hmap : ∀ p : ℝ × EuclideanSpace ℝ (Fin q), ∫ x, H (p.2 + x) ∂(multivariateGaussian 0 (S p.1)) =
      ∫ z, H (p.2 + (0 + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (S p.1)) z))
        ∂(stdGaussian (EuclideanSpace ℝ (Fin q))) := by
    intro p
    unfold multivariateGaussian
    have hφ : Measurable fun x : EuclideanSpace ℝ (Fin q) =>
        (0 : EuclideanSpace ℝ (Fin q)) + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (S p.1)) x := by
      fun_prop
    exact integral_map (φ := fun x : EuclideanSpace ℝ (Fin q) =>
        (0 : EuclideanSpace ℝ (Fin q)) + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (S p.1)) x)
      (f := fun x => H (p.2 + x)) hφ.aemeasurable
      (hH.comp (by fun_prop : Continuous fun x : EuclideanSpace ℝ (Fin q) => p.2 + x)).aestronglyMeasurable
  simp_rw [hmap]
  refine continuousOn_of_dominated (bound := fun _ => C) ?_ ?_ (integrable_const _) ?_
  · intro p _
    exact (hH.comp (by fun_prop)).aestronglyMeasurable
  · intro p _
    exact Filter.Eventually.of_forall fun z => hC _
  · refine Filter.Eventually.of_forall fun z => ?_
    refine hH.continuousOn.comp ?_ (Set.mapsTo_univ _ _)
    refine (continuous_snd.continuousOn).add ?_
    simp only [zero_add]
    have h1 : ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin q) => CFC.sqrt (S p.1))
        (Set.Icc 0 T ×ˢ Set.univ) :=
      hsq.comp continuousOn_fst (fun p hp => hp.1)
    have hlin : Continuous (fun B : Matrix (Fin q) (Fin q) ℝ => Matrix.toEuclideanCLM (𝕜 := ℝ) B) :=
      LinearMap.continuous_of_finiteDimensional
        ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin q)).toAlgEquiv.toLinearMap)
    have h3 : Continuous (fun B : Matrix (Fin q) (Fin q) ℝ => Matrix.toEuclideanCLM (𝕜 := ℝ) B z) :=
      (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin q)) z).continuous.comp hlin
    exact h3.comp_continuousOn h1

theorem s7_PIH_heat_cont_proof {q : ℕ} (T : ℝ) (S : ℝ → Matrix (Fin q) (Fin q) ℝ)
    (hS : ∀ i j, ContinuousOn (fun u => S u i j) (Set.Icc 0 T)) (hSpsd : ∀ u ∈ Set.Icc 0 T, (S u).PosSemidef)
    (G : EuclideanSpace ℝ (Fin q) → ℝ) (k : ℕ) (hG : MemCb k G) (j : ℕ) (hj : j ≤ k) :
    ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin q) => iteratedFDeriv ℝ j (gaussHeat S G p.1) p.2)
      (Set.Icc 0 T ×ˢ Set.univ) := by
  have hH : Continuous (iteratedFDeriv ℝ j G) := hG.1.continuous_iteratedFDeriv (by exact_mod_cast hj)
  refine (S7PIS3_gauss_cont T S hS hSpsd hH (C := ⨆ z, ‖iteratedFDeriv ℝ j G z‖)
    (fun x => S7PIS3_cb_bound hG hj x)).congr ?_
  intro p _
  exact S7PIS3_heat_deriv (multivariateGaussian 0 (S p.1)) hG hj p.2

end HRS.MC.Sec7.S7PIS3

end
