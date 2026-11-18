import HRS.MS.R2InterpAux8
import HRS.MS.CovMeasAux4

/-!
# S10.2 (worker S102), part 9: derivative bounds for differences of the orbits in the terminal time

From `S101Data` (the unpacked `R2OrbitSummable`): for `0 ≤ u ≤ t' ≤ t ≤ T` and `j ≤ r+1`,
`‖D^j(U^{u,t}φ_α - U^{u,t'}φ_α)(x)‖ ≤ c_α (t - t')`.  Route: `U^t - U^{t'} = ∫_{t'}^t ∂_sU ds` (S10.1 `s101_ftc`) and differentiation under
the integral sign (`HRS.contDiff_integral_dominated`); the parameter measurability of the iterated derivatives is Lemma A/B below.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas

variable {d : ℕ}

/-- The coordinate expansion `A = ∑_i (proj_i).smulRight (A e_i)` of a linear map out of `ℝ^d`. -/
def s102_expand {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Fin d → F) : Euc d →L[ℝ] F :=
  ∑ i, (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).smulRight (f i)

theorem s102_expand_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (A : Euc d →L[ℝ] F) :
    s102_expand (fun i => A (EuclideanSpace.single i (1 : ℝ))) = A := by
  ext v
  have hv : v = ∑ i, v i • EuclideanSpace.single i (1 : ℝ) := by
    have := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v
    simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] at this
    exact this.symm
  conv_rhs => rw [hv]
  simp [s102_expand, map_sum, map_smul]

/-- Lemma A: a.e.-measurability in the parameter of the Fréchet derivative. -/
theorem s102_aesm_fderiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (μ : Measure ℝ) (G : ℝ → Euc d → F)
    (hG : ∀ y, AEStronglyMeasurable (fun s => G s y) μ) (x : Euc d)
    (hd : ∀ s, DifferentiableAt ℝ (G s) x) :
    AEStronglyMeasurable (fun s => fderiv ℝ (G s) x) μ := by
  have hcol : ∀ i : Fin d, AEStronglyMeasurable
      (fun s => fderiv ℝ (G s) x (EuclideanSpace.single i (1 : ℝ))) μ := by
    intro i
    refine aestronglyMeasurable_of_tendsto_ae (atTop : Filter ℕ)
      (f := fun (n : ℕ) (s : ℝ) => ((1 : ℝ) / ((n : ℝ) + 1))⁻¹ •
        (G s (x + ((1 : ℝ) / ((n : ℝ) + 1)) • EuclideanSpace.single i (1 : ℝ)) - G s x)) ?_ ?_
    · intro n
      exact ((hG _).sub (hG x)).const_smul _
    · refine Filter.Eventually.of_forall fun s => ?_
      have h1 : HasDerivAt (fun t : ℝ => G s (x + t • EuclideanSpace.single i (1 : ℝ)))
          (fderiv ℝ (G s) x (EuclideanSpace.single i (1 : ℝ))) 0 := by
        have h2 : HasDerivAt (fun t : ℝ => x + t • EuclideanSpace.single i (1 : ℝ))
            (EuclideanSpace.single i (1 : ℝ)) 0 := by
          simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single i (1 : ℝ))).const_add x
        have h3 : HasFDerivAt (G s) (fderiv ℝ (G s) x) (x + (0 : ℝ) • EuclideanSpace.single i (1 : ℝ)) := by
          simpa using (hd s).hasFDerivAt
        exact h3.comp_hasDerivAt (0 : ℝ) h2
      have h4 := (hasDerivAt_iff_tendsto_slope_zero.1 h1)
      have h5 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝[≠] 0) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, Filter.Eventually.of_forall fun n => ?_⟩
        · simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
        · simp only [mem_compl_iff, mem_singleton_iff]
          positivity
      have h6 := h4.comp h5
      refine h6.congr fun n => ?_
      simp [Function.comp_def]
  have hsum : AEStronglyMeasurable (fun s => ∑ i : Fin d, (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).smulRight
      (fderiv ℝ (G s) x (EuclideanSpace.single i (1 : ℝ)))) μ := by
    refine Finset.aestronglyMeasurable_fun_sum (f := fun (i : Fin d) (s : ℝ) =>
      ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).smulRight
        (fderiv ℝ (G s) x (EuclideanSpace.single i (1 : ℝ))))) _ fun i _ => ?_
    have hc : Continuous (fun y : F => (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).smulRight y) :=
      (ContinuousLinearMap.smulRightL ℝ (Euc d) F (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)).continuous
    exact hc.comp_aestronglyMeasurable (hcol i)
  refine hsum.congr (Filter.Eventually.of_forall fun s => ?_)
  exact s102_expand_apply (fderiv ℝ (G s) x)

/-- Lemma B: a.e.-measurability in the parameter of the iterated derivatives. -/
theorem s102_aesm_iter (μ : Measure ℝ) (G : ℝ → Euc d → ℝ) (N : ℕ)
    (hc : ∀ s, ContDiff ℝ N (G s)) (hG : ∀ y, AEStronglyMeasurable (fun s => G s y) μ) :
    ∀ j ≤ N, ∀ x, AEStronglyMeasurable (fun s => iteratedFDeriv ℝ j (G s) x) μ := by
  intro j
  induction j with
  | zero =>
    intro _ x
    have : (fun s => iteratedFDeriv ℝ 0 (G s) x) =
        fun s => (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).symm (G s x) := by
      funext s; ext v; simp
    rw [this]
    exact (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).symm.continuous.comp_aestronglyMeasurable (hG x)
  | succ j ih =>
    intro hj x
    have ih' := ih (Nat.le_of_succ_le hj)
    have hd : ∀ s, DifferentiableAt ℝ (iteratedFDeriv ℝ j (G s)) x := fun s =>
      ((hc s).differentiable_iteratedFDeriv (m := j) (by exact_mod_cast hj)) x
    have hA := s102_aesm_fderiv μ (fun s => iteratedFDeriv ℝ j (G s)) ih' x hd
    have : (fun s => iteratedFDeriv ℝ (j + 1) (G s) x) =
        fun s => (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => Euc d) ℝ).symm
          (fderiv ℝ (iteratedFDeriv ℝ j (G s)) x) := by
      funext s
      rw [iteratedFDeriv_succ_eq_comp_left]
      rfl
    rw [this]
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => Euc d) ℝ).symm.continuous.comp_aestronglyMeasurable hA

/-- Interval integrability of the time-derivative slice. -/
theorem s102_th_intervalIntegrable {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}
    (hD : S101Data C m T r c) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) T) (α : MultiIndex d) (y : Euc d) {a b : ℝ}
    (hab : a ≤ b) : IntervalIntegrable (fun s => s101Th C m T u s α y) volume a b := by
  refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 ?_
  refine Measure.integrableOn_of_bounded (M := c α) (by simp) (s101_th_aesm hD hu α y) ?_
  exact Eventually.of_forall fun s => by
    rw [Real.norm_eq_abs]; exact s101_th_bound hD hu s α y

/-- **Terminal-time Lipschitz bound for the derivatives of the orbits.** -/
theorem s102_orbit_diff_bound {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}
    (hD : S101Data C m T r c) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) T) {t' t : ℝ} (ht' : t' ∈ Icc u T)
    (ht : t ∈ Icc u T) (htt : t' ≤ t) (α : MultiIndex d) (j : ℕ) (hj : j ≤ r + 1) (x : Euc d) :
    ‖iteratedFDeriv ℝ j (fun y => propagatorW C u t (oscTestFun m α) y -
      propagatorW C u t' (oscTestFun m α) y) x‖ ≤ c α * (t - t') := by
  have hfun : (fun y => propagatorW C u t (oscTestFun m α) y - propagatorW C u t' (oscTestFun m α) y) =
      fun y => ∫ s in Ioc t' t, s101Th C m T u s α y := by
    funext y
    have h1 := s101_ftc hD hu ht α y
    have h2 := s101_ftc hD hu ht' α y
    have h3 : (∫ s in u..t, s101Th C m T u s α y) - (∫ s in u..t', s101Th C m T u s α y) =
        ∫ s in t'..t, s101Th C m T u s α y :=
      intervalIntegral.integral_interval_sub_left (s102_th_intervalIntegrable hD hu α y ht.1)
        (s102_th_intervalIntegrable hD hu α y ht'.1)
    rw [intervalIntegral.integral_of_le htt] at h3
    rw [← h3, ← h1, ← h2]
    ring
  set ν : Measure ℝ := volume.restrict (Ioc t' t) with hν
  haveI : IsFiniteMeasure ν := ⟨by simp [hν]⟩
  set g : ℝ → Euc d → ℝ := fun s y => s101Th C m T u s α y with hg
  have hcd : ∀ s, ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) (g s) := fun s => (s101_th_slice hD hu s α).1
  have hmeas := s102_aesm_iter ν g (r + 1) hcd
    (fun y => (s101_th_aesm hD hu α y).mono_measure Measure.restrict_le_self)
  have key := HRS.contDiff_integral_dominated (B := Euc d) ν g (r + 1) (by omega) hcd
    (fun y => (s102_th_intervalIntegrable hD hu α y htt).1)
    hmeas (fun _ _ => c α) (fun _ _ _ => integrable_const _)
    (fun j _ hj _ y => (s101_th_slice hD hu _ α).2 j hj y)
  rw [hfun, (key.2 j hj x)]
  have hb : ∀ᵐ s ∂ν, ‖iteratedFDeriv ℝ j (g s) x‖ ≤ c α :=
    Filter.Eventually.of_forall fun s => (s101_th_slice hD hu s α).2 j hj x
  have := norm_integral_le_of_norm_le_const hb
  refine this.trans (le_of_eq ?_)
  simp [hν, Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.2 htt)]

end HRS.MS.R2Interp

end
