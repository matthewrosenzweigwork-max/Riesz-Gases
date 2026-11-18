import HRS.Stochastic.Brownian
import HRS.MS.S82P2Mom

/-!
# S8.2 observed-time layer, packet T8A.V02a: deterministic time scaling of finite Brownian coordinates

If `W` is a Brownian filtration with `F`, then `W'_t = β^(-1/2) W_{βt}` (after reindexing the coordinates by
`e : I ≃ J`) is a Brownian filtration for `F'_t = F_{βt}`: the filtration, adaptedness, completeness, continuity,
independence of increments and Gaussian increments all transfer, the Gaussian law by the scaling of `gaussianReal`
and the reindexing of the product measure.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A

/-- scaling and reindexing of a coordinate map is measurable for any σ-algebra on the domain -/
theorem r26t8a_v02a_meas {Omega : Type*} {m : MeasurableSpace Omega} {I J : Type*} [Fintype I]
    [Fintype J] (e : I ≃ J) (c : ℝ) (f : Omega → I → ℝ) (hf : Measurable[m] f) :
    Measurable[m] (fun w (j : J) => c * f w (e.symm j)) :=
  measurable_pi_iff.mpr fun j => measurable_const.mul ((measurable_pi_apply (e.symm j)).comp hf)

/-- the scaled and reindexed product Gaussian is the product Gaussian with the rescaled variance -/
theorem r26t8a_v02a_law {I J : Type*} [Fintype I] [Fintype J] (e : I ≃ J) (c : ℝ) (v w : NNReal)
    (hvw : (NNReal.mk (c ^ 2) (sq_nonneg c)) * v = w) :
    (Measure.pi fun _ : I => gaussianReal 0 v).map (fun x : I → ℝ => fun j : J => c * x (e.symm j)) =
      Measure.pi fun _ : J => gaussianReal 0 w := by
  have hS : Measurable (fun x : I → ℝ => fun i : I => c * x i) :=
    measurable_pi_iff.mpr fun i => measurable_const.mul (measurable_pi_apply i)
  have hpc : Measurable (MeasurableEquiv.piCongrLeft (fun _ : J => ℝ) e) :=
    (MeasurableEquiv.piCongrLeft (fun _ : J => ℝ) e).measurable
  have hfun : (fun x : I → ℝ => fun j : J => c * x (e.symm j)) =
      (MeasurableEquiv.piCongrLeft (fun _ : J => ℝ) e) ∘ (fun x : I → ℝ => fun i : I => c * x i) := by
    funext x j
    obtain ⟨i, rfl⟩ := e.surjective j
    simp only [Equiv.symm_apply_apply, Function.comp_apply]
    exact (MeasurableEquiv.piCongrLeft_apply_apply e (β := fun _ : J => ℝ) (fun i => c * x i) i).symm
  have hpi : (Measure.pi fun _ : I => gaussianReal 0 v).map (fun x : I → ℝ => fun i : I => c * x i) =
      Measure.pi fun _ : I => gaussianReal 0 w := by
    rw [Measure.pi_map_pi (f := fun _ : I => fun y : ℝ => c * y)
      (fun _ => (measurable_const.mul measurable_id).aemeasurable)]
    congr 1
    funext i
    rw [gaussianReal_map_const_mul, mul_zero, hvw]
  rw [hfun, ← Measure.map_map hpc hS, hpi]
  exact (measurePreserving_piCongrLeft (fun _ : J => gaussianReal 0 w) e).map_eq

theorem r26t8a_brownian_rescale {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {I J : Type*} [Fintype I] [Fintype J] (e : I ≃ J)
    (P : Measure Omega) [IsProbabilityMeasure P] (F : Filtration ℝ mOmega)
    (W : ℝ≥0 → Omega → I → ℝ) (hW : IsBrownianFiltration P F W)
    (beta : ℝ) (hbeta : 0 < beta) :
    ∃ F' : Filtration ℝ mOmega, (∀ t, F' t = F (beta * t)) ∧
      IsBrownianFiltration P F' (fun t w j => (Real.sqrt beta)⁻¹ * W (⟨beta, le_of_lt hbeta⟩ * t) w (e.symm j)) := by
  set bNN : NNReal := ⟨beta, le_of_lt hbeta⟩ with hbNN
  let F' : Filtration ℝ mOmega :=
    { seq := fun t => F (beta * t)
      mono' := fun s t h => F.mono (mul_le_mul_of_nonneg_left h hbeta.le)
      le' := fun t => F.le _ }
  have hcoe : ∀ t : NNReal, ((bNN * t : NNReal) : ℝ) = beta * t := fun t => by
    rw [NNReal.coe_mul]
    rfl
  refine ⟨F', fun t => rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t s hs hP
    exact hW.complete (beta * t) s hs hP
  · intro t
    have h := hW.adapted (bNN * t)
    rw [hcoe] at h
    change Measurable[F (beta * (t : ℝ))] _
    exact r26t8a_v02a_meas (m := F (beta * (t : ℝ))) e _ _ h
  · intro w
    funext j
    simp [hW.zero w]
  · intro w
    exact continuous_pi fun j => continuous_const.mul
      ((continuous_apply (e.symm j)).comp ((hW.cont w).comp (continuous_const.mul continuous_id)))
  · intro s t hst
    have hst' : bNN * s ≤ bNN * t := by gcongr
    have hI := hW.indep_incr (bNN * s) (bNN * t) hst'
    simp only [hcoe] at hI
    let T : (I → ℝ) → (J → ℝ) := fun x j => (Real.sqrt beta)⁻¹ * x (e.symm j)
    have hT : Measurable T := measurable_pi_iff.mpr fun j => measurable_const.mul (measurable_pi_apply _)
    have hD : Measurable (fun w => W (bNN * t) w - W (bNN * s) w) :=
      (hW.measurable (bNN * t)).sub (hW.measurable (bNN * s))
    have hle : MeasurableSpace.comap (fun w => T (W (bNN * t) w - W (bNN * s) w))
        (inferInstance : MeasurableSpace (J → ℝ)) ≤
        MeasurableSpace.comap (fun w => W (bNN * t) w - W (bNN * s) w)
          (inferInstance : MeasurableSpace (I → ℝ)) :=
      (hT.comp (comap_measurable _)).comap_le
    have hfun : (fun w => (fun j => (Real.sqrt beta)⁻¹ * W (bNN * t) w (e.symm j)) -
        (fun j => (Real.sqrt beta)⁻¹ * W (bNN * s) w (e.symm j))) =
        fun w => T (W (bNN * t) w - W (bNN * s) w) := by
      funext w j
      simp only [T, Pi.sub_apply]
      ring
    beta_reduce
    rw [hfun]
    exact indep_of_indep_of_le_left hI hle
  · intro s t hst
    have hst' : bNN * s ≤ bNN * t := by gcongr
    have hG := hW.gaussian_incr (bNN * s) (bNN * t) hst'
    have hvar : bNN * t - bNN * s = bNN * (t - s) := (mul_tsub _ _ _).symm
    rw [hvar] at hG
    have hvw : (NNReal.mk ((Real.sqrt beta)⁻¹ ^ 2) (sq_nonneg _)) * (bNN * (t - s)) = t - s := by
      apply NNReal.eq
      rw [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_mul, NNReal.coe_sub (by gcongr)]
      have hb : (bNN : ℝ) = beta := rfl
      rw [hb, inv_pow, Real.sq_sqrt hbeta.le]
      field_simp
    have hL : HasLaw (fun x : I → ℝ => fun j : J => (Real.sqrt beta)⁻¹ * x (e.symm j))
        (Measure.pi fun _ : J => gaussianReal 0 (t - s))
        (Measure.pi fun _ : I => gaussianReal 0 (bNN * (t - s))) :=
      ⟨(measurable_pi_iff.mpr fun j => measurable_const.mul (measurable_pi_apply _)).aemeasurable,
        r26t8a_v02a_law e _ _ _ hvw⟩
    have hc := hL.comp hG
    have hfun : (fun w => (fun j => (Real.sqrt beta)⁻¹ * W (bNN * t) w (e.symm j)) -
        (fun j => (Real.sqrt beta)⁻¹ * W (bNN * s) w (e.symm j))) =
        (fun x : I → ℝ => fun j : J => (Real.sqrt beta)⁻¹ * x (e.symm j)) ∘
          (fun w => W (bNN * t) w - W (bNN * s) w) := by
      funext w j
      simp only [Function.comp_apply, Pi.sub_apply]
      ring
    beta_reduce
    rw [hfun]
    exact hc

end HRS.MS.R26T8A

end
