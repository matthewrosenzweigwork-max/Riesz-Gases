import HRS.MC.E214D3

/-!
# E214E1: helpers for the coupled pair: pull-back along a measure-preserving map, reindexing a Gaussian law

* `indepFun_comp_of_map`, `linSol_comp`: `IndepFun` / `IsLinearFluctuationSolution` are stable under pull-back
  along a map `π` with `P.map π = P'`.
* `map_reindex_multivariateGaussian`: the image of `multivariateGaussian 0 S` under the reindexing isometry is
  `multivariateGaussian 0 (S.submatrix f.symm f.symm)`.
* `crossNoiseCov_congr`: `crossNoiseCov` only sees the densities on `[0,∞)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace HRS.MC.E214E

open HRS HRS.Sec7

variable {d : ℕ}

theorem indepFun_comp_of_map {Ω Ω' α β : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace α] [MeasurableSpace β] {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] (π : Ω → Ω') (hπ : Measurable π) (hmap : P.map π = P')
    {f : Ω' → α} {g : Ω' → β} (hf : AEMeasurable f P') (hg : AEMeasurable g P') (h : IndepFun f g P') :
    IndepFun (f ∘ π) (g ∘ π) P := by
  haveI : IsProbabilityMeasure P' := hmap ▸ (inferInstance : IsProbabilityMeasure (P.map π))
  have hf' : AEMeasurable f (P.map π) := hmap ▸ hf
  have hg' : AEMeasurable g (P.map π) := hmap ▸ hg
  rw [indepFun_iff_map_prod_eq_prod_map_map (hf'.comp_aemeasurable hπ.aemeasurable)
    (hg'.comp_aemeasurable hπ.aemeasurable)]
  rw [indepFun_iff_map_prod_eq_prod_map_map hf hg] at h
  have e1 : P.map (fun ω => ((f ∘ π) ω, (g ∘ π) ω)) = P'.map (fun ω' => (f ω', g ω')) := by
    rw [← hmap, AEMeasurable.map_map_of_aemeasurable (hf'.prodMk hg') hπ.aemeasurable]; rfl
  have e2 : P.map (f ∘ π) = P'.map f := by
    rw [← hmap, AEMeasurable.map_map_of_aemeasurable hf' hπ.aemeasurable]
  have e3 : P.map (g ∘ π) = P'.map g := by
    rw [← hmap, AEMeasurable.map_map_of_aemeasurable hg' hπ.aemeasurable]
  rw [e1, e2, e3]; exact h

theorem linSol_comp {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
    {P' : Measure Ω'} [IsProbabilityMeasure P] (π : Ω → Ω') (hπ : Measurable π) (hmap : P.map π = P')
    {D : DynData d} {ρ : ℝ → Torus d → ℝ} {m q T : ℝ} {Y₀ : Ω' → NegSobolev d m}
    {Y : ℝ → Ω' → NegSobolev d m} (hY₀ : Measurable Y₀)
    (hGmeas : ∀ (p : ℕ) (ts : Fin p → ℝ) (φ : Fin p → Torus d → ℝ), (∀ a, ts a ∈ Set.Icc 0 T) →
      (∀ a, Torus.IsSmooth (φ a)) → Measurable fun ω' => (WithLp.toLp 2 fun a =>
        NegSobolev.eval (Y (ts a) ω') (φ a) - NegSobolev.eval (Y₀ ω') (propagator D ρ 0 (ts a) (φ a)) :
        EuclideanSpace ℝ (Fin p)))
    (h : IsLinearFluctuationSolution P' D ρ m q T Y₀ Y) :
    IsLinearFluctuationSolution P D ρ m q T (fun ω => Y₀ (π ω)) (fun t ω => Y t (π ω)) := by
  have hae : ∀ {Q : Ω' → Prop}, (∀ᵐ ω ∂P', Q ω) → ∀ᵐ ω ∂P, Q (π ω) := fun {Q} hQ =>
    ae_of_ae_map hπ.aemeasurable (hmap ▸ hQ)
  refine ⟨hae h.init, hae h.cont, fun t => (h.meas t).comp hπ, fun p ts φ hts hφ => ?_⟩
  obtain ⟨hind, hlaw⟩ := h.gaussian_part p ts φ hts hφ
  haveI : IsProbabilityMeasure P' := hmap ▸ (inferInstance : IsProbabilityMeasure (P.map π))
  set Gf : Ω' → EuclideanSpace ℝ (Fin p) := fun ω' => WithLp.toLp 2 fun a =>
    NegSobolev.eval (Y (ts a) ω') (φ a) - NegSobolev.eval (Y₀ ω') (propagator D ρ 0 (ts a) (φ a)) with hGf
  have hGm : AEMeasurable Gf P' := (hGmeas p ts φ hts hφ).aemeasurable
  refine ⟨indepFun_comp_of_map π hπ hmap hGm hY₀.aemeasurable hind, ?_⟩
  have : law P (fun ω => Gf (π ω)) = law P' Gf := by
    unfold law
    rw [← hmap]
    exact (AEMeasurable.map_map_of_aemeasurable (hmap ▸ hGm) hπ.aemeasurable).symm
  exact this.trans hlaw

/-- Reindexing the coordinates of a centred multivariate Gaussian. -/
theorem map_reindex_multivariateGaussian {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι']
    [DecidableEq ι'] (f : ι ≃ ι') (S : Matrix ι ι ℝ) :
    (multivariateGaussian 0 S).map (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ f) =
      multivariateGaussian 0 (S.submatrix f.symm f.symm) := by
  set L := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ f with hL
  by_cases hS : S.PosSemidef
  · have hS' : (S.submatrix f.symm f.symm).PosSemidef := hS.submatrix f.symm
    refine Measure.ext_of_charFun ?_
    funext t
    rw [charFun_multivariateGaussian hS']
    have h1 : charFun ((multivariateGaussian 0 S).map L) t = charFun (multivariateGaussian 0 S) (L.symm t) := by
      rw [charFun_apply, charFun_apply, integral_map L.continuous.aemeasurable]
      · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [LinearIsometryEquiv.inner_map_eq_flip]
      · exact (Complex.measurable_exp.comp (by fun_prop)).aestronglyMeasurable
    rw [h1, charFun_multivariateGaussian hS]
    congr 2
    · simp
    · congr 1
      simp only [dotProduct, Matrix.mulVec, Matrix.submatrix_apply]
      have hx : ∀ x, (L.symm t).ofLp x = t.ofLp (f x) := fun x => by
        simp [hL, LinearIsometryEquiv.piLpCongrLeft_symm, LinearIsometryEquiv.piLpCongrLeft_apply,
          Equiv.piCongrLeft'_apply]
      simp only [hx]
      congr 1
      refine Fintype.sum_equiv f _ _ fun x => ?_
      congr 1
      refine (Fintype.sum_equiv f _ _ fun y => ?_)
      simp
  · have hS' : ¬ (S.submatrix f.symm f.symm).PosSemidef := fun h => hS (by
      simpa using h.submatrix f)
    rw [multivariateGaussian_of_not_posSemidef _ hS, multivariateGaussian_of_not_posSemidef _ hS',
      Measure.map_dirac' L.continuous.measurable]
    simp

theorem crossNoiseCov_congr (D : DynData d) (q : ℝ) {ρ₁ ρ₂ ρ₁' ρ₂' : ℝ → Torus d → ℝ}
    (h : ∀ s : ℝ, 0 ≤ s → ρ₁ s = ρ₂ s) (h' : ∀ s : ℝ, 0 ≤ s → ρ₁' s = ρ₂' s) (ta tb : ℝ)
    (φ ψ : Torus d → ℝ) :
    crossNoiseCov D q ρ₁ ρ₁' ta tb φ ψ = crossNoiseCov D q ρ₂ ρ₂' ta tb φ ψ := by
  unfold crossNoiseCov
  congr 1
  refine setIntegral_congr_fun measurableSet_Icc fun v hv => ?_
  simp only [HRS.MC.Sec7.S7FCW4.S7FCW4_propagator_congr D ρ₁ ρ₂ h, h v hv.1,
    HRS.MC.Sec7.S7FCW4.S7FCW4_propagator_congr D ρ₁' ρ₂' h', h' v hv.1]

end HRS.MC.E214E

end
