import HRS.MP.SelfSimP4MolC5

/-!
# MPP4MOL stage 5c (1): regularity of `u`, `V` and of the log-density `Λ = log u + 1 + V/θ`
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MP.SelfSimP4Mol

variable {d N : ℕ}

/-- `Λ = log u + 1 + V/θ`. -/
def p4m_Lam (v θ : ℝ) (ν : Measure (EucConfig d N)) (V : EucConfig d N → ℝ) (x : EucConfig d N) : ℝ :=
  Real.log (p4Mol v ν x) + 1 + V x / θ

/-- `ℓ_k = ∂_k u / u + ∂_k V / θ = ∂_k u / u - b_k / θ`. -/
def p4m_ell (v θ : ℝ) (ν : Measure (EucConfig d N)) (b : EucConfig d N → EucConfig d N)
    (k : Fin N × Fin d) (x : EucConfig d N) : ℝ :=
  p4m_gu v ν k x / p4Mol v ν x - b x k.1 k.2 / θ

section
variable {v : ℝ} {ν : Measure (EucConfig d N)}

theorem p4m_continuous_fderiv_mol (hv : 0 < v) [IsProbabilityMeasure ν] :
    Continuous (fderiv ℝ (p4Mol v ν)) := by
  obtain ⟨C, hC0, hC⟩ := p4m_D1_bound (d := d) (N := N) hv
  have hG1 : ContDiff ℝ 1 (p4Gauss d N v : EucConfig d N → ℝ) := p4m_contDiff_gauss v
  have hderivc : Continuous (fderiv ℝ (p4Gauss d N v : EucConfig d N → ℝ)) :=
    hG1.continuous_fderiv (by norm_num)
  have e : fderiv ℝ (p4Mol v ν) = fun x => ∫ y, fderiv ℝ (p4Gauss d N v : EucConfig d N → ℝ) (x - y) ∂ν :=
    funext fun x => (p4m_hasFDerivAt_mol hv x).fderiv
  rw [e]
  refine continuous_of_dominated (bound := fun _ => C) ?_ ?_ (integrable_const C) ?_
  · intro x
    exact (hderivc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · intro x
    exact Filter.Eventually.of_forall fun y => hC _
  · exact Filter.Eventually.of_forall fun y => hderivc.comp (continuous_id.sub continuous_const)

theorem p4m_contDiff_mol (hv : 0 < v) [IsProbabilityMeasure ν] : ContDiff ℝ 1 (p4Mol v ν) :=
  contDiff_one_iff_fderiv.2 ⟨fun x => (p4m_hasFDerivAt_mol hv x).differentiableAt,
    p4m_continuous_fderiv_mol hv⟩

theorem p4m_contDiff_V {b : EucConfig d N → EucConfig d N} (hbc : Continuous b) {V : EucConfig d N → ℝ}
    (hV : ∀ x, HasFDerivAt V (-(p4InnerL (b x))) x) : ContDiff ℝ 1 V := by
  refine contDiff_one_iff_fderiv.2 ⟨fun x => (hV x).differentiableAt, ?_⟩
  have : fderiv ℝ V = fun x => -(p4InnerL (b x)) := funext fun x => (hV x).fderiv
  rw [this]
  exact (p4m_continuous_innerL.comp hbc).neg

theorem p4m_contDiff_Lam (hv : 0 < v) [IsProbabilityMeasure ν] (hm : Integrable p4m_q ν) (θ : ℝ)
    {V : EucConfig d N → ℝ} (hVd : ContDiff ℝ 1 V) : ContDiff ℝ 1 (p4m_Lam v θ ν V) := by
  unfold p4m_Lam
  have h1 : ContDiff ℝ 1 (fun x => Real.log (p4Mol v ν x)) :=
    (p4m_contDiff_mol hv).log fun x => (p4m_mol_pos hv hm x).ne'
  exact (h1.add contDiff_const).add (hVd.div_const θ)

theorem p4m_fderiv_Lam_basis (hv : 0 < v) [IsProbabilityMeasure ν] (hm : Integrable p4m_q ν) (θ : ℝ)
    {b : EucConfig d N → EucConfig d N} {V : EucConfig d N → ℝ}
    (hV : ∀ x, HasFDerivAt V (-(p4InnerL (b x))) x) (k : Fin N × Fin d) (x : EucConfig d N) :
    fderiv ℝ (p4m_Lam v θ ν V) x (configBasis d N k) = p4m_ell v θ ν b k x := by
  have hu := (p4m_contDiff_mol hv (ν := ν)).differentiable (by norm_num) x
  have h1 := (hu.hasFDerivAt.log (p4m_mol_pos hv hm x).ne')
  have h3 : HasFDerivAt (fun x => V x / θ) (θ⁻¹ • (-(p4InnerL (b x)))) x := by
    have := (hV x).const_smul θ⁻¹
    convert this using 1
    funext y
    simp [div_eq_inv_mul]
  have h2 := ((h1.add_const 1).fun_add h3)
  have e : p4m_Lam v θ ν V = fun x => Real.log (p4Mol v ν x) + 1 + V x / θ := rfl
  rw [e, h2.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.neg_apply]
  rw [p4m_fderiv_mol_basis hv]
  unfold p4m_ell
  rw [p4m_inner_single]
  ring

end

end HRS.MP.SelfSimP4Mol
