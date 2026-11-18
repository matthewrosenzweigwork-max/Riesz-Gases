import HRS.MP.SelfSimP4MolE3

/-!
# MPP4MOL stage 5c (8): parametric integrals with compactly supported integrands
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MP.SelfSimP4Mol

variable {d N : ℕ}

theorem p4m_cont_param_cs {f : ℝ → EucConfig d N → ℝ} (hf : Continuous (Function.uncurry f))
    {χ : EucConfig d N → ℝ} (hχs : HasCompactSupport χ) (hz : ∀ s x, χ x = 0 → f s x = 0) :
    Continuous (fun s => ∫ x, f s x) := by
  have hc := continuous_parametric_integral_of_continuous (μ := (volume : Measure (EucConfig d N))) hf hχs
  have : (fun s => ∫ x, f s x) = fun s => ∫ x in tsupport χ, f s x := by
    funext s
    symm
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
      hz s x (image_eq_zero_of_notMem_tsupport hx)
  rw [this]
  exact hc

theorem p4m_integrable_time {f : ℝ → EucConfig d N → ℝ} (hf : Continuous (Function.uncurry f))
    {χ : EucConfig d N → ℝ} (hχs : HasCompactSupport χ) (hz : ∀ s x, χ x = 0 → f s x = 0) (t : ℝ) :
    Integrable (Function.uncurry f) ((volume.restrict (Set.Icc (0 : ℝ) t)).prod
      (volume : Measure (EucConfig d N))) := by
  have e : (volume.restrict (Set.Icc (0 : ℝ) t)).prod (volume : Measure (EucConfig d N)) =
      ((volume : Measure ℝ).prod (volume : Measure (EucConfig d N))).restrict
        (Set.Icc (0 : ℝ) t ×ˢ (Set.univ : Set (EucConfig d N))) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [e]
  have hS : IsCompact (Set.Icc (0 : ℝ) t ×ˢ tsupport χ) := isCompact_Icc.prod hχs
  have h1 : IntegrableOn (Function.uncurry f) (Set.Icc (0 : ℝ) t ×ˢ tsupport χ)
      ((volume : Measure ℝ).prod (volume : Measure (EucConfig d N))) :=
    hf.continuousOn.integrableOn_compact hS
  refine IntegrableOn.of_forall_diff_eq_zero h1 (measurableSet_Icc.prod MeasurableSet.univ) ?_
  rintro ⟨s, x⟩ ⟨⟨hs, -⟩, hx⟩
  have : x ∉ tsupport χ := fun h => hx ⟨hs, h⟩
  exact hz s x (image_eq_zero_of_notMem_tsupport this)

theorem p4m_swap_time {f : ℝ → EucConfig d N → ℝ} (hf : Continuous (Function.uncurry f))
    {χ : EucConfig d N → ℝ} (hχs : HasCompactSupport χ) (hz : ∀ s x, χ x = 0 → f s x = 0) (t : ℝ) :
    ∫ s in Set.Icc (0 : ℝ) t, ∫ x, f s x = ∫ x, ∫ s in Set.Icc (0 : ℝ) t, f s x :=
  integral_integral_swap (p4m_integrable_time hf hχs hz t)

end HRS.MP.SelfSimP4Mol
