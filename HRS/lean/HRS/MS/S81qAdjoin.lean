import HRS.MS.S81qOldPhys2
import HRS.MS.S81sGlue

/-!
# S8.1 (worker S81Q): adjoining an independent time-zero variable to a filtered Brownian space

Namespace `HRS.Whole.S81Q`, prefix `s81q_`.

`s81q_adjoin_cyl`: on `Ω₁ × Ω₀` with the product measure and the product filtration `ℱ₁ ⊗ const(borel)`, a cylindrical Brownian motion on `(Ω₁, ℱ₁)`
remains cylindrical Brownian (the independent variable is `ℱ_0`-measurable).  The proof is `isCylindricalBrownian_prod` with the empty second
family.  `s81q_itoC_eq_ito` is the bridge between a finite-index `IsItoC` integral and the real Itô integral `itoIntegral`.
-/

set_option autoImplicit false
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole HRS.Whole.S81P

namespace HRS.Whole.S81Q

/-- The empty Brownian family on a probability space with a constant filtration. -/
theorem s81q_empty_cyl {Ω₀ : Type} [m₀ : MeasurableSpace Ω₀] (μ : Measure Ω₀) [IsProbabilityMeasure μ] :
    IsCylindricalBrownian μ (Filtration.const ℝ m₀ le_rfl) (fun (_ : ℝ≥0) (_ : Ω₀) (e : Empty) => (e.elim : ℝ)) := by
  intro s
  haveI : IsEmpty ↥s := ⟨fun k => k.1.elim⟩
  refine ⟨fun t s' hs hμ => ?_, fun t => ?_, fun ω => ?_, fun ω => ?_, fun s' t hst => ?_, fun s' t hst => ?_⟩
  · exact hs
  · exact measurable_of_subsingleton_codomain _
  · exact Subsingleton.elim _ _
  · exact (continuous_const (y := (fun (k : ↥s) => ((k.1).elim : ℝ)))).congr fun t => Subsingleton.elim _ _
  · have e : (fun ω => (fun (k : ↥s) => ((k.1).elim : ℝ)) - (fun (k : ↥s) => ((k.1).elim : ℝ))) =
        fun _ : Ω₀ => (fun (k : ↥s) => ((k.1).elim : ℝ)) := by
      funext ω; exact Subsingleton.elim _ _
    show Indep (MeasurableSpace.comap (fun ω : Ω₀ => (fun (k : ↥s) => ((k.1).elim : ℝ)) -
      (fun (k : ↥s) => ((k.1).elim : ℝ))) inferInstance) _ μ
    rw [e, MeasurableSpace.comap_const]
    exact indep_bot_left _
  · refine ⟨measurable_const.aemeasurable, ?_⟩
    rw [Measure.pi_of_empty, Measure.map_const, measure_univ, one_smul]
    congr 1
    exact Subsingleton.elim _ _

/-- Adjoining an independent `ℱ_0`-measurable variable keeps a cylindrical Brownian motion Brownian. -/
theorem s81q_adjoin_cyl {Ω₁ Ω₀ : Type} [m₁ : MeasurableSpace Ω₁] [m₀ : MeasurableSpace Ω₀]
    (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁] (μ : Measure Ω₀) [IsProbabilityMeasure μ]
    (ℱ₁ : Filtration ℝ m₁) {κ : Type} [Countable κ] {W : ℝ≥0 → Ω₁ → κ → ℝ}
    (hW : IsCylindricalBrownian P₁ ℱ₁ W) :
    IsCylindricalBrownian (P₁.prod μ) (prodFiltration P₁ μ ℱ₁ (Filtration.const ℝ m₀ le_rfl))
      (fun t (p : Ω₁ × Ω₀) k => W t p.1 k) := by
  have h := isCylindricalBrownian_prod hW (s81q_empty_cyl μ)
  exact s81p_isCylindricalBrownian_comp_injective h Sum.inl Sum.inl_injective

/-- For a finite index set the countable-index Itô integral is the real Itô integral. -/
theorem s81q_itoC_eq_ito {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {κ : Type} [Fintype κ] {W : ℝ≥0 → Ω → κ → ℝ}
    (hW : IsBrownianFiltration P ℱ W) {ξ : ℝ → Ω → κ → ℝ}
    (hξ' : IsProgressiveL2 P ℱ (fun r ω (k : (Finset.univ : Finset κ)) => ξ r ω k))
    {J : ℝ → Ω → ℝ} (hJ : IsItoC P ℱ W ξ J) {τ : ℝ} (hτ : 0 ≤ τ) :
    J τ =ᵐ[P] itoIntegral P ℱ W ξ τ := by
  classical
  have h := hJ.approx τ hτ
  have h1 : (atTop : Filter (Finset κ)) = pure Finset.univ :=
    atTop_eq_pure_of_isTop (x := (Finset.univ : Finset κ)) (fun s => Finset.subset_univ s)
  rw [h1] at h
  have h0 := tendsto_nhds_unique (tendsto_pure_nhds _ _) h
  set e : ↥(Finset.univ : Finset κ) → κ := fun k => (k : κ) with he
  have hinj : Function.Injective e := Subtype.val_injective
  have hW₁ : IsBrownianFiltration P ℱ (fun t ω (i : (Finset.univ : Finset κ)) => W t ω (e i)) :=
    HRS.MS.S52.s52_brownian_restrict e hinj hW
  have hpad := itoIntegral_pad e hinj hW hW₁ hξ'
  have hpadfun : padFun e (fun r ω (k : (Finset.univ : Finset κ)) => ξ r ω k) = ξ := by
    funext r ω k
    have := padVec_apply e hinj (fun (k : (Finset.univ : Finset κ)) => ξ r ω k)
      ⟨k, Finset.mem_univ k⟩
    simpa [padFun, he] using this
  rw [hpadfun] at hpad
  have hmeas : AEMeasurable (fun ω => itoIntegral P ℱ
      (fun t ω (k : (Finset.univ : Finset κ)) => W t ω k)
      (fun r ω (k : (Finset.univ : Finset κ)) => ξ r ω k) τ ω - J τ ω) P := by
    refine ((((adapted_itoIntegral P ℱ _ _ τ).mono (ℱ.le τ) le_rfl)).sub ?_).aemeasurable
    exact (hJ.adapted τ).mono (ℱ.le τ) le_rfl
  have h2 := ae_eq_zero_of_lintegral_enorm_sq_eq_zero hmeas h0
  filter_upwards [h2, hpad] with ω hω hp
  have hp' := hp τ
  have : itoIntegral P ℱ (fun t ω (k : (Finset.univ : Finset κ)) => W t ω k)
      (fun r ω (k : (Finset.univ : Finset κ)) => ξ r ω k) τ ω - J τ ω = 0 := hω
  rw [← hp']
  linarith

end HRS.Whole.S81Q
