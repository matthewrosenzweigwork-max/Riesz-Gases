import HRS.Uniform.Q07cAux10

/-!
# Q07c, part 11: the difference covariation density `Sd` and small lemmas
-/

noncomputable section

open HRS HRS.MRep
open MeasureTheory Filter Topology HRS.HilbertCLTAux ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q07c

section Sd

open Classical

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {ι₀ : Type*} [Countable ι₀] (e0 : HilbertBasis ι₀ ℝ H)
variable {α : Type*} {mα : MeasurableSpace α}

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
lemma traceNormForm_zero' : traceNormForm (0 : H →L[ℝ] H →L[ℝ] ℝ) = 0 := by
  unfold traceNormForm; simp

lemma bures2_of_subsingleton [Subsingleton H] (C D : H →L[ℝ] H →L[ℝ] ℝ) :
    Uniform.bures2 C D = 0 := by
  have h : ∀ F : H →L[ℝ] H →L[ℝ] ℝ, F = 0 := form_eq_zero_of_subsingleton
  have h1 : traceNormForm C = 0 := by rw [h C]; exact traceNormForm_zero'
  have h2 : traceNormForm D = 0 := by rw [h D]; exact traceNormForm_zero'
  have h3 : traceNormForm ((innerSL ℝ).comp ((Uniform.formSqrt D).comp (Uniform.formSqrt C))) = 0 := by
    rw [h ((innerSL ℝ).comp ((Uniform.formSqrt D).comp (Uniform.formSqrt C)))]
    exact traceNormForm_zero'
  unfold Uniform.bures2
  rw [h1, h2, h3]; ring

lemma eq_zero_of_inner_basis (b : HilbertBasis ι₀ ℝ H) {v : H} (h : ∀ i, inner ℝ (b i) v = 0) :
    v = 0 := by
  have : b.repr v = b.repr 0 := by
    ext i
    simp [HilbertBasis.repr_apply_apply, h i]
  exact b.repr.injective this

/-- The covariation density of the difference: the covariance of the difference integrand where the
representing integrand reproduces the covariance, and a rank-one form of the right trace norm
otherwise. -/
def SdDef (D C Z S : α → H →L[ℝ] H →L[ℝ] ℝ) (a : α) : H →L[ℝ] H →L[ℝ] ℝ :=
  if C a = S a then Z a else
    fbForm (Uniform.bures2 (regForm e0 (S a)) (regForm e0 (D a)))

include e0 in
lemma measurableSet_eq_forms {C S : α → H →L[ℝ] H →L[ℝ] ℝ}
    (hC : ∀ x y, Measurable fun a => C a x y) (hS : ∀ x y, Measurable fun a => S a x y) :
    MeasurableSet {a | C a = S a} := by
  have : {a | C a = S a} = ⋂ i, ⋂ j, {a | C a (e0 i) (e0 j) = S a (e0 i) (e0 j)} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact ⟨fun h i j => by rw [h], fun h => form_ext_basis e0 h⟩
  rw [this]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
    measurableSet_eq_fun (hC _ _) (hS _ _)

lemma measurable_SdDef {D C Z S : α → H →L[ℝ] H →L[ℝ] ℝ}
    (hC : ∀ x y, Measurable fun a => C a x y) (hZ : ∀ x y, Measurable fun a => Z a x y)
    (hS : ∀ x y, Measurable fun a => S a x y) (hD : ∀ x y, Measurable fun a => D a x y)
    (x y : H) : Measurable fun a => SdDef e0 D C Z S a x y := by
  have hset := measurableSet_eq_forms e0 hC hS
  have hc : Measurable fun a => Uniform.bures2 (regForm e0 (S a)) (regForm e0 (D a)) :=
    measurable_bures2 e0 (fun a => regForm_tc e0 _) (fun a => regForm_tc e0 _)
      (fun x y => measurable_regForm e0 hS x y) (fun x y => measurable_regForm e0 hD x y)
  have : (fun a => SdDef e0 D C Z S a x y) =
      fun a => if C a = S a then Z a x y else fbForm
        (Uniform.bures2 (regForm e0 (S a)) (regForm e0 (D a))) x y := by
    funext a; unfold SdDef; split_ifs <;> rfl
  rw [this]
  exact Measurable.ite hset (hZ x y) ((measurable_fbForm x y).comp hc)

lemma SdDef_tc {D C Z S : α → H →L[ℝ] H →L[ℝ] ℝ} (hZ : ∀ a, IsTraceClassCov (Z a)) (a : α) :
    IsTraceClassCov (SdDef e0 D C Z S a) := by
  unfold SdDef
  split_ifs
  · exact hZ a
  · exact fbForm_tc _

lemma traceNormForm_SdDef {D C Z S : α → H →L[ℝ] H →L[ℝ] ℝ} (a : α)
    (hS : IsTraceClassCov (S a)) (hDa : IsTraceClassCov (D a))
    (hgood : C a = S a → traceNormForm (Z a) = Uniform.bures2 (S a) (D a)) :
    traceNormForm (SdDef e0 D C Z S a) = Uniform.bures2 (S a) (D a) := by
  unfold SdDef
  by_cases h : C a = S a
  · simp only [h, if_true]; exact hgood h
  · simp only [h, if_false]
    rw [regForm_eq e0 hS, regForm_eq e0 hDa]
    refine traceNormForm_fbForm (bures2_nonneg hS hDa) ?_
    by_cases hH : Subsingleton H
    · left; exact bures2_of_subsingleton _ _
    · right; exact not_subsingleton_iff_nontrivial.1 hH

end Sd

section NegZero

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {N : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)} {t : ℝ}

lemma isHM_ae_zero_nonpos (hM : IsHilbertMartingaleWithCovariation P ℱ t N Sg) {τ : ℝ}
    (hτ : τ ≤ 0) : N τ =ᵐ[P] 0 := by
  obtain ⟨ι₀, hι, b, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := H)
  haveI := hι
  have h : ∀ i, ∀ᵐ ω ∂P, inner ℝ (N τ ω) (b i) = 0 := fun i => by
    filter_upwards [ae_zero_nonpos_aux hM (b i) hτ] with ω h
    simpa using h
  filter_upwards [ae_all_iff.2 h] with ω hω
  exact eq_zero_of_inner_basis b fun i => by rw [real_inner_comm]; exact hω i

end NegZero

end HRS.Uniform.Q07c
