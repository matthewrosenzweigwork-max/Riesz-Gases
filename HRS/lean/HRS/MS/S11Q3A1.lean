import HRS.MS.S113Q1

/-!
# S11.3 / S11.4 (worker S11Q3), A1: spatial 2-jets with time-continuous coefficients

`s11q3_Jet2 A a1 a2`: `A : ℝ → E → ℝ` is jointly continuous, `a1 t = D_x A t`, `a2 t = D_x² A t` (explicit witnesses, jointly continuous).
Closure under sums, products with continuous functions of `t`, linear substitutions in space, and composition with a scalar `C²` function
(`exp`, `log` on `(0,∞)`).  Nothing here needs a time derivative.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ContDiff

namespace HRS.MS.S11Q3

section Jet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

theorem s11q3_cont_add2 {X : Type*} [TopologicalSpace X] [FiniteDimensional ℝ E] {f g : X → E →L[ℝ] E →L[ℝ] ℝ}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun x => f x + g x := by
  rw [continuous_clm_apply]
  intro v
  simp only [add_apply]
  exact ((continuous_clm_apply.1 hf) v).add ((continuous_clm_apply.1 hg) v)

structure s11q3_Jet2 (A : ℝ → E → ℝ) (a1 : ℝ → E → E →L[ℝ] ℝ) (a2 : ℝ → E → E →L[ℝ] E →L[ℝ] ℝ) : Prop where
  c0 : Continuous fun p : ℝ × E => A p.1 p.2
  c1 : Continuous fun p : ℝ × E => a1 p.1 p.2
  c2 : Continuous fun p : ℝ × E => a2 p.1 p.2
  h1 : ∀ t z, HasFDerivAt (A t) (a1 t z) z
  h2 : ∀ t z, HasFDerivAt (a1 t) (a2 t z) z

theorem s11q3_Jet2.zero : s11q3_Jet2 (E := E) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) where
  c0 := continuous_const
  c1 := continuous_const
  c2 := continuous_const
  h1 _ _ := hasFDerivAt_const _ _
  h2 _ _ := hasFDerivAt_const _ _

theorem s11q3_Jet2.add [FiniteDimensional ℝ E] {A B : ℝ → E → ℝ} {a1 b1 : ℝ → E → E →L[ℝ] ℝ} {a2 b2 : ℝ → E → E →L[ℝ] E →L[ℝ] ℝ}
    (hA : s11q3_Jet2 A a1 a2) (hB : s11q3_Jet2 B b1 b2) :
    s11q3_Jet2 (fun t z => A t z + B t z) (fun t z => a1 t z + b1 t z) (fun t z => a2 t z + b2 t z) where
  c0 := hA.c0.add hB.c0
  c1 := hA.c1.add hB.c1
  c2 := s11q3_cont_add2 hA.c2 hB.c2
  h1 t z := (hA.h1 t z).add (hB.h1 t z)
  h2 t z := (hA.h2 t z).add (hB.h2 t z)

theorem s11q3_Jet2.sum [FiniteDimensional ℝ E] {ι : Type*} (S : Finset ι) {A : ι → ℝ → E → ℝ} {a1 : ι → ℝ → E → E →L[ℝ] ℝ}
    {a2 : ι → ℝ → E → E →L[ℝ] E →L[ℝ] ℝ} (h : ∀ i ∈ S, s11q3_Jet2 (A i) (a1 i) (a2 i)) :
    s11q3_Jet2 (fun t z => ∑ i ∈ S, A i t z) (fun t z => ∑ i ∈ S, a1 i t z) (fun t z => ∑ i ∈ S, a2 i t z) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (s11q3_Jet2.zero (E := E))
  | insert j S hj ih =>
    have := (h j (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert hj] using this

theorem s11q3_Jet2.smulT {A : ℝ → E → ℝ} {a1 : ℝ → E → E →L[ℝ] ℝ} {a2 : ℝ → E → E →L[ℝ] E →L[ℝ] ℝ}
    (hA : s11q3_Jet2 A a1 a2) {κ : ℝ → ℝ} (hκ : Continuous κ) :
    s11q3_Jet2 (fun t z => κ t * A t z) (fun t z => κ t • a1 t z) (fun t z => κ t • a2 t z) where
  c0 := (hκ.comp continuous_fst).mul hA.c0
  c1 := (hκ.comp continuous_fst).smul hA.c1
  c2 := (hκ.comp continuous_fst).smul hA.c2
  h1 t z := (hA.h1 t z).const_mul (κ t)
  h2 t z := (hA.h2 t z).const_smul (κ t)

theorem s11q3_Jet2.static {G : E → ℝ} (hG : ContDiff ℝ 2 G) :
    s11q3_Jet2 (fun _ z => G z) (fun _ z => fderiv ℝ G z) (fun _ z => fderiv ℝ (fderiv ℝ G) z) where
  c0 := hG.continuous.comp continuous_snd
  c1 := (hG.continuous_fderiv (by norm_num)).comp continuous_snd
  c2 := ((hG.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)).comp continuous_snd
  h1 _ z := (hG.differentiable (by norm_num) z).hasFDerivAt
  h2 _ z := (((hG.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) z).hasFDerivAt

/-- Linear substitution in space. -/
theorem s11q3_Jet2.comp_clm [FiniteDimensional ℝ E'] {A : ℝ → E → ℝ} {a1 : ℝ → E → E →L[ℝ] ℝ}
    {a2 : ℝ → E → E →L[ℝ] E →L[ℝ] ℝ} (hA : s11q3_Jet2 A a1 a2) (π : E' →L[ℝ] E) :
    s11q3_Jet2 (fun t z => A t (π z)) (fun t z => (a1 t (π z)).comp π)
      (fun t z => (a2 t (π z)).bilinearComp π π) where
  c0 := hA.c0.comp (continuous_fst.prodMk (π.continuous.comp continuous_snd))
  c1 := by
    rw [continuous_clm_apply]
    intro v
    have : Continuous fun p : ℝ × E' => a1 p.1 (π p.2) := hA.c1.comp (continuous_fst.prodMk (π.continuous.comp continuous_snd))
    exact this.clm_apply continuous_const
  c2 := by
    rw [continuous_clm_apply]
    intro v
    rw [continuous_clm_apply]
    intro w
    have : Continuous fun p : ℝ × E' => a2 p.1 (π p.2) := hA.c2.comp (continuous_fst.prodMk (π.continuous.comp continuous_snd))
    exact (this.clm_apply continuous_const).clm_apply continuous_const
  h1 t z := (hA.h1 t (π z)).comp z π.hasFDerivAt
  h2 t z := by
    have h := (hA.h2 t (π z)).comp z π.hasFDerivAt
    have hΦ : HasFDerivAt (fun f : E →L[ℝ] ℝ => f.comp π) ((ContinuousLinearMap.compL ℝ E' E ℝ).flip π)
        (a1 t (π z)) := ((ContinuousLinearMap.compL ℝ E' E ℝ).flip π).hasFDerivAt
    have h3 := hΦ.comp z h
    have e : (a2 t (π z)).bilinearComp π π = ((ContinuousLinearMap.compL ℝ E' E ℝ).flip π).comp ((a2 t (π z)).comp π) := by
      ext v w
      simp
    rw [e]
    exact h3

/-- Composition with a scalar `C²` function `φ` on an open set `U` containing the values. -/
theorem s11q3_Jet2.comp_scalar [FiniteDimensional ℝ E] {A : ℝ → E → ℝ} {a1 : ℝ → E → E →L[ℝ] ℝ} {a2 : ℝ → E → E →L[ℝ] E →L[ℝ] ℝ}
    (hA : s11q3_Jet2 A a1 a2) {φ φ' φ'' : ℝ → ℝ} {U : Set ℝ} (hAU : ∀ t z, A t z ∈ U)
    (hφ : ∀ y ∈ U, HasDerivAt φ (φ' y) y) (hφ' : ∀ y ∈ U, HasDerivAt φ' (φ'' y) y)
    (hc'' : ContinuousOn φ'' U) :
    s11q3_Jet2 (fun t z => φ (A t z)) (fun t z => φ' (A t z) • a1 t z)
      (fun t z => φ' (A t z) • a2 t z + (φ'' (A t z) • a1 t z).smulRight (a1 t z)) := by
  have hcφ : ContinuousOn φ U := fun y hy => (hφ y hy).continuousAt.continuousWithinAt
  have hcφ' : ContinuousOn φ' U := fun y hy => (hφ' y hy).continuousAt.continuousWithinAt
  have hAc : Continuous fun p : ℝ × E => A p.1 p.2 := hA.c0
  have hmem : ∀ p : ℝ × E, A p.1 p.2 ∈ U := fun p => hAU p.1 p.2
  refine ⟨hcφ.comp_continuous hAc hmem, ?_, ?_, fun t z => ?_, fun t z => ?_⟩
  · exact (hcφ'.comp_continuous hAc hmem).smul hA.c1
  · refine s11q3_cont_add2 ((hcφ'.comp_continuous hAc hmem).smul hA.c2) ?_
    have h1 : Continuous fun p : ℝ × E => φ'' (A p.1 p.2) • a1 p.1 p.2 := (hc''.comp_continuous hAc hmem).smul hA.c1
    exact (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)).continuous₂.comp₂ h1 hA.c1
  · exact (hφ _ (hAU t z)).comp_hasFDerivAt z (hA.h1 t z)
  · have hc : HasFDerivAt (fun y => φ' (A t y)) (φ'' (A t z) • a1 t z) z :=
      (hφ' _ (hAU t z)).comp_hasFDerivAt z (hA.h1 t z)
    exact hc.smul (hA.h2 t z)

theorem s11q3_Jet2.exp [FiniteDimensional ℝ E] {A : ℝ → E → ℝ} {a1 : ℝ → E → E →L[ℝ] ℝ} {a2 : ℝ → E → E →L[ℝ] E →L[ℝ] ℝ}
    (hA : s11q3_Jet2 A a1 a2) :
    s11q3_Jet2 (fun t z => Real.exp (A t z)) (fun t z => Real.exp (A t z) • a1 t z)
      (fun t z => Real.exp (A t z) • a2 t z + (Real.exp (A t z) • a1 t z).smulRight (a1 t z)) :=
  hA.comp_scalar (U := univ) (φ := Real.exp) (φ' := Real.exp) (φ'' := Real.exp) (fun _ _ => mem_univ _)
    (fun y _ => Real.hasDerivAt_exp y) (fun y _ => Real.hasDerivAt_exp y) Real.continuous_exp.continuousOn

theorem s11q3_Jet2.log [FiniteDimensional ℝ E] {A : ℝ → E → ℝ} {a1 : ℝ → E → E →L[ℝ] ℝ} {a2 : ℝ → E → E →L[ℝ] E →L[ℝ] ℝ}
    (hA : s11q3_Jet2 A a1 a2) (hpos : ∀ t z, 0 < A t z) :
    s11q3_Jet2 (fun t z => Real.log (A t z)) (fun t z => (A t z)⁻¹ • a1 t z)
      (fun t z => (A t z)⁻¹ • a2 t z + (-((A t z) ^ 2)⁻¹ • a1 t z).smulRight (a1 t z)) := by
  refine hA.comp_scalar (U := Ioi 0) (φ := Real.log) (φ' := fun y => y⁻¹) (φ'' := fun y => -(y ^ 2)⁻¹)
    hpos (fun y hy => Real.hasDerivAt_log (Set.mem_Ioi.1 hy).ne') (fun y hy => ?_) ?_
  · have := hasDerivAt_inv (Set.mem_Ioi.1 hy).ne'
    simpa using this
  · refine ContinuousOn.neg ?_
    exact (continuousOn_id.pow 2).inv₀ fun y hy => pow_ne_zero 2 (Set.mem_Ioi.1 hy).ne'

end Jet

end HRS.MS.S11Q3

end
