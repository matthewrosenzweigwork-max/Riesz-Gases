import HRS.MS.SA12W2D
import HRS.MC.CepP3Aux1
import HRS.MS.SA12V2
import HRS.MS.SA12BuildC20

/-!
# S.A.12 C5 (SA12W2 worker), part E: descent of `L`-periodic functions to the unit torus

`sa12w2_desc L f` (`x ↦ f (L • rep x)`), `lift (desc L f) y = f (L y)` for `L`-periodic `f`, and the integral dictionary
torus `↔` unit cube `↔` period box `[0,L)^d`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ComplexConjugate ContDiff

namespace HRS.PDE.SA12W2

variable {d : ℕ}

open HRS.Whole HRS.Whole.AppendixALemmas

/-- The unit-torus function `x ↦ f (L • rep x)`. -/
def sa12w2_desc (L : ℝ) (f : Euc d → ℝ) : Torus d → ℝ := fun x => f (L • Torus.rep x)

theorem sa12w2_lift_desc {L : ℝ} {f : Euc d → ℝ}
    (hper : ∀ (x : Euc d) (z : Fin d → ℤ), f (x + L • latticePt z) = f x) (y : Euc d) :
    Torus.lift (sa12w2_desc L f) y = f (L • y) := by
  obtain ⟨m, hm⟩ := HRS.KernelGrad.exists_lattice_of_mk_eq (x := Torus.rep (Torus.mk y)) (y := y)
    (Torus.mk_rep _)
  show f (L • Torus.rep (Torus.mk y)) = f (L • y)
  rw [hm, smul_add]
  exact hper (L • y) m

theorem sa12w2_contDiff_desc {L : ℝ} {f : Euc d → ℝ}
    (hper : ∀ (x : Euc d) (z : Fin d → ℤ), f (x + L • latticePt z) = f x) (hL : L ≠ 0) {n : WithTop ℕ∞}
    (hf : ContDiff ℝ n f) : Torus.IsCk n (sa12w2_desc L f) := by
  unfold Torus.IsCk
  have : Torus.lift (sa12w2_desc L f) = fun y => f (L • y) := funext (sa12w2_lift_desc hper)
  rw [this]
  exact hf.comp (contDiff_const_smul L)

/-- Integral over the torus as an integral over the unit cube `[0,1)^d`. -/
theorem sa12w2_torus_int_cube {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : Torus d → E)
    (hF : AEStronglyMeasurable F volume) :
    ∫ x, F x = ∫ w in HRS.MC.CepP3.cubeE d, F (Torus.mk w) := by
  have h := HRS.MC.CepP3.mk_measurePreserving_cubeE (d := d)
  conv_lhs => rw [← h.map_eq]
  exact integral_map h.measurable.aemeasurable (by rw [h.map_eq]; exact hF)

theorem sa12w2_cube_smul {L : ℝ} (hL : 0 < L) : (fun w : Euc d => L • w) ⁻¹' periodBox d L = HRS.MC.CepP3.cubeE d := by
  ext w
  simp only [mem_preimage, periodBox, HRS.MC.CepP3.cubeE, mem_setOf_eq, mem_Ico]
  refine forall_congr' fun i => ?_
  simp only [PiLp.smul_apply, smul_eq_mul]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by nlinarith, by nlinarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by nlinarith, by nlinarith⟩

/-- Cube integral and period-box integral. -/
theorem sa12w2_cube_box {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L : ℝ} (hL : 0 < L)
    (g : Euc d → E) :
    ∫ w in HRS.MC.CepP3.cubeE d, g (L • w) = (L ^ d)⁻¹ • ∫ x in periodBox d L, g x := by
  have hmeas : MeasurableSet (periodBox d L) := by
    have : periodBox d L = (fun w : Euc d => w.ofLp) ⁻¹' (Set.pi univ fun _ : Fin d => Ico (0 : ℝ) L) := by
      ext w; simp [periodBox]
    rw [this]
    exact (MeasurableSet.pi countable_univ fun _ _ => measurableSet_Ico).preimage
      (PiLp.volume_preserving_ofLp (Fin d)).measurable
  rw [← sa12w2_cube_smul hL, ← integral_indicator (hmeas.preimage (measurable_const_smul L)),
    ← integral_indicator hmeas]
  have e : (fun w : Euc d => ((fun w : Euc d => L • w) ⁻¹' periodBox d L).indicator
      (fun w => g (L • w)) w) = fun w => (periodBox d L).indicator g (L • w) := by
    funext w
    by_cases hw : L • w ∈ periodBox d L <;> simp [Set.indicator, hw]
  rw [e, Measure.integral_comp_smul (μ := (volume : Measure (Euc d))) ((periodBox d L).indicator g) L]
  simp [finrank_euclideanSpace, abs_of_pos (pow_pos hL d)]

end HRS.PDE.SA12W2
