import HRS.MC.CepP5
import HRS.MC.CepP3

/-!
# Packet P6, Aux1: the collision set is Lebesgue-null on `Config d N` (`d ≥ 1`)
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MC.CepP6

open HRS HRS.MC.CepP3

variable {d N : ℕ}

/-- The subspace `{Y | Y i = Y j}` of the covering space. -/
def eqSub (d N : ℕ) (i j : Fin N) : Submodule ℝ (Fin N → Euc d) where
  carrier := {Y | Y i = Y j}
  add_mem' := by
    intro a b ha hb
    simp only [mem_setOf_eq, Pi.add_apply] at *
    rw [ha, hb]
  zero_mem' := rfl
  smul_mem' := by
    intro c a ha
    simp only [mem_setOf_eq, Pi.smul_apply] at *
    rw [ha]

theorem eqSub_ne_top (hd : 1 ≤ d) {i j : Fin N} (hij : i ≠ j) : eqSub d N i j ≠ ⊤ := by
  intro h
  have : (Pi.single i (EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ)) : Fin N → Euc d) ∈ eqSub d N i j := by
    rw [h]; trivial
  have h2 : (Pi.single i (EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ)) : Fin N → Euc d) i =
      (Pi.single i (EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ)) : Fin N → Euc d) j := this
  rw [Pi.single_eq_same, Pi.single_eq_of_ne hij.symm] at h2
  have := congrArg (fun v : Euc d => v ⟨0, hd⟩) h2
  simp at this

theorem volume_collisionSet (hd : 1 ≤ d) : (volume : Measure (Config d N)) (collisionSet d N) = 0 := by
  have hmp := mkC_measurePreserving_cube (d := d) (N := N)
  have hcm : MeasurableSet (collisionSet d N) := (isClosed_collisionSet d N).measurableSet
  rw [← hmp.measure_preimage hcm.nullMeasurableSet,
    Measure.restrict_apply (measurable_mkC hcm)]
  refine measure_mono_null ?_ (measure_iUnion_null fun i => measure_iUnion_null fun j =>
    measure_iUnion_null fun hij => Measure.addHaar_submodule (volume : Measure (Fin N → Euc d))
      (eqSub d N i j) (eqSub_ne_top hd hij))
  intro Y hY
  obtain ⟨i, j, hij, h⟩ := hY.1
  simp only [mem_iUnion]
  refine ⟨i, j, hij, ?_⟩
  show Y i = Y j
  ext k
  have h1 : Torus.rep (Torus.mk (Y i)) k = Torus.rep (Torus.mk (Y j)) k := by
    have : Torus.mk (Y i) = Torus.mk (Y j) := h
    rw [this]
  rw [rep_mk_apply, rep_mk_apply, Int.fract_eq_self.2 (hY.2 i k), Int.fract_eq_self.2 (hY.2 j k)] at h1
  exact h1

end HRS.MC.CepP6
