import HRS.MS.GenPathAux40
import HRS.Main.GFSpec6

/-!
# S5.6 packet P7f: transfer of the whole-space particle system along a measure-preserving map
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.GenPath

open HRS.Whole HRS.MP.RdRem

variable {d : ℕ}

theorem s56_strong_comp {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {N : ℕ}
    {P : Measure Ω} {P' : Measure Ω'} {π : Ω' → Ω} (hπ : MeasurePreserving π P' P) {D : WholeDyn d} {T : ℝ}
    {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (h : IsWholeStrongSolution P D T X₀ W X) :
    IsWholeStrongSolution P' D T (fun z' => X₀ (π z')) (fun t z' => W t (π z')) (fun t z' => X t (π z')) :=
  { init := hπ.quasiMeasurePreserving.ae h.init
    eqn := hπ.quasiMeasurePreserving.ae h.eqn
    cont := hπ.quasiMeasurePreserving.ae h.cont
    adapted := fun t => (h.adapted t).comp hπ.measurable
    no_collision := hπ.quasiMeasurePreserving.ae h.no_collision }

theorem s56_energyMoment_comp (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) {N : ℕ} (hN : 0 < N)
    {Ω Ω₁ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₁] {P : Measure Ω} {P₁ : Measure Ω₁}
    {π : Ω₁ → Ω} (hπ : MeasurePreserving π P₁ P) (X : ℝ≥0 → Ω → EucConfig d N)
    (hXm : ∀ t, Measurable (X t)) (p : ℝ) :
    S.energyMomentE N p P₁ (fun t z => X t (π z)) = S.energyMomentE N p P X := by
  unfold WholeSetup.energyMomentE
  refine iSup_congr fun t => ?_
  have hm : Measurable fun ζ => ENNReal.ofReal |rieszModulatedEnergy d b.s (X (Real.toNNReal t) ζ)
      (HRS.Whole.withDensityReal (S.ρ N t)) + HRS.oN d b.s b.C₀ N| ^ p := by
    have h := s56_energy_meas b hbv S N
    have e := mrrClamp_of_mem t.2
    have h2 : Measurable fun x : EucConfig d N => rieszModulatedEnergy d b.s x
        (HRS.Whole.withDensityReal (S.ρ N t)) + HRS.oN d b.s b.C₀ N := by
      have := h.comp (measurable_const (a := (t : ℝ)).prodMk measurable_id)
      simpa [Function.comp_def, e] using this
    exact (ENNReal.measurable_ofReal.comp (measurable_abs.comp (h2.comp (hXm _)))).pow_const p
  rw [HRS.GF.lintegral_comp_mp hπ (f := fun ζ => ENNReal.ofReal |rieszModulatedEnergy d b.s
    (X (Real.toNNReal t) ζ) (HRS.Whole.withDensityReal (S.ρ N t)) + HRS.oN d b.s b.C₀ N| ^ p) hm.aemeasurable]

end HRS.MS.GenPath
