import HRS.MS.Fp81S21HilbertMart
import HRS.MS.R2InterpAux110

/-!
# HRS S2.1(iii), B6-i: filtered gradient-noise moment stage

Transfer the uniform empirical higher-marginal moment to the supplied filtered
particle realization.  This is the fixed-time estimate used in the integrated
Hilbert--Schmidt bound for the stochastic-integral construction.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open Classical MeasureTheory
open scoped ENNReal RealInnerProductSpace BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

/-- The uniform higher-marginal estimate also holds along the supplied
filtered version, since P00 identifies its path with the observed particle
path on one event for all times. -/
theorem fp81s21_b6i_filtered_gradient_weight_moment (p : Parameters) :
    ∃ δstar : ℝ, 0 < δstar ∧ δstar ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δstar → ∀ R : Trajectory p δ,
        ∃ C : ℝ, 0 ≤ C ∧
          ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N,
            ∀ Fp : FilteredParticle A, ∀ H : ℝ, 0 < H →
              ∀ u : ℝ, u ∈ Set.Icc 0 H →
                Integrable
                  (fun ω => (N : ℝ)⁻¹ *
                    ∑ i : Fin N,
                      jbracket (Fp.X u.toNNReal ω i) ^ (2 * ((p.d : ℝ) + 2))) A.P ∧
                (∫ ω, ((N : ℝ)⁻¹ *
                  ∑ i : Fin N,
                    jbracket (Fp.X u.toNNReal ω i) ^ (2 * ((p.d : ℝ) + 2))) ∂A.P) ≤ C := by
  obtain ⟨δstar, hδstar, hδhalf, hweights⟩ :=
    fp81s21_b6i_uniform_gradient_weight_moment p
  refine ⟨δstar, hδstar, hδhalf, ?_⟩
  intro δ hδ hδle R
  obtain ⟨C, hC, hweight⟩ := hweights δ hδ hδle R
  refine ⟨C, hC, ?_⟩
  intro N hN A Fp H hH u hu
  let exponent : ℝ := 2 * ((p.d : ℝ) + 2)
  let weight : Euc p.d → ℝ := fun x => jbracket x ^ exponent
  have hweightMeas : Measurable weight := by
    change Measurable (fun x : Euc p.d => jbracket x ^ exponent)
    exact (measurable_id.pow_const exponent).comp (by fun_prop)
  have hweightNonneg : ∀ x, 0 ≤ weight x := by
    intro x
    exact Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hu0 : 0 ≤ u := hu.1
  have hXmeas : Measurable (A.X u.toNNReal) := (A.strong H).adapted _
  obtain ⟨hMomentInt, hMomentBound⟩ := hweight N hN A u hu0
  have hEmp := HRS.MS.R2Interp.s102_empMoment
    (show 0 < N by omega) A.P (A.X u.toNNReal) hXmeas hweightMeas
    hweightNonneg hMomentInt
  have hsame : ∀ᵐ ω ∂A.P, Fp.X u.toNNReal ω = A.X u.toNNReal ω := by
    exact Fp.indist.mono fun ω hω => hω u.toNNReal
  have havgEq :
      (fun ω => (N : ℝ)⁻¹ *
        ∑ i : Fin N, weight (Fp.X u.toNNReal ω i)) =ᵐ[A.P]
      (fun ω => (N : ℝ)⁻¹ *
        ∑ i : Fin N, weight (A.X u.toNNReal ω i)) := by
    filter_upwards [hsame] with ω hω
    simp [hω]
  refine ⟨hEmp.1.congr havgEq.symm, ?_⟩
  calc
    (∫ ω, (N : ℝ)⁻¹ *
      ∑ i : Fin N, weight (Fp.X u.toNNReal ω i) ∂A.P) =
        ∫ ω, (N : ℝ)⁻¹ *
          ∑ i : Fin N, weight (A.X u.toNNReal ω i) ∂A.P :=
            integral_congr_ae havgEq
    _ = ∫ x, weight x ∂(HRS.Whole.meanEmpirical (A.P.map (A.X u.toNNReal))) := hEmp.2
    _ ≤ C := hMomentBound

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.fp81s21_b6i_filtered_gradient_weight_moment
