import HRS.MC.S7S7bAux5
import HRS.Energy.Commutator.EnergyAux

/-!
# Packet `s7_S7b_weighted_moments`, helper 6: translation estimate in `L^2`
`int |f(x + z) - f(x)|^2 dx <= tdist(z,0)^2 ||f||_{H^1}^2`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate

noncomputable section

namespace HRS.MC.Sec7.S7b

open HRS HRS.PDE HRS.PDE.MFApriori HRS.PDE.MFPair HRS.PDE.MFThermalReg HRS.PDE.ClassicalPart

variable {d : ℕ}

theorem s7b_coeff_shift {f : Torus d → ℝ} (hf : Continuous f) (z : Torus d) (k : Lattice d) :
    coeffOf (fun x => f (x + z) - f x) k = (Torus.mode k z - 1) * coeffOf f k := by
  have hc : ∀ g : Torus d → ℝ, Continuous g →
      Integrable (fun x => Torus.mode (-k) x * (g x : ℂ)) := by
    intro g hg
    have : Continuous (fun x => Torus.mode (-k) x * (g x : ℂ)) :=
      (Torus.continuous_mode (-k)).mul (Complex.continuous_ofReal.comp hg)
    exact this.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hfz : Continuous (fun x => f (x + z)) := hf.comp (continuous_id.add continuous_const)
  rw [coeffOf_eq_fcoefC, coeffOf_eq_fcoefC]
  unfold Torus.fcoef
  have e : ∀ x, Torus.mode (-k) x * (((f (x + z) - f x : ℝ)) : ℂ) =
      Torus.mode (-k) x * (f (x + z) : ℂ) - Torus.mode (-k) x * (f x : ℂ) := fun x => by
    push_cast; ring
  simp_rw [e]
  rw [integral_sub (hc _ hfz) (hc _ hf)]
  have := Torus.fcoef_translate f k z
  unfold Torus.fcoef at this
  rw [this]
  ring

/-- Translation estimate: `int |f(x + z) - f(x)|^2 <= tdist(z,0)^2 ||f||^2_{H^1}`. -/
theorem s7b_shift_L2 {f : Torus d → ℝ} (hf : Continuous f) (hm : MemHs (1 : ℝ) (coeffOf f))
    (z : Torus d) :
    ∫ x, (f (x + z) - f x) ^ 2 ≤ ‖Torus.centeredRep z‖ ^ 2 * hsNormSq (1 : ℝ) (coeffOf f) := by
  have hfz : Continuous (fun x => f (x + z) - f x) :=
    (hf.comp (continuous_id.add continuous_const)).sub hf
  rw [← parseval_real hfz]
  unfold hsNormSq
  set c := Torus.centeredRep z with hcdef
  have hz : z = Torus.mk c := (HRS.PDE.R2Aux.mk_centeredRep z).symm
  have hpt : ∀ k : Lattice d, sobWeight (0 : ℝ) k * ‖coeffOf (fun x => f (x + z) - f x) k‖ ^ 2 ≤
      ‖c‖ ^ 2 * (sobWeight (1 : ℝ) k * ‖coeffOf f k‖ ^ 2) := by
    intro k
    rw [s7b_coeff_shift hf z k, norm_mul]
    have h0 : sobWeight (0 : ℝ) k = 1 := by simp [sobWeight]
    have h1 : sobWeight (1 : ℝ) k = 1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 := by
      simp [sobWeight]
    rw [h0, h1, one_mul, mul_pow]
    have hmod : ‖Torus.mode k z - 1‖ ≤ 2 * Real.pi * Lattice.enorm k * ‖c‖ := by
      rw [hz, Torus.mode_mk]
      have : Complex.exp (((2 * Real.pi * Lattice.dot k c : ℝ) : ℂ) * Complex.I) =
          Complex.exp (Complex.I * ((2 * Real.pi * Lattice.dot k c : ℝ) : ℂ)) := by
        rw [mul_comm]
      rw [this]
      refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_pos Real.pi_pos]
      have := Torus.abs_dot_le k c
      calc 2 * Real.pi * |Lattice.dot k c| ≤ 2 * Real.pi * (Lattice.enorm k * ‖c‖) := by gcongr
        _ = _ := by ring
    have hmod2 : ‖Torus.mode k z - 1‖ ^ 2 ≤ (2 * Real.pi * Lattice.enorm k * ‖c‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hmod 2
    have hen : 0 ≤ ‖coeffOf f k‖ ^ 2 := sq_nonneg _
    calc ‖Torus.mode k z - 1‖ ^ 2 * ‖coeffOf f k‖ ^ 2
        ≤ (2 * Real.pi * Lattice.enorm k * ‖c‖) ^ 2 * ‖coeffOf f k‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hmod2 hen
      _ = ‖c‖ ^ 2 * (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 * ‖coeffOf f k‖ ^ 2) := by ring
      _ ≤ ‖c‖ ^ 2 * ((1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) * ‖coeffOf f k‖ ^ 2) := by
          gcongr
          linarith
  have hsum1 : Summable fun k : Lattice d => ‖c‖ ^ 2 * (sobWeight (1 : ℝ) k * ‖coeffOf f k‖ ^ 2) :=
    hm.mul_left _
  have hnn : ∀ k : Lattice d, 0 ≤ sobWeight (0 : ℝ) k * ‖coeffOf (fun x => f (x + z) - f x) k‖ ^ 2 :=
    fun k => mul_nonneg (MFProduct.sobWeight_nonneg _ k) (sq_nonneg _)
  have hsum0 : Summable fun k : Lattice d =>
      sobWeight (0 : ℝ) k * ‖coeffOf (fun x => f (x + z) - f x) k‖ ^ 2 :=
    Summable.of_nonneg_of_le hnn hpt hsum1
  calc ∑' k : Lattice d, sobWeight (0 : ℝ) k * ‖coeffOf (fun x => f (x + z) - f x) k‖ ^ 2
      ≤ ∑' k : Lattice d, ‖c‖ ^ 2 * (sobWeight (1 : ℝ) k * ‖coeffOf f k‖ ^ 2) :=
        hsum0.tsum_le_tsum hpt hsum1
    _ = ‖c‖ ^ 2 * ∑' k : Lattice d, sobWeight (1 : ℝ) k * ‖coeffOf f k‖ ^ 2 := tsum_mul_left

end HRS.MC.Sec7.S7b

end
