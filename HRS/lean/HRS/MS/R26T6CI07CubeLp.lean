import HRS.MS.R26T6CI07Centered

/-!
# S11.1 I07: exact L3 criterion from integrable cubic modulus.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace HRS.MS.R26T6C
open HRS
variable {d : ℕ}

theorem r26t6c_memLp_three_of_integrable_cube
    (mu : Measure (Euc d)) (f : Euc d → ℝ)
    (hf : Measurable f)
    (hi : Integrable (fun x => |f x| ^ 3) mu) :
    MemLp f 3 mu := by
  rw [memLp_iff]
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num : (3 : ENNReal) ≠ 0)
    (by norm_num : (3 : ENNReal) ≠ ⊤)
    hf.aestronglyMeasurable).2
  have hpt : ∀ x : Euc d, ‖f x‖ₑ ^ (3 : ENNReal).toReal =
      ENNReal.ofReal (|f x| ^ 3) := by
    intro x
    rw [Real.enorm_eq_ofReal_abs]
    simp only [ENNReal.toReal_ofNat]
    calc
      _ = (ENNReal.ofReal |f x|) ^ (3 : ℕ) := by
        simpa using (ENNReal.rpow_natCast (ENNReal.ofReal |f x|) 3)
      _ = _ := (ENNReal.ofReal_pow (abs_nonneg (f x)) 3).symm
  simp_rw [hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => by positivity)]
  exact ENNReal.ofReal_lt_top

end HRS.MS.R26T6C
