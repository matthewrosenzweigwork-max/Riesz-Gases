import HRS.Commutator.Torus.TEXTAux5

/-!
# T-EXT-A helpers, part 6: `mult_kernel_T`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

lemma text_cRep_norm_le (c : Euc d) (hc : ∀ i, |c i| ≤ 1 / 2) : ‖c‖ ≤ d / 2 := by
  have h1 := Whole.cmxHLS_norm_toLp_le (d := d) (fun i => c i)
  have h2 : (WithLp.toLp 2 (fun i => c i) : Euc d) = c := rfl
  rw [h2] at h1
  refine h1.trans ?_
  calc ∑ i, |c i| ≤ ∑ _i : Fin d, (1 / 2 : ℝ) := Finset.sum_le_sum fun i _ => hc i
    _ = d / 2 := by simp; ring

lemma text_mk_ne_zero_of_ne {c : Euc d} (hc : c ≠ 0) (hc2 : ∀ i, |c i| ≤ 1 / 2) :
    Torus.mk c ≠ 0 := by
  intro h
  apply hc
  ext i
  have h1 : (Torus.mk c) i = 0 := by rw [h]; rfl
  have h2 : ‖((c i : ℝ) : UnitAddCircle)‖ = |c i| := by
    rw [AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero]
    simpa using hc2 i
  have h3 : ((c i : ℝ) : UnitAddCircle) = 0 := h1
  rw [h3, norm_zero] at h2
  have := abs_eq_zero.1 h2.symm
  simpa using this

/-- Key identity: the Fourier symbol of the rescaled kernel. -/
lemma text_symbol_scale {γ η : ℝ} (hγ : γ ≠ 0) (hη : 0 < η) (k : Lattice d) :
    ((η ^ γ : ℝ) : ℂ) *
        (((1 - Whole.chi (η • Lattice.toEuc k)) * (2 * Real.pi * ‖η • Lattice.toEuc k‖) ^ (-γ) : ℝ) : ℂ) =
      ((if k = 0 then 0 else
            (1 - Whole.chi (η • Lattice.toEuc k)) * (2 * Real.pi * Lattice.enorm k) ^ (-γ) : ℝ) : ℂ) := by
  by_cases hk : k = 0
  · subst hk
    have h0 : Lattice.toEuc (0 : Lattice d) = 0 := by ext i; simp [Lattice.toEuc]
    simp [h0, Real.zero_rpow (neg_ne_zero.2 hγ)]
  · simp only [hk, ite_false]
    rw [← Complex.ofReal_mul]
    congr 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη]
    unfold Lattice.enorm
    have hη1 : (0 : ℝ) ≤ 2 * Real.pi * ‖Lattice.toEuc k‖ := by positivity
    have : 2 * Real.pi * (η * ‖Lattice.toEuc k‖) = η * (2 * Real.pi * ‖Lattice.toEuc k‖) := by ring
    rw [this, Real.mul_rpow hη.le hη1]
    have e : η ^ γ * η ^ (-γ) = 1 := by rw [← Real.rpow_add hη]; simp
    linear_combination ((1 - Whole.chi (η • Lattice.toEuc k)) *
      (2 * Real.pi * ‖Lattice.toEuc k‖) ^ (-γ)) * e

end HRS.Commutator.TorusNote
