import HRS.Commutator.Torus.TSAMPAux14

/-!
# T-SAMP helpers, part 15: `vhi_Lp_T` (assembly)
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s : ℝ}

lemma tsamp_bessel_alg {α η : ℝ} (hη : 0 < η) (hα : 0 < α) (k : Lattice d) (V Wh : ℂ)
    (hW : Wh = (((2 * Real.pi * Lattice.enorm k) ^ α : ℝ) : ℂ) * V) :
    ((η ^ α : ℝ) : ℂ) * (Wh - ((Whole.chi (η • Lattice.toEuc k) : ℝ) : ℂ) * Wh +
        ((((1 + 4 * Real.pi ^ 2 * ‖η • Lattice.toEuc k‖ ^ 2) ^ (α / 2) *
          ((1 - Whole.chi (η • Lattice.toEuc k)) * (2 * Real.pi * ‖η • Lattice.toEuc k‖) ^ (-α)) : ℝ) : ℂ) -
          (((1 - Whole.chi (η • Lattice.toEuc k) : ℝ)) : ℂ)) * Wh) =
      ((((1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2) ^ (α / 2) : ℝ)) : ℂ) *
        ((1 - ((Whole.chi (η • Lattice.toEuc k) : ℝ) : ℂ)) * V) := by
  by_cases hk : k = 0
  · subst hk
    have h0 : Lattice.toEuc (0 : Lattice d) = 0 := by ext i; simp [Lattice.toEuc]
    have he : Lattice.enorm (0 : Lattice d) = 0 := text_enorm_zero
    have hc : Whole.chi (η • Lattice.toEuc (0 : Lattice d)) = 1 := by
      rw [h0, smul_zero]; exact Whole.cmxFB_chi_one (by simp)
    rw [hW, he, hc]
    simp [Real.zero_rpow hα.ne']
  · have hen : 0 < Lattice.enorm k := by
      have := HRS.one_le_enorm k hk
      linarith
    have hn : ‖η • Lattice.toEuc k‖ = η * Lattice.enorm k := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη]; rfl
    set χ : ℝ := Whole.chi (η • Lattice.toEuc k) with hχ
    set u : ℝ := 2 * Real.pi * Lattice.enorm k with hu
    have hupos : 0 < u := by rw [hu]; positivity
    have hreal : η ^ α * ((1 + 4 * Real.pi ^ 2 * (η * Lattice.enorm k) ^ 2) ^ (α / 2) *
        ((1 - χ) * (2 * Real.pi * (η * Lattice.enorm k)) ^ (-α))) * u ^ α =
        (1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2) ^ (α / 2) * (1 - χ) := by
      have e1 : 2 * Real.pi * (η * Lattice.enorm k) = η * u := by rw [hu]; ring
      have e2 : (1 + 4 * Real.pi ^ 2 * (η * Lattice.enorm k) ^ 2) =
          1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2 := by ring
      rw [e1, e2, Real.mul_rpow hη.le hupos.le]
      have h3 : η ^ α * η ^ (-α) = 1 := by rw [← Real.rpow_add hη]; simp
      have h4 : u ^ (-α) * u ^ α = 1 := by rw [← Real.rpow_add hupos]; simp
      calc η ^ α * ((1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2) ^ (α / 2) *
            ((1 - χ) * (η ^ (-α) * u ^ (-α)))) * u ^ α
          = (1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2) ^ (α / 2) * (1 - χ) *
              ((η ^ α * η ^ (-α)) * (u ^ (-α) * u ^ α)) := by ring
        _ = _ := by rw [h3, h4]; ring
    rw [hn, hW]
    have hc : (((η ^ α : ℝ) : ℂ)) * ((((1 + 4 * Real.pi ^ 2 * (η * Lattice.enorm k) ^ 2) ^ (α / 2) *
          ((1 - χ) * (2 * Real.pi * (η * Lattice.enorm k)) ^ (-α)) : ℝ) : ℂ)) *
          (((u ^ α : ℝ)) : ℂ) =
        ((((1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2) ^ (α / 2) * (1 - χ) : ℝ)) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, hreal]
    push_cast at hc ⊢
    linear_combination (V) * hc

end HRS.Commutator.TorusNote
