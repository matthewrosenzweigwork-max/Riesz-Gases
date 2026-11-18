import HRS.Uniform.Q54Aux19
import HRS.Uniform.Q54Aux20

/-!
# Q54, part 21: the coefficient hypotheses `GenHyp` for the mean-field data of Proposition 5.1

For `FiniteRegHyp d s βm βp K V ρ₀` and every solution `ρc` (`IsMFSolutionHK`), the generator data `(mfData, mfPath ρc t)`
satisfies `GenHyp d s K 1 Bμ BV` for all `t ≥ 0`, with `Bμ, BV` depending on the data of Proposition 5.1 only
(uniform bound `‖ρ^t‖_{H^K} ≤ C` and the Fourier decay of `V ∈ C^{K+2}`).
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q54

open HRS HRS.PDE HRS.PDE.ET

variable {d : ℕ}

theorem jp_zero : Lattice.jp (0 : Lattice d) = 1 := by
  have h : Lattice.toEuc (0 : Lattice d) = 0 := by
    ext i; simp [Lattice.toEuc]
  simp [Lattice.jp, Lattice.enorm, h]

theorem coeff_decay_V (V : Torus d → ℝ) (n : ℕ) (hV : Torus.IsCk (n : WithTop ℕ∞) V) :
    ∃ BV : ℝ, 0 ≤ BV ∧ ∀ m : Lattice d, ‖coeffOf V m‖ ≤ BV * Lattice.jp m ^ (-(n : ℝ)) := by
  set c0 : ℝ := Torus.cbNorm n V with hc0
  have hc00 : 0 ≤ c0 := R2Aux.cbNorm_nonneg' n V
  set c1 : ℝ := ((1 + 2 * Real.pi) / (2 * Real.pi)) ^ n with hc1
  have hc10 : 0 ≤ c1 := by positivity
  refine ⟨c0 * c1 + c0, by positivity, fun m => ?_⟩
  by_cases hm : m = 0
  · subst hm
    have h1 : ‖coeffOf V 0‖ ≤ c0 := by
      rw [coeffOf_eq_fcoef]
      exact Torus.norm_fcoef_le_of_bound (fun x => R2Aux.abs_le_cbNorm hV x) 0
    rw [jp_zero, Real.one_rpow, mul_one]
    nlinarith [mul_nonneg hc00 hc10]
  · have h1 := coeffOf_decay V hV m hm
    have hj := Torus.jp_pos m
    have e : Lattice.jp m ^ (-(n : ℝ)) = (Lattice.jp m ^ n)⁻¹ := by
      rw [Real.rpow_neg hj.le, Real.rpow_natCast]
    rw [e, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    calc ‖coeffOf V m‖ * Lattice.jp m ^ n ≤ c0 * c1 := h1
      _ ≤ (c0 * c1 + c0) := by linarith

theorem sqrt_sobWeight_eq (K : ℝ) (m : Lattice d) : Real.sqrt (sobWeight K m) = Lattice.jp m ^ K := by
  rw [sobWeight_eq_jp, ← Real.sqrt_sq (Real.rpow_nonneg (Torus.jp_pos m).le K)]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Torus.jp_pos m).le]
  push_cast; ring_nf

theorem genHyp_of_mf (hd : 1 ≤ d) (s βm βp : ℝ) (K : ℕ) (V ρ₀ : Torus d → ℝ)
    (H : FiniteRegHyp d s βm βp K V ρ₀) :
    ∃ Bμ BV : ℝ, 0 ≤ Bμ ∧ 0 ≤ BV ∧ ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρc : ℝ → Coeff d),
      IsMFSolutionHK d s V β⁻¹ K ρ₀ ρc → ∀ t : ℝ, 0 ≤ t →
        GenHyp d s (K : ℝ) 1 Bμ BV (mfData d s H.hs0 H.hsd V β (H.hβm.trans_le hβ.1))
          (mfPath ρc t) := by
  obtain ⟨cU, CU, hcU, hU⟩ := finite_reg_uniform_bounds hd s βm βp K V ρ₀ H
  obtain ⟨BV, hBV0, hBV⟩ := coeff_decay_V V (K + 1)
    (H.hV.of_le (by exact_mod_cast (by omega : K + 1 ≤ K + 2)))
  have hKd : (d : ℝ) / 2 < K := by linarith [H.hK]
  refine ⟨max CU 0, BV, le_max_right _ _, hBV0, fun β hβ ρc hρc t ht => ⟨rfl, ?_, ?_, ?_⟩⟩
  · intro i j
    show |(-1 : Matrix (Fin d) (Fin d) ℝ) i j| ≤ 1
    rw [Matrix.neg_apply, Matrix.one_apply]
    split_ifs <;> norm_num
  · intro m
    have hreal := MFGlobal.isRealCoeff_of_isMFSolutionHK hd s βm βp K V ρ₀ H β hβ ρc hρc
    have hMemK : MemHs (K : ℝ) (ρc t) := hρc.cont.1 t ht
    have hsumK : Summable fun k => ‖ρc t k‖ := summable_norm_of_memHs (K : ℝ) hKd _ hMemK
    have hcoef : coeffOf (mfPath ρc t) = ρc t := coeffOf_toFun (ρc t) (hreal t ht) hsumK
    rw [hcoef]
    have h1 := MFApriori.norm_coeff_le_hsNorm (K : ℝ) hMemK m
    rw [sqrt_sobWeight_eq] at h1
    have h2 : HRS.PDE.hsNorm (K : ℝ) (ρc t) ≤ max CU 0 :=
      ((hU β hβ ρc hρc t ht).2).trans (le_max_left _ _)
    have hj := Torus.jp_pos m
    have e : Lattice.jp m ^ (-(K : ℝ)) = (Lattice.jp m ^ (K : ℝ))⁻¹ := Real.rpow_neg hj.le _
    rw [e, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hj _)]
    exact h1.trans h2
  · intro m
    have := hBV m
    simpa [mfData] using this

end HRS.Uniform.Q54
