import HRS.MS.R26T8AC07d

/-!
# S8.2 observed-time layer, packet T8A.C07e: the outer integral of the threefold bound

`∫⁻ ρ(z) q(x-z) (1 + |log min(1,‖z-y‖)|) dz ≤ C3` uniformly in `x, y`: `q ≤ A + K`, `|log min(1,r)| ≤ (4/d) r^{-d/4} 1_{r ≤ 1}`;
the terms are a radial integral of `A`, the two-centre integral with exponents `(d/2, d/4)` when `‖x-y‖ < 2` (and `0` otherwise),
the mass of `ρ`, and a radial integral of `r^{-d/4} 1_{r≤1}`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_c07e_Lbound (d : ℕ) (hd : 1 ≤ d) (u : Euc d) :
    ENNReal.ofReal (|Real.log (min 1 ‖u‖)|) ≤ ENNReal.ofReal (4 / d) *
      ENNReal.ofReal ((Set.Ioc 0 1).indicator (fun r => r ^ (-((d : ℝ) / 4))) ‖u‖) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  set θ : ℝ := (d : ℝ) / 4 with hθ
  have hθ0 : 0 < θ := by positivity
  by_cases h0 : ‖u‖ = 0
  · rw [h0]; simp
  have hpos : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg u) (Ne.symm h0)
  by_cases h1 : ‖u‖ ≤ 1
  · rw [indicator_of_mem (show ‖u‖ ∈ Set.Ioc 0 1 from ⟨hpos, h1⟩), min_eq_right h1,
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hl : Real.log ‖u‖ ≤ 0 := Real.log_nonpos hpos.le h1
    rw [abs_of_nonpos hl, ← Real.log_inv]
    have := Real.log_le_rpow_div (inv_pos.2 hpos).le hθ0
    rw [Real.inv_rpow hpos.le, ← Real.rpow_neg hpos.le] at this
    calc Real.log ‖u‖⁻¹ ≤ ‖u‖ ^ (-θ) / θ := this
      _ = 4 / d * ‖u‖ ^ (-θ) := by rw [hθ]; field_simp
  · push_neg at h1
    rw [min_eq_left h1.le, Real.log_one, abs_zero, ENNReal.ofReal_zero]
    exact zero_le

theorem r26t8a_c07e_radialA (d : ℕ) (hd : 1 ≤ d) {r0 : ℝ} (hr0 : 0 < r0) (hr01 : r0 ≤ 1) :
    ∫⁻ w : Euc d, ENNReal.ofReal ((Set.Ioc 0 r0).indicator (fun r => r ^ (-((d : ℝ) / 2))) ‖w‖) ≤
      ENNReal.ofReal (r26t8a_c08a_const d * (1 / ((d : ℝ) / 2))) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  set e : ℝ := (d : ℝ) / 2 with he
  have he0 : 0 < e := by positivity
  have := r26t8a_c08a_radial d hd (p := e) (ε := 0) (δ := r0) le_rfl hr0.le
    (Or.inr (by rw [he]; linarith))
  have hex : (d : ℝ) - 1 - e + 1 = e := by rw [he]; ring
  have hI : ∫ r in (0 : ℝ)..r0, r ^ ((d : ℝ) - 1 - e) = r0 ^ e / e := by
    rw [integral_rpow (Or.inl (by rw [he]; linarith)), hex, Real.zero_rpow he0.ne']; simp
  rw [hI] at this
  refine this.trans_le (ENNReal.ofReal_le_ofReal ?_)
  have h1 : r0 ^ e ≤ 1 := Real.rpow_le_one hr0.le hr01 he0.le
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h1 he0.le)
    (r26t8a_c08a_const_nonneg d)

theorem r26t8a_c07e_radialL (d : ℕ) (hd : 1 ≤ d) :
    ∫⁻ w : Euc d, ENNReal.ofReal ((Set.Ioc 0 1).indicator (fun r => r ^ (-((d : ℝ) / 4))) ‖w‖) ≤
      ENNReal.ofReal (r26t8a_c08a_const d * (1 / ((d : ℝ) - (d : ℝ) / 4))) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  set θ : ℝ := (d : ℝ) / 4 with hθ
  have := r26t8a_c08a_radial d hd (p := θ) (ε := 0) (δ := 1) le_rfl zero_le_one
    (Or.inr (by rw [hθ]; linarith))
  have hex : (d : ℝ) - 1 - θ + 1 = (d : ℝ) - θ := by ring
  have hI : ∫ r in (0 : ℝ)..1, r ^ ((d : ℝ) - 1 - θ) = 1 / ((d : ℝ) - θ) := by
    rw [integral_rpow (Or.inl (by rw [hθ]; linarith)), hex, Real.one_rpow,
      Real.zero_rpow (by rw [hθ]; linarith)]
    simp
  rw [hI] at this
  exact this.le

end HRS.MS.R26T8A
