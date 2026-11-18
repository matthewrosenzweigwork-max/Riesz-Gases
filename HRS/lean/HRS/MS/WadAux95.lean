import HRS.MS.WadAux94

/-!
# S8.3, packet S8E-5, part 6: clause (4a) of the frozen `weighted_adjoint_decay`

`s8e_tensor_pt`: pointwise bound for the iterated action `U_t[x' ↦ U_t(R x')(y)](x)` on a doubly centered pair
(`U_t = s85_Ulim`): the inner action decays by clause (2a), and so does the outer one up to the mean, which is bounded
by the first moment of the inner action.  `s8e_clause4a`: the fifth conjunct of the frozen statement (for every
`IsWeightedSemigroup` `U`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8e_tensor_pt (hd : 2 ≤ d) {a β M : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) (hMpos : 0 < M) {Cd c : ℝ} (hCd : 0 ≤ Cd)
    (h2a : S8e2a a β M ρβ Cd c) {R : Euc d → Euc d → ℝ} (hR : MemCMpair M 0 R)
    (hdc : IsDoublyCentered (HRS.Whole.withDensityReal ρβ) R) {N0 : ℝ} (hN0 : ∀ z, |s8e_Qa M R z| ≤ N0)
    {t : ℝ} (ht : 1 ≤ t) (x y : Euc d) :
    |s85_Ulim a β ρβ M t (fun x' => s85_Ulim a β ρβ M t (R x') y) x| ≤
      Cd * Real.exp (-c * t) * (Cd * Real.exp (-c * t) +
        (∫ z, jbracket z ^ M ∂(HRS.Whole.withDensityReal ρβ))) * N0 * jbracket x ^ M * jbracket y ^ M := by
  have hM := hMpos.le
  have hP : HRS.Whole.IsProbDensity ρβ := hρ.1.1
  have hg : s84_GaussReg ρβ := s84_thermal_gaussReg hd ha hβ hρ
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρβ) := s85_isProb hP
  set G : Euc d → ℝ := fun x' => s85_Ulim a β ρβ M t (R x') y with hGdef
  have hG : MemCM M G := s8e_G_cm hd ha hβ hρ hMpos hCd h2a hR hdc ht y
  have hN00 : 0 ≤ N0 := (abs_nonneg _).trans (hN0 (0, 0))
  set B : ℝ := Cd * Real.exp (-c * t) * N0 * jbracket y ^ M with hB
  have hE0 : 0 ≤ Cd * Real.exp (-c * t) := mul_nonneg hCd (Real.exp_pos _).le
  have hjy := Real.rpow_nonneg (s83_jb_pos y).le M
  have hjx := Real.rpow_nonneg (s83_jb_pos x).le M
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hwt : Wt M B G := fun x' => by
    rw [Real.norm_eq_abs]
    refine (s8e_G_bound hd ha hβ hρ hMpos h2a hR hdc hN0 ht x' y).trans (le_of_eq ?_)
    rw [hB]; ring
  have hdec := s8e_Ulim_projMean hd ha hβ hρ hMpos ht hG x
  have h1 := h2a ht hG hwt x
  have hint : Integrable (fun z => jbracket z ^ M) (HRS.Whole.withDensityReal ρβ) :=
    s85_jb_integrable hP hg hM
  have hm0 : 0 ≤ ∫ z, jbracket z ^ M ∂(HRS.Whole.withDensityReal ρβ) :=
    integral_nonneg fun z => Real.rpow_nonneg (s83_jb_pos z).le _
  have h2 : |HRS.Whole.pair (HRS.Whole.withDensityReal ρβ) G| ≤
      B * (∫ z, jbracket z ^ M ∂(HRS.Whole.withDensityReal ρβ)) := by
    unfold HRS.Whole.pair
    rw [← Real.norm_eq_abs, ← integral_const_mul]
    exact norm_integral_le_of_norm_le (hint.const_mul B) (Eventually.of_forall fun z => hwt z)
  rw [hdec]
  refine (abs_add_le _ _).trans ?_
  have hjx1 : 1 ≤ jbracket x ^ M := Real.one_le_rpow (s83_one_le_jb x) hM
  set m : ℝ := ∫ z, jbracket z ^ M ∂(HRS.Whole.withDensityReal ρβ) with hm
  calc _ ≤ Cd * Real.exp (-c * t) * B * jbracket x ^ M + B * m := add_le_add h1 h2
    _ ≤ Cd * Real.exp (-c * t) * B * jbracket x ^ M + B * m * jbracket x ^ M := by
        have := mul_le_mul_of_nonneg_left hjx1 (mul_nonneg hB0 hm0)
        nlinarith
    _ = _ := by rw [hB]; ring

end HRS.MS.Wad
