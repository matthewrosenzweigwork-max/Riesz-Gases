import HRS.MS.S113EndAux19
import HRS.MS.MfeConfAux60
import HRS.MS.SuppA0Aux2

/-!
# S11.3 endpoint (worker S11X), part 20: the S.B.1 trajectory bundle `Sb1Tr3` of a Gaussian-bounded mean-field solution

`s113x_tr3_of_gauss`: a family of positive probability densities `ρ_t`, solving the whole-space mean-field equation of
`quadraticGradientDyn d s q β` on `[0,T]`, with `‖D^k ρ_t(y)‖ ≤ B e^{-c‖y‖²}` for `k ≤ 3`, is an `Sb1Tr3` (decay `(1+|y|)^{-(d+3)}`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113BD

open HRS HRS.Whole

variable {d : ℕ}

theorem s113x_gauss_le_pow {c : ℝ} (hc : 0 < c) (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : Euc d, Real.exp (-c * ‖x‖ ^ 2) ≤ K * (1 + ‖x‖) ^ (-(N : ℝ)) := by
  obtain ⟨K, hK0, hK⟩ := HRS.MS.Mov63.mnc_gauss_poly hc N
  refine ⟨K, hK0, fun x => ?_⟩
  have hpos : 0 < (1 + ‖x‖) := by positivity
  have h := hK ‖x‖ (norm_nonneg _)
  rw [Real.rpow_neg hpos.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  linarith

theorem s113x_weightedSupE_lt_top (hd : 1 ≤ d) {c B : ℝ} (hc : 0 < c) (hB : 0 ≤ B) {f : Euc d → ℝ}
    (hg : ∀ k ≤ 3, ∀ y, ‖iteratedFDeriv ℝ k f y‖ ≤ B * Real.exp (-c * ‖y‖ ^ 2)) :
    weightedSupE 3 ((d : ℝ) + 3) f < ⊤ := by
  obtain ⟨K1, hK1, hK⟩ := HRS.MS.Mov63.mnc_gauss_poly hc (d + 3)
  refine lt_of_le_of_lt (b := ENNReal.ofReal (B * K1)) ?_ ENNReal.ofReal_lt_top
  unfold weightedSupE derivSupE
  refine iSup_le fun j => iSup_le fun i => iSup_le fun x => ENNReal.ofReal_le_ofReal ?_
  simp only
  have hjb : jbracket x ≤ 1 + ‖x‖ := by
    unfold jbracket
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [norm_nonneg x]
  have hj0 : 0 ≤ jbracket x := Real.sqrt_nonneg _
  have hpow : jbracket x ^ ((d : ℝ) + 3) ≤ (1 + ‖x‖) ^ (d + 3) := by
    have : jbracket x ^ ((d : ℝ) + 3) = jbracket x ^ (d + 3) := by
      rw [← Real.rpow_natCast]; push_cast; rfl
    rw [this]
    exact pow_le_pow_left₀ hj0 hjb _
  have hpd : |partialDeriv i f x| ≤ B * Real.exp (-c * ‖x‖ ^ 2) := by
    unfold partialDeriv
    rw [← Real.norm_eq_abs]
    refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
    have : ∏ l : Fin (j : ℕ), ‖(EuclideanSpace.single (i l) (1 : ℝ) : Euc d)‖ = 1 := by simp
    rw [this, mul_one]
    exact hg j (by omega) x
  calc jbracket x ^ ((d : ℝ) + 3) * |partialDeriv i f x| ≤ (1 + ‖x‖) ^ (d + 3) * (B * Real.exp (-c * ‖x‖ ^ 2)) :=
        mul_le_mul hpow hpd (abs_nonneg _) (by positivity)
    _ = B * ((1 + ‖x‖) ^ (d + 3) * Real.exp (-c * ‖x‖ ^ 2)) := by ring
    _ ≤ B * K1 := mul_le_mul_of_nonneg_left (hK ‖x‖ (norm_nonneg _)) hB


theorem s113x_tr3_of_gauss (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (q β : ℝ) {T c B : ℝ} (hc : 0 < c)
    (hB : 0 ≤ B) {ρ : ℝ → Euc d → ℝ} (hmf : IsWholeMeanFieldSolution (quadraticGradientDyn d s q β) T ρ)
    (hpos : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ y, 0 < ρ t y) (hcd : ∀ t ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ 3 (ρ t))
    (hg : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k ≤ 3, ∀ y, ‖iteratedFDeriv ℝ k (ρ t) y‖ ≤ B * Real.exp (-c * ‖y‖ ^ 2)) :
    ∃ C Bp C3 : ℝ, MfeConf.Sb1Tr3 (quadraticGradientDyn d s q β) T C Bp C3 ρ := by
  obtain ⟨K1, hK1, hK1'⟩ := s113x_gauss_le_pow (d := d) hc (d + 1)
  obtain ⟨K3, hK3, hK3'⟩ := s113x_gauss_le_pow (d := d) hc (d + 3)
  obtain ⟨ΛV, hV⟩ := HRS.MS.A0.a0_vhyp (d := d) q
  have hV3 : MfeConf.Sb1Pot (quadraticGradientDyn d s q β).V ΛV :=
    ⟨(contDiff_infty.1 hV.1) 3, fun x => hV.2.1 2 le_rfl le_rfl x⟩
  have hexp1 : ∀ y : Euc d, Real.exp (-c * ‖y‖ ^ 2) ≤ 1 := fun y =>
    Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖y‖])
  have hslice : ∀ r ∈ Set.Icc (0 : ℝ) T, MfeConf.Sb1Slice d (B * K1) (ρ r) := fun r hr => by
    refine ⟨hmf.density r hr, ⟨hcd r hr, fun l hl y => ?_⟩, by positivity⟩
    refine (hg r hr l hl y).trans ?_
    have := mul_le_mul_of_nonneg_left (hK1' y) hB
    have e : ((d + 1 : ℕ) : ℝ) = (d : ℝ) + 1 := by push_cast; ring
    rw [e] at this
    simpa [mul_assoc] using this
  refine ⟨B * K1, ΛV, B * K3, ?_⟩
  refine ⟨⟨by positivity, hd, hs0, hsd, rfl, hV3, hmf, hslice, fun r hr => ⟨hmf.density r hr, ⟨hcd r hr, fun j hj => ?_⟩,
    s113x_weightedSupE_lt_top hd hc hB (hg r hr)⟩⟩, fun r hr l hl y => ?_, hpos, by positivity⟩
  · refine ⟨B, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (hg r hr j hj x).trans (mul_le_of_le_one_right hB (hexp1 x))
  · refine (hg r hr l (by omega) y).trans ?_
    have := mul_le_mul_of_nonneg_left (hK3' y) hB
    have e : ((d + 3 : ℕ) : ℝ) = (d : ℝ) + 3 := by push_cast; ring
    rw [e] at this
    simpa [MfeConf.sb1w, mul_assoc] using this

end HRS.MS.S113BD

end
