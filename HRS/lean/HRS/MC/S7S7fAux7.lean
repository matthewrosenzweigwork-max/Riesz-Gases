import HRS.MC.S7S7fAux6

/-!
# Packet S7f, helper 7: the bias term `R1` is `O(N^{-1/2})` uniformly over the unit ball
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7f

open HRS HRS.Sec7 HRS.MC.SEdge HRS.StaticLimitAux HRS.MC.Sec7.S7d HRS.MC.Sec7.S7c

variable {d : ℕ} {s : ℝ} {r : ℝ}

theorem s7f_R1_bound (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hr : r = 2 * (d : ℝ) + 6)
    {γ : ℝ} (hγ : 0 ≤ γ) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
    {a : NonzeroLattice d → Torus d → ℝ} {v : NonzeroLattice d → Fin d → Torus d → ℝ} {C₀ : ℝ}
    (hmode : s7_ModeData d s γ ρ r a v C₀)
    (G : Measure (NegSobolev d r)) [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianWithCov r G fun φ ψ =>
      ∫ x, φ x * responseRep (periodicRiesz d s) (withDensityReal ρ) γ ψ x ∂(withDensityReal ρ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N → ∀ Φ ∈ CbUnitBall (NegSobolev d r) 5,
      |∑' k : NonzeroLattice d, ∑' l : NonzeroLattice d, Real.sqrt N * (s7_Cmode r ρ a l k -
            ∫ X, sed_A (v k) (s7_phi r l) X ∂(sed_Q d s N γ ρ)) *
          ∫ X, iteratedFDeriv ℝ 2 (steinSolG G Φ) (zetaE r (sed_Q d s N γ ρ) X)
            ![s7_eps r k, s7_eps r l] ∂(sed_Q d s N γ ρ)| ≤ K / Real.sqrt N := by
  have hb := s7d_b_summable (d := d)
  have hb0 := s7f_b_nonneg (d := d)
  obtain ⟨CB, hCB⟩ := HRS.MC.Sec7.S7b.s7_S7b_weighted_moments_proof hd hs0 hs r hr hγ hρ hmode 1
  have hS2 : 0 ≤ ∑' p : NonzeroLattice d × NonzeroLattice d, s7_b p.1 * s7_b p.2 :=
    tsum_nonneg fun p => mul_nonneg (hb0 _) (hb0 _)
  refine ⟨|CB| * ∑' p : NonzeroLattice d × NonzeroLattice d, s7_b p.1 * s7_b p.2,
    mul_nonneg (abs_nonneg _) hS2, fun N hN Φ hΦ => ?_⟩
  have hr' : (d : ℝ) < 2 * r := by rw [hr]; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hQ : IsProbabilityMeasure (sed_Q d s N γ ρ) :=
    HRS.MC.SEdge.B4b.b4b_isProb hd hs0 hs hγ hρ N hN
  have hNpos : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hNr : (N : ℝ) = Real.sqrt N * Real.sqrt N := (Real.mul_self_sqrt (Nat.cast_nonneg N)).symm
  have hcl : s7d_Cl (steinSolG G Φ) := s7d_stein_cl G hG.1 hΦ
  have hWm := s7c_zeta_meas hN hr' (sed_Q d s N γ ρ)
  set Q := sed_Q d s N γ ρ with hQdef
  set sN := Real.sqrt N with hsN
  have hM1 : ∀ k l : NonzeroLattice d,
      |∫ X, iteratedFDeriv ℝ 2 (steinSolG G Φ) (zetaE r Q X) ![s7_eps r k, s7_eps r l] ∂Q| ≤ 1 := by
    intro k l
    refine s7f_abs_integral_le _ (fun X => ?_)
    have := s7d_D2_bound (hcl.2 2 (by norm_num) (by norm_num) (zetaE r Q X)) (s7_eps r k) (s7_eps r l)
    rwa [HRS.MC.Sec7.S7e.s7e_eps_norm, HRS.MC.Sec7.S7e.s7e_eps_norm, mul_one] at this
  have hterm : ∀ k l : NonzeroLattice d, |sN * (s7_Cmode r ρ a l k -
        ∫ X, sed_A (v k) (s7_phi r l) X ∂Q) *
      ∫ X, iteratedFDeriv ℝ 2 (steinSolG G Φ) (zetaE r Q X) ![s7_eps r k, s7_eps r l] ∂Q| ≤
      (|CB| / sN) * (s7_b k * s7_b l) := by
    intro k l
    have h3 := (hCB N hN k l).2.2
    rw [abs_sub_comm] at h3
    rw [abs_mul, abs_mul, abs_of_pos hNpos]
    have hbk := hb0 k
    have hbl := hb0 l
    have h4 : |s7_Cmode r ρ a l k - ∫ X, sed_A (v k) (s7_phi r l) X ∂Q| ≤
        |CB| * (s7_b k * s7_b l) / N := by
      refine h3.trans ?_
      rw [mul_assoc]
      have hNp : (0 : ℝ) < N := by exact_mod_cast hN
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self CB)
        (mul_nonneg hbk hbl)) hNp.le
    calc sN * |s7_Cmode r ρ a l k - ∫ X, sed_A (v k) (s7_phi r l) X ∂Q| *
          |∫ X, iteratedFDeriv ℝ 2 (steinSolG G Φ) (zetaE r Q X) ![s7_eps r k, s7_eps r l] ∂Q|
        ≤ sN * (|CB| * (s7_b k * s7_b l) / N) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left h4 hNpos.le) (hM1 k l) (abs_nonneg _)
            (mul_nonneg hNpos.le (div_nonneg (mul_nonneg (abs_nonneg _) (mul_nonneg hbk hbl))
              (Nat.cast_nonneg N)))
      _ = (|CB| / sN) * (s7_b k * s7_b l) := by
          rw [mul_one, hNr]
          field_simp
  have := s7f_tsum2_abs_le hb hb0 hterm
  calc _ ≤ (|CB| / sN) * ∑' p : NonzeroLattice d × NonzeroLattice d, s7_b p.1 * s7_b p.2 := this
    _ = _ := by ring

end HRS.MC.Sec7.S7f

end
