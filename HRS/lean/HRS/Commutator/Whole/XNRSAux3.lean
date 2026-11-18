import HRS.Commutator.Whole.XNRSAux2

/-!
# Packet X-NRS, part 3: the induction `J_m` bound from the base case and the multiplier bound

Hypotheses: the base bound `‖J(2α',h)‖ ≤ C₀ K ‖Λ^{α'}h‖²` (the super-Coulombic estimate for
`α' ∈ (0,1)`, or the trivial `α' = 0` case) and, for each `m ≥ 1`, the multiplier bound
`‖Λ^{α'+m-1}(∂_a v_c Γ)‖² ≤ (C_B K)² ‖Λ^{α'+m-1}Γ‖²` (a Kato–Ponce/Leibniz consequence).
Conclusion: `‖J(2α'+2m,h)‖ ≤ C_m K ‖Λ^{α'+m}h‖²`.
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv

noncomputable section

namespace HRS.Commutator.Whole.XNRS

variable {d : ℕ}

/-- `C_0 = C₀`, `C_{m+1} = d C_m + d² C_B`. -/
def xC (d : ℕ) (C0 CB : ℝ) : ℕ → ℝ
  | 0 => C0
  | m + 1 => d * xC d C0 CB m + (d : ℝ) ^ 2 * CB

lemma xC_nonneg {C0 CB : ℝ} (h0 : 0 ≤ C0) (hB : 0 ≤ CB) (m : ℕ) : 0 ≤ xC d C0 CB m := by
  induction m with
  | zero => exact h0
  | succ m ih => simp only [xC]; positivity

lemma xhom_xdr_le {β : ℝ} (hβ : 0 ≤ β) (a : Fin d) (h : 𝓢(Euc d, ℂ)) :
    xhom β (xdr a h) ≤ xhom (β + 1) h := by
  unfold xhom
  refine integral_mono (integrable_xhom hβ _) (integrable_xhom (by linarith) _) fun ξ => ?_
  simp only
  rw [fourier_xdr, norm_mul]
  have hξa : |ξ a| ≤ ‖ξ‖ := by
    have := EuclideanSpace.norm_eq ξ
    calc |ξ a| = Real.sqrt (ξ a ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (∑ i, ξ i ^ 2) := by
          apply Real.sqrt_le_sqrt
          exact Finset.single_le_sum (f := fun i => ξ i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ a)
      _ = ‖ξ‖ := by rw [EuclideanSpace.norm_eq]; simp
  have hn : ‖(2 * (Real.pi : ℂ) * Complex.I * ((ξ a : ℝ) : ℂ))‖ ≤ 2 * Real.pi * ‖ξ‖ := by
    rw [norm_mul, norm_mul, norm_mul]
    simp only [Complex.norm_ofNat, Complex.norm_real, Complex.norm_I, Real.norm_eq_abs, abs_of_nonneg Real.pi_pos.le,
      mul_one]
    nlinarith [Real.pi_pos]
  have hpos : 0 ≤ 2 * Real.pi * ‖ξ‖ := by positivity
  have hrw : (2 * Real.pi * ‖ξ‖) ^ (2 * (β + 1)) = (2 * Real.pi * ‖ξ‖) ^ (2 * β) * (2 * Real.pi * ‖ξ‖) ^ 2 := by
    rcases eq_or_lt_of_le hpos with h0 | h0
    · rw [← h0]
      have h2β : (0 : ℝ) < 2 * (β + 1) := by linarith
      rw [Real.zero_rpow h2β.ne']; simp
    · rw [show 2 * (β + 1) = 2 * β + (2 : ℕ) by push_cast; ring, Real.rpow_add h0, Real.rpow_natCast]
  rw [hrw]
  have hnn : 0 ≤ (2 * Real.pi * ‖ξ‖) ^ (2 * β) := by positivity
  calc (2 * Real.pi * ‖ξ‖) ^ (2 * β) * (‖(2 * (Real.pi : ℂ) * Complex.I * ((ξ a : ℝ) : ℂ))‖ * ‖𝓕 h ξ‖) ^ 2
      = (2 * Real.pi * ‖ξ‖) ^ (2 * β) * (‖(2 * (Real.pi : ℂ) * Complex.I * ((ξ a : ℝ) : ℂ))‖ ^ 2 * ‖𝓕 h ξ‖ ^ 2) := by
        rw [mul_pow]
    _ ≤ (2 * Real.pi * ‖ξ‖) ^ (2 * β) * ((2 * Real.pi * ‖ξ‖) ^ 2 * ‖𝓕 h ξ‖ ^ 2) := by
        gcongr
    _ = _ := by ring


/-- Induction on `m`: `‖J(2α'+2m,h)‖ ≤ C_m K ‖Λ^{α'+m}h‖²`. -/
theorem xind {ρ : Euc d → ℝ} (hρ : XGoodCut ρ) {v : Euc d → Euc d} (hv : XTVF v)
    {K C0 CB α' : ℝ} (hK : 0 ≤ K) (hC0 : 0 ≤ C0) (hCB : 0 ≤ CB) (hα' : 0 ≤ α')
    (hbase : ∀ h : 𝓢(Euc d, ℂ), XInD ρ h → ‖xJ v ρ (2 * α') h‖ ≤ C0 * K * xhom α' h)
    {N : ℕ}
    (hmul : ∀ m : ℕ, 1 ≤ m → m ≤ N → ∀ (a c : Fin d) (Γ : 𝓢(Euc d, ℂ)), XInD ρ Γ →
      xhom (α' + m - 1) (xwmul v a c Γ) ≤ (CB * K) ^ 2 * xhom (α' + m - 1) Γ) :
    ∀ (m : ℕ), m ≤ N → ∀ (h : 𝓢(Euc d, ℂ)), XInD ρ h →
      ‖xJ v ρ (2 * α' + 2 * m) h‖ ≤ xC d C0 CB m * K * xhom (α' + m) h := by
  intro m
  induction m with
  | zero =>
    intro _ h hh
    simpa [xC] using hbase h hh
  | succ m ih =>
    intro hmN h hh
    have hβ : 0 ≤ α' + m := by positivity
    have hrec := xrec hρ hv hh (2 * α' + 2 * m)
    have e1 : 2 * α' + 2 * m + 2 = 2 * α' + 2 * ((m + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [e1] at hrec
    rw [hrec]
    have hA : ∀ a : Fin d, ‖xJ v ρ (2 * α' + 2 * m) (xdr a h)‖ ≤
        xC d C0 CB m * K * xhom (α' + (m + 1 : ℕ)) h := by
      intro a
      refine (ih (by omega) (xdr a h) (xInD_xdr hh a)).trans ?_
      have := xhom_xdr_le hβ a h
      have e2 : α' + ((m + 1 : ℕ) : ℝ) = α' + m + 1 := by push_cast; ring
      rw [e2]
      exact mul_le_mul_of_nonneg_left this (mul_nonneg (xC_nonneg hC0 hCB m) hK)
    have hR : ∀ a c : Fin d, ‖∫ x, xlam (2 * α' + 2 * m) ρ (xdr a h) x * xwmul v a c (xdr c h) x‖ ≤
        CB * K * xhom (α' + (m + 1 : ℕ)) h := by
      intro a c
      rw [integral_xlam_mul hρ (xInD_xdr hh a)]
      have e3 : 2 * α' + 2 * (m : ℝ) = 2 * (α' + m) := by ring
      rw [e3]
      refine (norm_xpair_le hβ _ _).trans ?_
      set X := xhom (α' + ((m + 1 : ℕ) : ℝ)) h with hX
      have e2 : α' + ((m + 1 : ℕ) : ℝ) = α' + m + 1 := by push_cast; ring
      have h1 : xhom (α' + m) (xdr a h) ≤ X := by rw [hX, e2]; exact xhom_xdr_le hβ a h
      have h2 : xhom (α' + m) (xwmul v a c (xdr c h)) ≤ (CB * K) ^ 2 * X := by
        have := hmul (m + 1) (by omega) hmN a c (xdr c h) (xInD_xdr hh c)
        have e4 : α' + ((m + 1 : ℕ) : ℝ) - 1 = α' + m := by push_cast; ring
        rw [e4] at this
        refine this.trans ?_
        have hle : xhom (α' + m) (xdr c h) ≤ X := by rw [hX, e2]; exact xhom_xdr_le hβ c h
        exact mul_le_mul_of_nonneg_left hle (sq_nonneg _)
      calc Real.sqrt (xhom (α' + m) (xdr a h)) * Real.sqrt (xhom (α' + m) (xwmul v a c (xdr c h)))
          ≤ Real.sqrt X * Real.sqrt ((CB * K) ^ 2 * X) := by
            gcongr
        _ = CB * K * X := by
            have hX0 : 0 ≤ X := by
              rw [hX]
              exact integral_nonneg fun ξ => by positivity
            rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg hCB hK)]
            have := Real.mul_self_sqrt hX0
            rw [show Real.sqrt X * (CB * K * Real.sqrt X) = CB * K * (Real.sqrt X * Real.sqrt X) by ring, this]
    calc ‖∑ a, xJ v ρ (2 * α' + 2 * m) (xdr a h) +
          ∑ a, ∑ c, ∫ x, xlam (2 * α' + 2 * m) ρ (xdr a h) x * xwmul v a c (xdr c h) x‖
        ≤ ∑ a, ‖xJ v ρ (2 * α' + 2 * m) (xdr a h)‖ +
          ∑ a, ∑ c, ‖∫ x, xlam (2 * α' + 2 * m) ρ (xdr a h) x * xwmul v a c (xdr c h) x‖ := by
          refine (norm_add_le _ _).trans (add_le_add (norm_sum_le _ _) ?_)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
      _ ≤ ∑ a : Fin d, xC d C0 CB m * K * xhom (α' + (m + 1 : ℕ)) h +
          ∑ a : Fin d, ∑ c : Fin d, CB * K * xhom (α' + (m + 1 : ℕ)) h := by
          refine add_le_add (Finset.sum_le_sum fun a _ => hA a)
            (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun c _ => hR a c)
      _ = xC d C0 CB (m + 1) * K * xhom (α' + (m + 1 : ℕ)) h := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, xC]
          ring

end HRS.Commutator.Whole.XNRS
