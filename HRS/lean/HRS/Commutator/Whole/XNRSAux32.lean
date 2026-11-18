import HRS.Commutator.Whole.XNRSAux31

/-!
# Packet X-NRS, part 32: the commutator bound for smooth `v`, conditional on the multiplier bound
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv Convolution

noncomputable section

namespace HRS.Commutator.Whole.XNRS

variable {d : ℕ}

theorem xmain_smooth (hd : 3 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ c0 : ℝ, 0 ≤ c0 ∧ ∀ (v : Euc d → Euc d) (_hv : XTVF v) (L K : ℝ) (_hL0 : 0 ≤ L) (_hLK : L ≤ K)
      (_hL : XLip v L) (CB : ℝ) (_hCB : 0 ≤ CB) (k : ℕ)
      (_hk1 : (k : ℝ) ≤ ((d : ℝ) - s) / 2) (_hk2 : ((d : ℝ) - s) / 2 < k + 1)
      (_hmul : ∀ ρ : Euc d → ℝ, XGoodCut ρ → ∀ m : ℕ, 1 ≤ m → m ≤ k →
        ∀ (a c : Fin d) (Γ : 𝓢(Euc d, ℂ)), XInD ρ Γ →
        xhom (((d : ℝ) - s) / 2 - k + m - 1) (xwmul v a c Γ) ≤
          (CB * K) ^ 2 * xhom (((d : ℝ) - s) / 2 - k + m - 1) Γ)
      (a : Euc d → ℝ) (_ha : HRS.Commutator.Whole.IsRealSchwartz a) (_hmass : s = 0 → ∫ x, a x = 0),
      ENNReal.ofReal |HRS.Commutator.Whole.CcommFun (kernGrad s) v a| ≤
        ENNReal.ofReal (c0 * xC d (((d : ℝ) + ((d : ℝ) + 2 * (((d : ℝ) - s) / 2 - k) + 2) / 2)) CB k * K) *
          HRS.Commutator.Whole.homSqE (-HRS.Commutator.Whole.alphaE d s)
            (HRS.PDE.ToolboxRd.fourierL2 a) := by
  obtain ⟨c0, hc0, hcore⟩ := xcore hd hs0 hsd
  refine ⟨c0, hc0, fun v hv L K hL0 hLK hL CB hCB k hk1 hk2 hmul a ha hmass => ?_⟩
  obtain ⟨φ, hφ⟩ := ha
  have hK0 : 0 ≤ K := hL0.trans hLK
  have hseq := xCcomm_tendsto hd hs0 hsd hL0 hL hφ hmass
  have hlim : Tendsto (fun n : ℝ => ENNReal.ofReal |HRS.Commutator.Whole.CcommFun (kernGrad s) v (xan a n)|)
      atTop (nhds (ENNReal.ofReal |HRS.Commutator.Whole.CcommFun (kernGrad s) v a|)) :=
    (ENNReal.continuous_ofReal.tendsto _).comp ((continuous_abs.tendsto _).comp hseq)
  refine le_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with n hn
  have hn0 : 0 < n := by linarith
  have hφn : ∀ x, xφn φ n hn0 x = ((xan a n x : ℝ) : ℂ) := xφn_real hφ n hn0
  have hcb := hcore (xρ n) (xρ_good hn0) v hv L K hL0 hLK hL CB hCB k hk1 hk2 (hmul (xρ n) (xρ_good hn0))
    (xan a n) (xφn φ n hn0) hφn (xInD_xφn φ hn0)
  have hα0 : 0 ≤ ((d : ℝ) - s) / 2 - k := by linarith
  have hC0 : 0 ≤ (d : ℝ) + ((d : ℝ) + 2 * (((d : ℝ) - s) / 2 - k) + 2) / 2 := by positivity
  have hxC : 0 ≤ xC d (((d : ℝ) + ((d : ℝ) + 2 * (((d : ℝ) - s) / 2 - k) + 2) / 2)) CB k :=
    xC_nonneg hC0 hCB k
  have hcK : 0 ≤ c0 * xC d (((d : ℝ) + ((d : ℝ) + 2 * (((d : ℝ) - s) / 2 - k) + 2) / 2)) CB k * K :=
    mul_nonneg (mul_nonneg hc0 hxC) hK0
  have hβ : -(((d : ℝ) - s) / 2) ≤ 0 := by
    have : 0 < ((d : ℝ) - s) / 2 := by linarith
    linarith
  have hle : ∀ ξ, ‖𝓕 (xφn φ n hn0) ξ‖ ≤ ‖𝓕 φ ξ‖ := by
    intro ξ
    rw [fourier_xφn, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ xσ n ξ from xcut_nonneg n n ξ)]
    exact mul_le_of_le_one_right (norm_nonneg _) (show xσ n ξ ≤ 1 from xcut_le_one n n ξ)
  have hh := xhom_ofReal_le (xρ_good hn0) (xInD_xφn φ hn0) hβ hle hφ
  calc ENNReal.ofReal |HRS.Commutator.Whole.CcommFun (kernGrad s) v (xan a n)|
      ≤ ENNReal.ofReal (c0 * xC d (((d : ℝ) + ((d : ℝ) + 2 * (((d : ℝ) - s) / 2 - k) + 2) / 2)) CB k * K *
          xhom (-(((d : ℝ) - s) / 2)) (xφn φ n hn0)) := ENNReal.ofReal_le_ofReal hcb
    _ = ENNReal.ofReal (c0 * xC d (((d : ℝ) + ((d : ℝ) + 2 * (((d : ℝ) - s) / 2 - k) + 2) / 2)) CB k * K) *
          ENNReal.ofReal (xhom (-(((d : ℝ) - s) / 2)) (xφn φ n hn0)) := ENNReal.ofReal_mul hcK
    _ ≤ _ := by
        gcongr
        exact hh

end HRS.Commutator.Whole.XNRS
