import HRS.Commutator.Whole.XNRSAux17

/-!
# Packet X-NRS, part 18: the bound for Fourier-localised `a` and smooth `v`
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv

noncomputable section

namespace HRS.Commutator.Whole.XNRS

variable {d : ℕ}

lemma xhom_xlam {ρ : Euc d → ℝ} (hρ : XGoodCut ρ) {h : 𝓢(Euc d, ℂ)} (hh : XInD ρ h) (β γ : ℝ) :
    xhom β (xlam γ ρ h) = xhom (β + γ) h := by
  unfold xhom
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only
  rw [fourier_xlam_of_inD hρ hh, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  by_cases hξ : ξ = 0
  · subst hξ
    obtain ⟨ε, hε, hz⟩ := xInD_fourier_zero_near hρ hh
    rw [hz 0 (by simpa using hε)]
    simp
  · have hn : 0 < 2 * Real.pi * ‖ξ‖ := by
      have := norm_pos_iff.2 hξ
      positivity
    rw [show 2 * (β + γ) = 2 * β + 2 * γ by ring, Real.rpow_add hn, mul_pow,
      ← Real.rpow_natCast ((2 * Real.pi * ‖ξ‖) ^ γ), ← Real.rpow_mul hn.le]
    push_cast
    rw [mul_comm γ 2]
    ring

theorem xcore (hd : 3 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ c0 : ℝ, 0 ≤ c0 ∧ ∀ (ρ : Euc d → ℝ) (_hρ : XGoodCut ρ) (v : Euc d → Euc d) (_hv : XTVF v)
      (L K : ℝ) (_hL0 : 0 ≤ L) (_hLK : L ≤ K) (_hL : XLip v L) (CB : ℝ) (_hCB : 0 ≤ CB) (k : ℕ)
      (_hk1 : (k : ℝ) ≤ ((d : ℝ) - s) / 2) (_hk2 : ((d : ℝ) - s) / 2 < k + 1)
      (_hmul : ∀ m : ℕ, 1 ≤ m → m ≤ k → ∀ (a c : Fin d) (Γ : 𝓢(Euc d, ℂ)), XInD ρ Γ →
        xhom (((d : ℝ) - s) / 2 - k + m - 1) (xwmul v a c Γ) ≤
          (CB * K) ^ 2 * xhom (((d : ℝ) - s) / 2 - k + m - 1) Γ)
      (a : Euc d → ℝ) (φ : 𝓢(Euc d, ℂ)) (_ha : ∀ x, φ x = (a x : ℂ)) (_hφ : XInD ρ φ),
      |CcommFun (kernGrad s) v a| ≤
        c0 * xC d (((d : ℝ) + ((d : ℝ) + 2 * (((d : ℝ) - s) / 2 - k) + 2) / 2)) CB k * K *
          xhom (-(((d : ℝ) - s) / 2)) φ := by
  obtain ⟨c', hc'⟩ := xB_J hd hs0 hsd
  refine ⟨2 * ‖c'‖, by positivity, fun ρ hρ v hv L K hL0 hLK hL CB hCB k hk1 hk2 hmul a φ ha hφ => ?_⟩
  have hd1 : 1 ≤ d := by omega
  have hB := hc' ρ hρ v hv L hL0 hL a φ ha hφ
  set h := xlam (-((d : ℝ) - s)) ρ φ with hh
  have hhD : XInD ρ h := xInD_xlam hρ hφ _
  have hJ := xJbound hd1 hρ hv hL0 hLK hL (α' := ((d : ℝ) - s) / 2 - k) (CB := CB)
    (by linarith) (by linarith) hCB k hmul h hhD
  have e1 : 2 * (((d : ℝ) - s) / 2 - k) + 2 * (k : ℝ) = (d : ℝ) - s := by ring
  rw [e1] at hJ
  have e2 : xhom (((d : ℝ) - s) / 2 - k + k) h = xhom (-(((d : ℝ) - s) / 2)) φ := by
    rw [hh, xhom_xlam hρ hφ]
    congr 1
    ring
  rw [e2] at hJ
  have hnorm : |CcommFun (kernGrad s) v a| = 2 * ‖c'‖ * ‖xJ v ρ ((d : ℝ) - s) h‖ := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, hB, norm_mul, norm_mul]
    simp
  rw [hnorm]
  calc 2 * ‖c'‖ * ‖xJ v ρ ((d : ℝ) - s) h‖
      ≤ 2 * ‖c'‖ * (xC d (((d : ℝ) + ((d : ℝ) + 2 * (((d : ℝ) - s) / 2 - k) + 2) / 2)) CB k * K *
          xhom (-(((d : ℝ) - s) / 2)) φ) :=
        mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = _ := by ring

end HRS.Commutator.Whole.XNRS
