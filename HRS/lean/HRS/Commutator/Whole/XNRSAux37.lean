import HRS.Commutator.Whole.XNRSAux36

/-!
# Packet X-NRS, part 37: `nrs_commutator`, conditional on the multiplier bound `XBB`
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv Convolution

noncomputable section

namespace HRS.Commutator.Whole.XNRS

variable {d : ℕ}

open HRS.Commutator.Whole HRS.Commutator.Whole.SAMP1

/-- **The multiplier bound** (the Kato–Ponce / Hardy–Littlewood–Sobolev input of Nguyen–Rosenzweig–
Serfaty): for a smooth temperate field `v` with `‖∇v‖_∞ + ‖|∇|^α v‖_{L^p} ≤ K`, `α = (d-s)/2`,
`p = 2d/(d-s-2)`, `k = ⌊α⌋`, `α' = α - k` and `1 ≤ m ≤ k`: multiplication by `∂_a v_c` is bounded by
`CB K` on `Ḣ^{α'+m-1}`, for Fourier-localised Schwartz functions, uniformly in the localisation. -/
def XBB (d : ℕ) (s CB : ℝ) : Prop :=
  0 ≤ CB ∧ ∀ (v : Euc d → Euc d), XTVF v → ∀ K : ℝ, SubTransport d s v K →
    ∀ (ρ : Euc d → ℝ), XGoodCut ρ → ∀ k : ℕ, (k : ℝ) ≤ ((d : ℝ) - s) / 2 →
      ((d : ℝ) - s) / 2 < k + 1 → ∀ m : ℕ, 1 ≤ m → m ≤ k →
      ∀ (a c : Fin d) (Γ : 𝓢(Euc d, ℂ)), XInD ρ Γ →
        xhom (((d : ℝ) - s) / 2 - k + m - 1) (xwmul v a c Γ) ≤
          (CB * K) ^ 2 * xhom (((d : ℝ) - s) / 2 - k + m - 1) Γ

theorem xnrs_conditional (hd : 3 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {CB : ℝ}
    (hBB : XBB d s CB) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Euc d → Euc d) (K : ℝ), SubTransport d s v K →
      ∀ a : Euc d → ℝ, IsRealSchwartz a → (s = 0 → ∫ x, a x = 0) →
        ENNReal.ofReal |CcommFun (kernGrad s) v a| ≤
          ENNReal.ofReal (C * K) * homSqE (-alphaE d s) (HRS.PDE.ToolboxRd.fourierL2 a) := by
  obtain ⟨c0, hc0, hmain⟩ := xmain_smooth hd hs0 hsd
  have hα0 : 0 ≤ ((d : ℝ) - s) / 2 := by linarith
  set k : ℕ := ⌊((d : ℝ) - s) / 2⌋₊ with hk
  have hk1 : (k : ℝ) ≤ ((d : ℝ) - s) / 2 := Nat.floor_le hα0
  have hk2 : ((d : ℝ) - s) / 2 < k + 1 := Nat.lt_floor_add_one _
  set Cx : ℝ := xC d (((d : ℝ) + ((d : ℝ) + 2 * (((d : ℝ) - s) / 2 - k) + 2) / 2)) CB k with hCx
  have hC0 : 0 ≤ (d : ℝ) + ((d : ℝ) + 2 * (((d : ℝ) - s) / 2 - k) + 2) / 2 := by
    have : 0 ≤ ((d : ℝ) - s) / 2 - k := by linarith
    positivity
  have hCx0 : 0 ≤ Cx := xC_nonneg hC0 hBB.1 k
  refine ⟨c0 * Cx + 1, by positivity, ?_⟩
  intro v K hv a ha hmass
  have hv' := hv
  obtain ⟨L, F, hF0, hLip, hw, hLF⟩ := hv'
  have hL0 : (0 : ℝ) ≤ L := L.2
  have hLK : (L : ℝ) ≤ K := by linarith
  have hK0 : 0 ≤ K := hL0.trans hLK
  obtain ⟨φ, hφ⟩ := ha
  have hseq := xmol_tendsto hd hs0 hsd hLip hφ
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal |CcommFun (kernGrad s) (xmol (xmk d n) v) a|)
      atTop (nhds (ENNReal.ofReal |CcommFun (kernGrad s) v a|)) :=
    (ENNReal.continuous_ofReal.tendsto _).comp ((continuous_abs.tendsto _).comp hseq)
  have hcC : ENNReal.ofReal (c0 * Cx * K) ≤ ENNReal.ofReal ((c0 * Cx + 1) * K) :=
    ENNReal.ofReal_le_ofReal (by nlinarith [mul_nonneg hc0 hCx0])
  refine le_trans (le_of_tendsto hlim (Eventually.of_forall fun n => ?_))
    (mul_le_mul' hcC le_rfl)
  have hvtg : XTVF (xmol (xmk d n) v) := xmol_xtvf (xmk_ker n) (xmk_smooth n) hLip
  have hvsub : SubTransport d s (xmol (xmk d n) v) K := xmol_transport hd hs0 hsd (xmk_ker n) hv
  have hvlip : XLip (xmol (xmk d n) v) L := fun x y => xmol_lip (xmk_ker n) hLip x y
  exact hmain _ hvtg L K hL0 hLK hvlip CB hBB.1 k hk1 hk2
    (fun ρ hρ m hm1 hmk a c Γ hΓ => hBB.2 _ hvtg K hvsub ρ hρ k hk1 hk2 m hm1 hmk a c Γ hΓ)
    a ⟨φ, hφ⟩ hmass

end HRS.Commutator.Whole.XNRS
