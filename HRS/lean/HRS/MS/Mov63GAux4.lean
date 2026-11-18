import HRS.MS.Mov63GAux3
import HRS.MS.Mov63FAux6

/-!
# S6.3, packet N8 (part 4): the abstract master comparison

Namespace `HRS.MS.Mov63`, prefix `mng_`.  **`mng_master`**: weak maximum principle on `[0,T] × ℝ^d` in the Gaussian growth class
`|P| ≤ K_p exp(κ₀ ‖x‖²)`, `κ₀ < q/(2ν)`, for `∂_tP ≥ νΔP + ⟨b,∇P⟩ + cP` (`c ≤ 0`), drift with `⟨b,x⟩ ≤ -q‖x‖² + M‖x‖`
(the generic form of `mnf_master`, using `mnf_comparison`, `mnf_lyap_super`, `mnf_hgrow`).
-/

noncomputable section

open Filter Topology Set MeasureTheory
open scoped RealInnerProductSpace

namespace HRS.MS.Mov63

open HRS

variable {d : ℕ}

theorem mng_master {ν q M κ0 Kp T : ℝ} (hν : 0 < ν) (hq : 0 < q) (hκ0 : κ0 < q / (2 * ν)) (hKp : 0 ≤ Kp)
    {P Pt : ℝ → Euc d → ℝ} {bv : ℝ → Euc d → Euc d} {c : ℝ → Euc d → ℝ}
    (hP2 : ∀ t ∈ Icc 0 T, ContDiff ℝ 2 (P t))
    (hPc : ContinuousOn (fun p : ℝ × Euc d => P p.1 p.2) (Icc 0 T ×ˢ univ))
    (hPd : ∀ t ∈ Ioc 0 T, ∀ x, HasDerivWithinAt (fun s => P s x) (Pt t x) (Icc 0 T) t)
    (hPeq : ∀ t ∈ Ioc 0 T, ∀ x, ν * Laplacian.laplacian (P t) x + inner ℝ (bv t x) (gradient (P t) x) +
      c t x * P t x ≤ Pt t x)
    (hc : ∀ t ∈ Ioc 0 T, ∀ x, c t x ≤ 0)
    (hbdiss : ∀ t ∈ Ioc 0 T, ∀ x, inner ℝ (bv t x) x ≤ -q * ‖x‖ ^ 2 + M * ‖x‖)
    (hgrow : ∀ t ∈ Icc 0 T, ∀ x, |P t x| ≤ Kp * Real.exp (κ0 * ‖x‖ ^ 2))
    (h0 : ∀ x, 0 ≤ P 0 x) : ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ P t x := by
  set κ : ℝ := (max κ0 0 + q / (2 * ν)) / 2 with hκ
  have hqν : 0 < q / (2 * ν) := by positivity
  have hκ1 : max κ0 0 < κ := by rw [hκ]; have := max_lt hκ0 hqν; linarith
  have hκpos : 0 < κ := lt_of_le_of_lt (le_max_right _ _) hκ1
  have hκ0' : κ0 < κ := lt_of_le_of_lt (le_max_left _ _) hκ1
  have hνκ : 2 * ν * κ < q := by
    have h2 : κ < q / (2 * ν) := by rw [hκ]; have := max_lt hκ0 hqν; linarith
    rw [lt_div_iff₀ (by positivity)] at h2
    linarith
  set lam : ℝ := 2 * ν * κ * d + κ ^ 2 * M ^ 2 / (2 * κ * q - 4 * ν * κ ^ 2) + 1 with hlam
  have hapos : 0 < 2 * κ * q - 4 * ν * κ ^ 2 := by
    have : 0 < 2 * κ * (q - 2 * ν * κ) := mul_pos (by positivity) (by linarith)
    nlinarith
  have hlam0 : 0 ≤ lam := by
    rw [hlam]
    have : 0 ≤ 2 * ν * κ * d := by positivity
    have : 0 ≤ κ ^ 2 * M ^ 2 / (2 * κ * q - 4 * ν * κ ^ 2) := by positivity
    linarith
  refine mnf_comparison (ν := ν) hν.le (T := T) (P := P) (Pt := Pt)
    (φ := mnf_lyap lam κ) (φt := fun t x => lam * mnf_lyap lam κ t x) (b := bv) (c := c)
    hP2 (fun t ht => mnf_lyap_cd lam κ t) hPc (mnf_lyap_cont lam κ).continuousOn hPd ?_ hPeq hc ?_ ?_ ?_ h0
  · intro t ht x
    exact (mnf_lyap_hasDerivAt lam κ t x).hasDerivWithinAt
  · intro t ht x
    exact mnf_lyap_super hν hκpos hνκ t x _ (hbdiss t ht x)
  · intro t ht x
    exact mnf_lyap_pos _ _ _ _
  · exact mnf_hgrow hKp hκ0' hlam0 hgrow

end HRS.MS.Mov63

end
