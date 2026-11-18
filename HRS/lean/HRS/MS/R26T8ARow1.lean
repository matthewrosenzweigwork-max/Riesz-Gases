import HRS.MS.R26T8AP17f
import HRS.MS.R26T8APot3

/-!
# S8.2 row lemma, step 1: pointwise jets of the shifted integrand
For `F` conormal and `rho` smooth with polynomially decaying jets:
`‖D^j_x [rho(x-u) F(x, x-u)]‖ <= 2^j K (1+|x-u|)^(-N) * (A pairWeight M x (x-u) (1 + (min 1 |u|)^(-sigma) (1+|log min 1 |u||)^b))`, `u != 0`
(all `x`-derivatives fall on the centre variable `x - u/2`; Leibniz and `r26t8a_nest_zero`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff
open HRS HRS.Whole HRS.MS.Phase2S82

namespace HRS.MS.R26T8A

variable {d : ℕ}

theorem r26t8a_row_pt (k b : ℕ) (M σ A K N : ℝ) {ρ : Euc d → ℝ} (hρ : ContDiff ℝ (k : WithTop ℕ∞) ρ)
    (hK : ∀ i ≤ k, ∀ y : Euc d, ‖iteratedFDeriv ℝ i ρ y‖ ≤ K * (1 + ‖y‖) ^ (-N))
    {F : Euc d → Euc d → ℝ} (hF : Conormal k b M σ A F) {u : Euc d} (hu : u ≠ 0) (x : Euc d) (j : ℕ) (hj : j ≤ k) :
    ‖iteratedFDeriv ℝ j (fun x' : Euc d => ρ (x' - u) * F x' (x' - u)) x‖ ≤
      2 ^ j * (K * (1 + ‖x - u‖) ^ (-N)) *
        (A * pairWeight M x (x - u) *
          (1 + (min 1 ‖u‖) ^ (-(σ + ((0 : ℕ) : ℝ))) * (1 + |Real.log (min 1 ‖u‖)|) ^ b)) := by
  set g : Euc d → ℝ := fun x' => F x' (x' - u) with hg
  have hgc : ContDiff ℝ (k : WithTop ℕ∞) g := by
    have hl : ContDiff ℝ (k : WithTop ℕ∞) (fun x' : Euc d => (x', x' - u)) :=
      contDiff_id.prodMk (contDiff_id.sub contDiff_const)
    have := hF.1.comp_contDiff hl (fun x' => by
      intro h; apply hu
      have h' : x' - (x' - u) = 0 := sub_eq_zero.2 h
      simpa using h')
    exact this
  have hfc : ContDiff ℝ (k : WithTop ℕ∞) (fun x' : Euc d => ρ (x' - u)) :=
    hρ.comp (contDiff_id.sub contDiff_const)
  have hmul := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) hfc hgc x (n := j) (by exact_mod_cast hj)
  refine hmul.trans ?_
  have hX : x - (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • u = x := by module
  have hY : x - (1 / 2 : ℝ) • u - (1 / 2 : ℝ) • u = x - u := by module
  set Bg : ℝ := A * pairWeight M x (x - u) *
    (1 + (min 1 ‖u‖) ^ (-(σ + ((0 : ℕ) : ℝ))) * (1 + |Real.log (min 1 ‖u‖)|) ^ b) with hBg
  have hgj : ∀ i ≤ k, ‖iteratedFDeriv ℝ i g x‖ ≤ Bg := by
    intro i hi
    have e : g = fun x' => midPair F (x' - (1 / 2 : ℝ) • u) u := by
      funext x'
      unfold midPair
      have h1 : x' - (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • u = x' := by module
      have h2 : x' - (1 / 2 : ℝ) • u - (1 / 2 : ℝ) • u = x' - u := by module
      rw [h1, h2]
    have e2 : iteratedFDeriv ℝ i g x = iteratedFDeriv ℝ i (fun Y => midPair F Y u) (x - (1 / 2 : ℝ) • u) := by
      rw [e]; exact iteratedFDeriv_comp_sub (f := fun Y => midPair F Y u) i ((1 / 2 : ℝ) • u) x
    have h3 := hF.2 i 0 (by omega) (x - (1 / 2 : ℝ) • u) u hu
    have e3 : ‖mixedJet i 0 F (x - (1 / 2 : ℝ) • u) u‖ = ‖iteratedFDeriv ℝ i g x‖ := by
      rw [e2]
      show ‖r26t8a_nest i 0 (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) (x - (1 / 2 : ℝ) • u) u‖ = _
      rw [r26t8a_nest_zero]
    rw [← e3]
    rw [hX, hY] at h3
    exact h3
  calc ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun x' : Euc d => ρ (x' - u)) x‖ *
        ‖iteratedFDeriv ℝ (j - i) g x‖
      ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (K * (1 + ‖x - u‖) ^ (-N)) * Bg := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ j := by have := Finset.mem_range.1 hi; omega
        have h1 : ‖iteratedFDeriv ℝ i (fun x' : Euc d => ρ (x' - u)) x‖ ≤ K * (1 + ‖x - u‖) ^ (-N) := by
          rw [iteratedFDeriv_comp_sub (f := ρ) i u x]
          exact hK i (by omega) _
        have h2 := hgj (j - i) (by omega)
        have hch : (0 : ℝ) ≥ 0 := le_rfl
        exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2 (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) ((norm_nonneg _).trans h1))
    _ = 2 ^ j * (K * (1 + ‖x - u‖) ^ (-N)) * Bg := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        congr 1
        rw [show ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) = 2 ^ j by exact_mod_cast Nat.sum_range_choose j]

end HRS.MS.R26T8A
