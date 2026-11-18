import HRS.Sections.ScrnAux8

/-!
# Packet SCRN, part 9: derivative bounds of a torus function from its Fourier coefficients

`scrn_iteratedFDeriv_le`: for a continuous `g` with `∑_k (2π|k|)^i |ĝ(k)| < ∞` (`i ≤ j`), `g` is `C^j` and
`‖D^i g(y)‖ ≤ 2 ∑_k (2π|k|)^i |ĝ(k)|` (the `k = 0` mode drops out for `i ≥ 1`).
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

namespace HRS

variable {d : ℕ}

open PDE in
theorem scrn_iteratedFDeriv_le {g : Torus d → ℝ} (hg : Continuous g) {j : ℕ}
    (hs : ∀ i : ℕ, i ≤ j → Summable fun k : Lattice d =>
      (2 * Real.pi * Lattice.enorm k) ^ i * ‖coeffOf g k‖) :
    Torus.IsCk j g ∧ ∀ i : ℕ, i ≤ j → ∀ y : Euc d,
      ‖iteratedFDeriv ℝ i (Torus.lift g) y‖ ≤
        2 * ∑' k : Lattice d, (2 * Real.pi * Lattice.enorm k) ^ i * ‖coeffOf g k‖ := by
  set c : Coeff d := coeffOf g with hc
  have hs0 : Summable fun k : Lattice d => ‖c k‖ := by
    simpa using hs 0 (Nat.zero_le _)
  have hlift : Torus.lift g = fun y => ∑' k, termFun c k y := by
    have h1 : toFun (coeffOf g) = g := toFun_coeffOf g hg hs0
    rw [← h1]
    exact lift_toFun_eq_tsum c hs0
  have hcomb : ∀ k : Lattice d, ContDiff ℝ ⊤ (fun t : ℝ =>
      (c k).re * Real.cos t + (-(c k).im) * Real.sin t) := fun k =>
    (contDiff_const.mul Real.contDiff_cos).add (contDiff_const.mul Real.contDiff_sin)
  have hf : ∀ k, ContDiff ℝ (j : ℕ∞) (termFun c k) := fun k =>
    ((hcomb k).comp (Torus.freqFunctional k).contDiff).of_le le_top
  set v : ℕ → Lattice d → ℝ := fun i k => 2 * ((2 * Real.pi * Lattice.enorm k) ^ i * ‖c k‖) with hv
  have hvs : ∀ i : ℕ, (i : ℕ∞) ≤ j → Summable (v i) := fun i hi =>
    (hs i (by exact_mod_cast hi)).mul_left 2
  have hbd : ∀ (i : ℕ) (k : Lattice d) (x : Euc d), (i : ℕ∞) ≤ j →
      ‖iteratedFDeriv ℝ i (termFun c k) x‖ ≤ v i k := by
    intro i k x _
    have hb := Torus.norm_iteratedFDeriv_comp_functional _ (hcomb k) _
      (fun i t => norm_iteratedFDeriv_trig_comb ((c k).re) (-(c k).im) i t)
      (Torus.freqFunctional k) i x
    refine hb.trans ?_
    have h1 : |(c k).re| + |-(c k).im| ≤ 2 * ‖c k‖ := by
      rw [abs_neg]
      have := Complex.abs_re_le_norm (c k)
      have := Complex.abs_im_le_norm (c k)
      linarith
    have h2 : ‖Torus.freqFunctional k‖ ^ i ≤ (2 * Real.pi * Lattice.enorm k) ^ i :=
      pow_le_pow_left₀ (norm_nonneg _) (Torus.norm_freqFunctional_le _) i
    calc (|(c k).re| + |-(c k).im|) * ‖Torus.freqFunctional k‖ ^ i
        ≤ (2 * ‖c k‖) * (2 * Real.pi * Lattice.enorm k) ^ i := by gcongr
      _ = v i k := by simp only [hv]; ring
  have hCk : Torus.IsCk j g := by
    unfold Torus.IsCk
    rw [hlift]
    exact contDiff_tsum (N := (j : ℕ∞)) hf hvs (fun i k x hi => hbd i k x hi)
  refine ⟨hCk, fun i hi y => ?_⟩
  have hit := iteratedFDeriv_tsum (N := (j : ℕ∞)) (𝕜 := ℝ) hf hvs (fun i k x hi => hbd i k x hi)
    (k := i) (by exact_mod_cast hi)
  rw [hlift, hit]
  have hsv : Summable (v i) := hvs i (by exact_mod_cast hi)
  have hnorms : Summable fun k => ‖iteratedFDeriv ℝ i (termFun c k) y‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => hbd i k y (by exact_mod_cast hi)) hsv
  calc ‖∑' k, iteratedFDeriv ℝ i (termFun c k) y‖
      ≤ ∑' k, ‖iteratedFDeriv ℝ i (termFun c k) y‖ := norm_tsum_le_tsum_norm hnorms
    _ ≤ ∑' k, v i k := hnorms.tsum_le_tsum (fun k => hbd i k y (by exact_mod_cast hi)) hsv
    _ = 2 * ∑' k : Lattice d, (2 * Real.pi * Lattice.enorm k) ^ i * ‖c k‖ := by
        simp only [hv]; rw [tsum_mul_left]

end HRS
