import HRS.Sections.AdjKDAux5
import HRS.Main.T25Aux4
import HRS.Sections.Q40bAux5

/-!
# ADJKD, part 6: helper lemmas for the `L¹` remainder bound (packet B2)
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.AdjK

open HRS.Uniform

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

/-- The adjoint propagator is `C²` in space on `[0,t]` (also in the junk case). -/
theorem adjkd_propagator_ck2 (D : DynData d) (ρ : ℝ → Torus d → ℝ) {r t : ℝ} (hr : 0 ≤ r)
    (hrt : r ≤ t) (φ : Torus d → ℝ) : Torus.IsCk 2 (propagator D ρ r t φ) := by
  unfold propagator
  by_cases h : ∃ f, IsClassicalAdjointSolution D ρ t φ f
  · rw [dif_pos h]
    exact h.choose_spec.c2 r ⟨hr, hrt⟩
  · rw [dif_neg h]
    show ContDiff ℝ 2 (Torus.lift (fun _ : Torus d => (0 : ℝ)))
    exact contDiff_const

/-- Decay of the coefficients gives summability of the Sobolev series. -/
theorem adjkd_sobolev_summable {m m' : ℝ} (hmm' : (d : ℝ) < 2 * (m - m')) {B : ℝ}
    (a : NonzeroLattice d → ℝ) (ha : ∀ j, |a j| ≤ B * Lattice.jp j.1 ^ (-m)) :
    Summable fun j : NonzeroLattice d => Lattice.jp j.1 ^ (2 * m') * a j ^ 2 := by
  have hs := summable_jp_rpow (d := d) (m - m') hmm'
  refine Summable.of_nonneg_of_le (fun j => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _)
    (sq_nonneg _)) (fun j => ?_) (hs.mul_left (B ^ 2))
  have h1 : a j ^ 2 ≤ (B * Lattice.jp j.1 ^ (-m)) ^ 2 := by
    rw [← sq_abs (a j)]
    exact pow_le_pow_left₀ (abs_nonneg _) (ha j) 2
  have h2 : (B * Lattice.jp j.1 ^ (-m)) ^ 2 = B ^ 2 * Lattice.jp j.1 ^ (-(2 * m)) := by
    rw [mul_pow, Torus.jp_rpow_sq]
    congr 2
    ring
  have hjp : 0 ≤ Lattice.jp j.1 ^ (2 * m') := Real.rpow_nonneg (Torus.jp_pos _).le _
  calc Lattice.jp j.1 ^ (2 * m') * a j ^ 2
      ≤ Lattice.jp j.1 ^ (2 * m') * (B ^ 2 * Lattice.jp j.1 ^ (-(2 * m))) := by
        rw [← h2]; exact mul_le_mul_of_nonneg_left h1 hjp
    _ = B ^ 2 * Lattice.jp j.1 ^ (-(2 * (m - m'))) := by
        rw [show -(2 * (m - m')) = 2 * m' + -(2 * m) by ring, Real.rpow_add (Torus.jp_pos _)]
        ring

/-- From the `L¹`-bound of `N * Z` to the `L¹`-bound of `√N * Z`. -/
theorem adjkd_y_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : ℕ} (hN : 0 < N)
    {Z : Ω → ℝ} (hZ : Integrable (fun ω => (N : ℝ) * Z ω) P) {K : ℝ}
    (hb : ∫ ω, |(N : ℝ) * Z ω| ∂P ≤ K) :
    ∫⁻ ω, ‖Real.sqrt N * Z ω‖ₑ ∂P ≤ ENNReal.ofReal (K / Real.sqrt N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.2 hNr
  have e : ∀ ω, Real.sqrt N * Z ω = (1 / Real.sqrt N) * ((N : ℝ) * Z ω) := by
    intro ω
    field_simp
    rw [Real.sq_sqrt hNr.le]
    ring
  have hK0 : 0 ≤ K := le_trans (integral_nonneg fun ω => abs_nonneg _) hb
  simp_rw [e]
  have h1 : ∀ ω, ‖(1 / Real.sqrt N) * ((N : ℝ) * Z ω)‖ₑ =
      ENNReal.ofReal (1 / Real.sqrt N) * ‖(N : ℝ) * Z ω‖ₑ := by
    intro ω
    rw [enorm_mul, ← ofReal_norm_eq_enorm, Real.norm_eq_abs, abs_of_pos (by positivity)]
  simp_rw [h1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have h2 : ∫⁻ ω, ‖(N : ℝ) * Z ω‖ₑ ∂P = ENNReal.ofReal (∫ ω, ‖(N : ℝ) * Z ω‖ ∂P) :=
    (ofReal_integral_norm_eq_lintegral_enorm hZ).symm
  rw [h2]
  have h3 : ∫ ω, ‖(N : ℝ) * Z ω‖ ∂P ≤ K := by simpa [Real.norm_eq_abs] using hb
  calc ENNReal.ofReal (1 / Real.sqrt N) * ENNReal.ofReal (∫ ω, ‖(N : ℝ) * Z ω‖ ∂P)
      ≤ ENNReal.ofReal (1 / Real.sqrt N) * ENNReal.ofReal K :=
        mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal h3)
    _ = ENNReal.ofReal (K / Real.sqrt N) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

end HRS.AdjK
