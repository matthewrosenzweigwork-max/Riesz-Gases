import HRS.Sections.Q38bAux4

/-!
# EQ-INITMOM, base: an `E_M`-second moment from coordinatewise second moments

If `F : Ω → E_M` is measurable with `∫⁻ ofReal (F_k²) ≤ ofReal (B ⟨k⟩^{-2M})` for every coordinate `k`
(`F_k` the weighted `ℓ²`-coordinate), then `∫⁻ ‖F‖ₑ² ≤ ofReal (B ∑_k ⟨k⟩^{-2M})`; the series converges for `2M > d`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MD.EQInit

variable {d : ℕ}

theorem eqinit_lintegral_enorm_sq_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {M : ℝ}
    (hM : (d : ℝ) < 2 * M) (F : Ω → NegSobolev d M) (hF : Measurable F) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ k : NonzeroLattice d,
      ∫⁻ ω, ENNReal.ofReal (NegSobolev.coord (F ω) k ^ 2) ∂P ≤
        ENNReal.ofReal (B * Lattice.jp k.1 ^ (-(2 * M)))) :
    ∫⁻ ω, ‖F ω‖ₑ ^ 2 ∂P ≤
      ENNReal.ofReal (B * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * M))) := by
  have hS := summable_jp_rpow (d := d) M hM
  have hS0 : ∀ k : NonzeroLattice d, 0 ≤ Lattice.jp k.1 ^ (-(2 * M)) := fun k =>
    Real.rpow_nonneg (Torus.jp_pos _).le _
  have e1 : ∀ ω, ‖F ω‖ₑ ^ 2 = ∑' k : NonzeroLattice d, ENNReal.ofReal (NegSobolev.coord (F ω) k ^ 2) := by
    intro ω
    obtain ⟨hsum, hnorm⟩ := NegSobolev.coord_sq (F ω)
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _), hnorm,
      ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg _) hsum]
  simp_rw [e1]
  rw [lintegral_tsum]
  · calc ∑' k : NonzeroLattice d, ∫⁻ ω, ENNReal.ofReal (NegSobolev.coord (F ω) k ^ 2) ∂P
        ≤ ∑' k : NonzeroLattice d, ENNReal.ofReal (B * Lattice.jp k.1 ^ (-(2 * M))) :=
          ENNReal.tsum_le_tsum h
      _ = ENNReal.ofReal (∑' k : NonzeroLattice d, B * Lattice.jp k.1 ^ (-(2 * M))) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg hB (hS0 k)) (hS.mul_left B)).symm
      _ = _ := by rw [tsum_mul_left]
  · intro k
    exact ((q38b_continuous_coord k).measurable.comp hF |>.pow_const 2).ennreal_ofReal.aemeasurable

end HRS.MD.EQInit
