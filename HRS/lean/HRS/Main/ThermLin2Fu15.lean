import HRS.Main.ThermLin2Fu14

/-!
# THERMLIN2 Fu15: duality bound `|⟨z, ψ⟩| ≤ ‖z‖_{E_{m-b}} ‖ψ‖_{H^{m-b}}` (in `ℝ≥0∞`, with `tl2NormShift`)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P HRS.Uniform.Q54c

variable {d : ℕ}

theorem tl2fu_eval_le_shift {m : ℝ} (b : ℝ) (z : NegSobolev d m) {ψ : Torus d → ℝ}
    (hψ : MemSobolev (m - b) ψ) :
    ENNReal.ofReal |NegSobolev.eval z ψ| ≤
      tl2NormShift m b z * ENNReal.ofReal (sobolevNorm (m - b) ψ) := by
  set u : NonzeroLattice d → ℝ := fun k => Lattice.jp k.1 ^ b * NegSobolev.coord z k with hu
  set v : NonzeroLattice d → ℝ := fun k => Lattice.jp k.1 ^ (m - b) * Torus.funRealCoeff ψ k with hv
  have hv2 : Summable fun k => v k ^ 2 := by
    refine hψ.2.congr fun k => ?_
    simp only [hv]; rw [mul_pow, Torus.jp_rpow_sq]
  have e : NegSobolev.eval z ψ = ∑' k, u k * v k := by
    unfold NegSobolev.eval NegSobolev.fourierCoeff
    refine tsum_congr fun k => ?_
    simp only [hu, hv]
    have : Lattice.jp k.1 ^ m = Lattice.jp k.1 ^ b * Lattice.jp k.1 ^ (m - b) := by
      rw [← Real.rpow_add (Torus.jp_pos _)]; ring_nf
    rw [this]; ring
  have hs0 : 0 ≤ sobolevNorm (m - b) ψ := Real.sqrt_nonneg _
  have hsn : Real.sqrt (∑' k, v k ^ 2) ≤ sobolevNorm (m - b) ψ := by
    unfold sobolevNorm
    refine Real.sqrt_le_sqrt ?_
    have : ∑' k, v k ^ 2 = ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * (m - b)) * Torus.funRealCoeff ψ k ^ 2 :=
      tsum_congr fun k => by simp only [hv]; rw [mul_pow, Torus.jp_rpow_sq]
    rw [this]
    nlinarith [sq_nonneg (Torus.mean ψ)]
  have hterm : ∀ k, ENNReal.ofReal (Lattice.jp k.1 ^ (2 * b) * NegSobolev.coord z k ^ 2) = ENNReal.ofReal (u k ^ 2) :=
    fun k => by simp only [hu]; rw [mul_pow, Torus.jp_rpow_sq]
  by_cases hfin : ∑' k : NonzeroLattice d, ENNReal.ofReal (u k ^ 2) = ⊤
  · have hN : tl2NormShift m b z = ⊤ := by
      unfold tl2NormShift
      simp_rw [hterm]
      rw [hfin]
      exact ENNReal.top_rpow_of_pos (by norm_num)
    rw [hN]
    by_cases hs : sobolevNorm (m - b) ψ = 0
    · have hS : ∑' k, v k ^ 2 = 0 := by
        have h1 : Real.sqrt (∑' k, v k ^ 2) = 0 := le_antisymm (hs ▸ hsn) (Real.sqrt_nonneg _)
        exact (Real.sqrt_eq_zero (tsum_nonneg fun k => sq_nonneg _)).1 h1
      have hv0 : ∀ k, v k = 0 := by
        intro k
        have := hv2.le_tsum k (fun j _ => sq_nonneg _)
        rw [hS] at this
        exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm this (sq_nonneg _))
      rw [e]
      simp [hv0]
    · have : 0 < ENNReal.ofReal (sobolevNorm (m - b) ψ) := ENNReal.ofReal_pos.2 (lt_of_le_of_ne hs0 (Ne.symm hs))
      rw [ENNReal.top_mul this.ne']
      exact le_top
  · have hu2 : Summable fun k => u k ^ 2 := by
      have := ENNReal.summable_toReal hfin
      refine this.congr fun k => ?_
      rw [ENNReal.toReal_ofReal (sq_nonneg _)]
    have hN : tl2NormShift m b z = ENNReal.ofReal (Real.sqrt (∑' k, u k ^ 2)) := by
      unfold tl2NormShift
      simp_rw [hterm]
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg _) hu2,
        ENNReal.ofReal_rpow_of_nonneg (tsum_nonneg fun k => sq_nonneg _) (by norm_num),
        Real.sqrt_eq_rpow]
    rw [hN, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hcs := Torus.cs_tsum (fun k => |u k|) (fun k => |v k|) (fun _ => abs_nonneg _) (fun _ => abs_nonneg _)
      (by simpa [sq_abs] using hu2) (by simpa [sq_abs] using hv2)
    rw [e]
    have h1 : |∑' k, u k * v k| ≤ ∑' k, |u k| * |v k| := by
      have hs : Summable fun k => ‖u k * v k‖ := by simpa [abs_mul] using hcs.1
      simpa [abs_mul] using norm_tsum_le_tsum_norm hs
    refine h1.trans (hcs.2.trans ?_)
    simp only [sq_abs]
    exact mul_le_mul_of_nonneg_left hsn (Real.sqrt_nonneg _)

end HRS.ThermLin.Plan2
