import HRS.Main.GFEVAux16

/-!
# Packet GFEVG, part 17: the core `D = E_{γ-4} ⊂ E_γ`, the operator `A`, interpolation
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.GF

open HRS HRS.PDE HRS.PDE.ET HRS.Uniform HRS.Uniform.Q54 HRS.Uniform.Q48b

variable {d : ℕ}

theorem gfev_coord_eq_fc {m : ℝ} (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord F k = Lattice.jp k.1 ^ (-m) * NegSobolev.fourierCoeff F k := by
  unfold NegSobolev.fourierCoeff
  rw [← mul_assoc, ← Real.rpow_add (Torus.jp_pos k.1)]
  simp

/-- Interpolation: `‖embed b e‖² ≤ ‖e‖ ‖embed c e‖` for `b = (a + c)/2`. -/
theorem gfev_interp {a b c : ℝ} (hb : b = (a + c) / 2) (hac : a ≤ c) (e : NegSobolev d a) :
    ‖NegSobolev.embed b e‖ ^ 2 ≤ ‖e‖ * ‖NegSobolev.embed c e‖ := by
  have hab : a ≤ b := by rw [hb]; linarith
  set x : NonzeroLattice d → ℝ := fun k => |NegSobolev.coord e k| with hx
  set y : NonzeroLattice d → ℝ := fun k => |NegSobolev.coord (NegSobolev.embed c e) k| with hy
  obtain ⟨hs1, hn1⟩ := NegSobolev.coord_sq e
  obtain ⟨hs2, hn2⟩ := NegSobolev.coord_sq (NegSobolev.embed c e)
  obtain ⟨hs3, hn3⟩ := NegSobolev.coord_sq (NegSobolev.embed b e)
  have hpt : ∀ k, NegSobolev.coord (NegSobolev.embed b e) k ^ 2 = x k * y k := by
    intro k
    have hj := Torus.jp_pos k.1
    have e1 := gfev_coord_embed hab e k
    have e2 := gfev_coord_embed hac e k
    have e3 := gfev_coord_eq_fc e k
    simp only [hx, hy]
    rw [e1, e2, e3, abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hj _),
      abs_of_pos (Real.rpow_pos_of_pos hj _)]
    set f := NegSobolev.fourierCoeff e k
    have h5 : Lattice.jp k.1 ^ (-b) * Lattice.jp k.1 ^ (-b) = Lattice.jp k.1 ^ (-a) * Lattice.jp k.1 ^ (-c) := by
      rw [← Real.rpow_add hj, ← Real.rpow_add hj]; congr 1; rw [hb]; ring
    calc (Lattice.jp k.1 ^ (-b) * f) ^ 2 = (Lattice.jp k.1 ^ (-b) * Lattice.jp k.1 ^ (-b)) * (f * f) := by ring
      _ = (Lattice.jp k.1 ^ (-a) * Lattice.jp k.1 ^ (-c)) * (|f| * |f|) := by rw [h5, abs_mul_abs_self]
      _ = _ := by ring
  have hcs := Torus.cs_tsum x y (fun _ => abs_nonneg _) (fun _ => abs_nonneg _)
    (by simpa [hx, sq_abs] using hs1) (by simpa [hy, sq_abs] using hs2)
  have h1 : ‖NegSobolev.embed b e‖ ^ 2 = ∑' k, x k * y k := by
    rw [hn3]; exact tsum_congr hpt
  rw [h1]
  refine hcs.2.trans (le_of_eq ?_)
  have e1 : Real.sqrt (∑' k, x k ^ 2) = ‖e‖ := by
    rw [← Real.sqrt_sq (norm_nonneg e), hn1]; congr 1; exact tsum_congr fun k => sq_abs _
  have e2 : Real.sqrt (∑' k, y k ^ 2) = ‖NegSobolev.embed c e‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (NegSobolev.embed c e)), hn2]; congr 1; exact tsum_congr fun k => sq_abs _
  rw [e1, e2]

end HRS.GF
