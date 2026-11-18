import HRS.Commutator.Torus.TEN2Aux3

/-!
# Torus energy layer (packet T-EN2), helper part 4: pointwise bound on the periodisation

Prefix `ten2_`.  `perio f_η (x) ≤ f_η(centeredRep x) + K₁ η^{2d+4-s}`: the images other than the nearest one
are at distance `≥ |m|/(2√d)` and `f_η(z) ≲ η^{2d+4-s}|z|^{-(2d+4)}`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s η : ℝ}

/-- The constant `K₁` of the tail bound. -/
def ten2K1 (d : ℕ) (s : ℝ) : ℝ :=
  Whole.cPhi d s / (2 * (d : ℝ) + 4 - s) *
    ((2 * Real.sqrt d) ^ (2 * (d : ℝ) + 4) * ∑' m : Lattice d, ‖Lattice.toEuc m‖ ^ (-(2 * (d : ℝ) + 4)))

theorem ten2K1_nonneg (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) : 0 ≤ ten2K1 d s := by
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hs2 : s < 2 * (d : ℝ) + 4 := by linarith
  have hcp := Whole.cPhi_pos d hs0 hs2
  have h2 : (0 : ℝ) < 2 * (d : ℝ) + 4 - s := by linarith
  have hZ : 0 ≤ ∑' m : Lattice d, ‖Lattice.toEuc m‖ ^ (-(2 * (d : ℝ) + 4)) :=
    tsum_nonneg fun m => by positivity
  unfold ten2K1
  positivity

theorem ten2_perio_le (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (hη : 0 < η) (x : Torus d) :
    perio (Whole.fTrunc s η : Euc d → ℝ) x ≤
      Whole.fTrunc s η (KernelGrad.centeredRep x) + ten2K1 d s * η ^ (2 * (d : ℝ) + 4 - s) := by
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hs2 : s < 2 * (d : ℝ) + 4 := by linarith
  set c := KernelGrad.centeredRep x with hcdef
  have hc : ∀ i, |c i| ≤ 1 / 2 := fun i => KernelGrad.abs_centeredRep_le x i
  obtain ⟨m0, hm0⟩ := tpos_centeredRep_eq x
  have hm0' : c = Torus.rep x + Lattice.toEuc m0 := hm0
  set f : Euc d → ℝ := Whole.fTrunc s η with hf
  set g : Lattice d → ℝ := fun m => f (c + Lattice.toEuc m) with hg
  have hgsum : Summable g := tpos_fTrunc_summable hs0 hsd hη c
  have hgnn : ∀ m, 0 ≤ g m := fun m => tpos_fTrunc_nonneg hs0 hs2 η _
  have h1 : perio f x = ∑' m, g m := by
    unfold perio
    calc ∑' m : Lattice d, f (Torus.rep x + Lattice.toEuc m)
        = ∑' m : Lattice d, g (m - m0) := by
          refine tsum_congr fun m => ?_
          simp only [hg]
          congr 1
          rw [hm0', ten2_toEuc_sub]
          abel
      _ = ∑' m, g m := (Equiv.subRight m0).tsum_eq g
  have h2 : ∑' m, g m = f c + ∑' m, if m = 0 then 0 else g m := by
    have := hgsum.tsum_eq_add_tsum_ite 0
    rw [this]
    simp [hg, ten2_toEuc_zero]
  -- termwise tail bound
  set r : ℝ := 2 * (d : ℝ) + 4 with hr
  have hr0 : 0 < r := by positivity
  set B : ℝ := 2 * Real.sqrt d with hB
  have hB0 : 0 < B := by positivity
  set A : ℝ := Whole.cPhi d s / (2 * (d : ℝ) + 4 - s) with hA
  have hcp := Whole.cPhi_pos d hs0 hs2
  have h2' : (0 : ℝ) < 2 * (d : ℝ) + 4 - s := by linarith
  have hA0 : 0 ≤ A := by positivity
  have hterm : ∀ m : Lattice d, (if m = 0 then 0 else g m) ≤
      (A * η ^ (2 * (d : ℝ) + 4 - s) * B ^ r) * ‖Lattice.toEuc m‖ ^ (-r) := by
    intro m
    by_cases hm : m = 0
    · subst hm
      have : (Lattice.toEuc (0 : Lattice d)) = 0 := ten2_toEuc_zero
      simp [this, Real.zero_rpow (show -r ≠ 0 by linarith)]
    · simp only [hm, ite_false]
      have hle := ten2_norm_le_of_cube hc hm
      have hmpos : 0 < ‖Lattice.toEuc m‖ := tpos_toEuc_ne_zero hm
      have hupos : 0 < ‖c + Lattice.toEuc m‖ := by
        have : 0 < 2 * Real.sqrt d * ‖c + Lattice.toEuc m‖ := lt_of_lt_of_le hmpos hle
        exact (pos_iff_pos_of_mul_pos this).1 (by positivity)
      have hne : c + Lattice.toEuc m ≠ 0 := norm_pos_iff.1 hupos
      have h3 := tpos_fTrunc_le (d := d) hs0 hs2 hη hne
      have h4 : ‖c + Lattice.toEuc m‖ ^ (-r) ≤ B ^ r * ‖Lattice.toEuc m‖ ^ (-r) := by
        have h5 : (B * ‖c + Lattice.toEuc m‖) ^ (-r) ≤ ‖Lattice.toEuc m‖ ^ (-r) :=
          Real.rpow_le_rpow_of_nonpos hmpos hle (by linarith)
        rw [Real.mul_rpow hB0.le hupos.le] at h5
        have h6 : B ^ r * B ^ (-r) = 1 := by
          rw [← Real.rpow_add hB0]; simp
        calc ‖c + Lattice.toEuc m‖ ^ (-r)
            = B ^ r * (B ^ (-r) * ‖c + Lattice.toEuc m‖ ^ (-r)) := by
              rw [← mul_assoc, h6, one_mul]
          _ ≤ B ^ r * ‖Lattice.toEuc m‖ ^ (-r) := mul_le_mul_of_nonneg_left h5 (by positivity)
      calc g m = f (c + Lattice.toEuc m) := rfl
        _ ≤ A * η ^ (2 * (d : ℝ) + 4 - s) * ‖c + Lattice.toEuc m‖ ^ (-r) := h3
        _ ≤ A * η ^ (2 * (d : ℝ) + 4 - s) * (B ^ r * ‖Lattice.toEuc m‖ ^ (-r)) :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = _ := by ring
  have hsumB : Summable (fun m : Lattice d => (A * η ^ (2 * (d : ℝ) + 4 - s) * B ^ r) *
      ‖Lattice.toEuc m‖ ^ (-r)) :=
    (tpos_summable_rpow (d := d) (r := r) (by rw [hr]; linarith)).mul_left _
  have hsumI : Summable (fun m : Lattice d => if m = 0 then (0 : ℝ) else g m) :=
    Summable.of_nonneg_of_le (fun m => by by_cases hm : m = 0 <;> simp [hm, hgnn]) hterm hsumB
  have h7 : ∑' m : Lattice d, (if m = 0 then (0 : ℝ) else g m) ≤
      ten2K1 d s * η ^ (2 * (d : ℝ) + 4 - s) := by
    calc ∑' m : Lattice d, (if m = 0 then (0 : ℝ) else g m)
        ≤ ∑' m : Lattice d, (A * η ^ (2 * (d : ℝ) + 4 - s) * B ^ r) * ‖Lattice.toEuc m‖ ^ (-r) :=
          hsumI.tsum_le_tsum hterm hsumB
      _ = (A * η ^ (2 * (d : ℝ) + 4 - s) * B ^ r) * ∑' m : Lattice d, ‖Lattice.toEuc m‖ ^ (-r) :=
          tsum_mul_left
      _ = ten2K1 d s * η ^ (2 * (d : ℝ) + 4 - s) := by
          unfold ten2K1
          simp only [hA, hB, hr]
          ring
  rw [h1, h2]
  linarith

end HRS.Commutator.TorusNote
