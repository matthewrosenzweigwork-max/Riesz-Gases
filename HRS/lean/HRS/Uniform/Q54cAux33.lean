import HRS.Uniform.Q54cAux32

/-!
# Q54c, part 33: termwise differentiation of the real Fourier series
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q54c

open HRS HRS.PDE HRS.Torus

variable {d : ℕ}

open Classical in
/-- the derivative of `lift (realMode k)` in the direction `e_j` at `z`. -/
def Dmode (k : NonzeroLattice d) (j : Fin d) (z : Euc d) : ℝ :=
  2 * Real.pi * (k.1 j : ℝ) * Real.sqrt 2 *
    (if Lattice.IsPosHalf k.1 then -Real.sin (Torus.freqFunctional k.1 z)
      else Real.cos (Torus.freqFunctional k.1 z))

theorem freq_single (k : Lattice d) (j : Fin d) :
    Torus.freqFunctional k (EuclideanSpace.single j 1) = 2 * Real.pi * (k j : ℝ) := by
  rw [Torus.freqFunctional_apply]
  simp [Lattice.dot, PiLp.single_apply]

open Classical in
theorem lift_realMode_pos {k : NonzeroLattice d} (hp : Lattice.IsPosHalf k.1) (z : Euc d) :
    Torus.lift (Torus.realMode k) z = Real.sqrt 2 * Real.cos (Torus.freqFunctional k.1 z) := by
  simp [Torus.lift, Torus.realMode, hp, Torus.cosMode_mk, Torus.freqFunctional_apply]

open Classical in
theorem lift_realMode_neg {k : NonzeroLattice d} (hp : ¬ Lattice.IsPosHalf k.1) (z : Euc d) :
    Torus.lift (Torus.realMode k) z = Real.sqrt 2 * Real.sin (Torus.freqFunctional k.1 z) := by
  simp [Torus.lift, Torus.realMode, hp, Torus.sinMode_mk, Torus.freqFunctional_apply]

open Classical in
theorem hasDerivAt_lift_realMode (k : NonzeroLattice d) (j : Fin d) (z : Euc d) (s : ℝ) :
    HasDerivAt (fun s : ℝ => Torus.lift (Torus.realMode k) (z + s • EuclideanSpace.single j 1))
      (Dmode k j (z + s • EuclideanSpace.single j 1)) s := by
  have hf : ∀ s : ℝ, Torus.freqFunctional k.1 (z + s • EuclideanSpace.single j 1) =
      Torus.freqFunctional k.1 z + s * (2 * Real.pi * (k.1 j : ℝ)) := by
    intro s
    rw [map_add, map_smul, freq_single]; simp
  have hlin : HasDerivAt (fun s : ℝ => Torus.freqFunctional k.1 z + s * (2 * Real.pi * (k.1 j : ℝ)))
      (2 * Real.pi * (k.1 j : ℝ)) s := by
    simpa using ((hasDerivAt_id s).mul_const (2 * Real.pi * (k.1 j : ℝ))).const_add
      (Torus.freqFunctional k.1 z)
  by_cases hp : Lattice.IsPosHalf k.1
  · have hl : (fun s : ℝ => Torus.lift (Torus.realMode k) (z + s • EuclideanSpace.single j 1)) =
        fun s => Real.sqrt 2 * Real.cos (Torus.freqFunctional k.1 z + s * (2 * Real.pi * (k.1 j : ℝ))) := by
      funext s
      rw [lift_realMode_pos hp, hf s]
    rw [hl]
    have := (hlin.cos).const_mul (Real.sqrt 2)
    convert this using 1
    simp only [Dmode, hp, ite_true, ← hf s]
    ring
  · have hl : (fun s : ℝ => Torus.lift (Torus.realMode k) (z + s • EuclideanSpace.single j 1)) =
        fun s => Real.sqrt 2 * Real.sin (Torus.freqFunctional k.1 z + s * (2 * Real.pi * (k.1 j : ℝ))) := by
      funext s
      rw [lift_realMode_neg hp, hf s]
    rw [hl]
    have := (hlin.sin).const_mul (Real.sqrt 2)
    convert this using 1
    simp only [Dmode, hp, ite_false, ← hf s]
    ring

open Classical in
theorem abs_Dmode_le (k : NonzeroLattice d) (j : Fin d) (z : Euc d) :
    |Dmode k j z| ≤ Real.sqrt 2 * Lattice.jp k.1 := by
  unfold Dmode
  rw [abs_mul, abs_mul, abs_mul]
  have hs : |(if Lattice.IsPosHalf k.1 then -Real.sin (Torus.freqFunctional k.1 z)
      else Real.cos (Torus.freqFunctional k.1 z))| ≤ 1 := by
    split_ifs
    · rw [abs_neg]; exact Real.abs_sin_le_one _
    · exact Real.abs_cos_le_one _
  have h2 : |(2 : ℝ) * Real.pi| * |(k.1 j : ℝ)| ≤ Lattice.jp k.1 := by
    rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    exact HRS.Uniform.Q14.q14_two_pi_k_le k.1 j
  rw [abs_of_nonneg (Real.sqrt_nonneg 2)]
  calc |(2 : ℝ) * Real.pi| * |(k.1 j : ℝ)| * Real.sqrt 2 * _ ≤
      Lattice.jp k.1 * Real.sqrt 2 * 1 := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg 2)) hs (abs_nonneg _)
          (by have := Torus.jp_ge_one k.1; positivity)
    _ = _ := by ring

end HRS.Uniform.Q54c
