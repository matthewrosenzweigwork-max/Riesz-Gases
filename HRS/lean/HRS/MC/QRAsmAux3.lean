import HRS.MC.QRVocab
import HRS.MC.QRAsmAux2
import HRS.MC.QRPMargAux2

/-!
# QRAsm, auxiliary file 3: the cube of frequencies and the low-frequency part of the mode estimate
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace HRS.MC.QRSpec.Asm

variable {Ω : Type} [MeasurableSpace Ω]

/-! ### The cube `{a ≠ 0 : |a_i| ≤ L}` -/

/-- The finite set of nonzero frequencies in the cube of side `L`. -/
def asmCube (d L : ℕ) : Finset (NonzeroLattice d) :=
  (Fintype.piFinset fun _ : Fin d => Finset.Icc (-(L : ℤ)) (L : ℤ)).subtype (fun k : Lattice d => k ≠ 0)

lemma mem_asmCube {d L : ℕ} {a : NonzeroLattice d} : a ∈ asmCube d L ↔ ∀ i, |a.1 i| ≤ (L : ℤ) := by
  simp [asmCube, Finset.mem_subtype, Fintype.mem_piFinset, abs_le]

lemma card_asmCube_le (d L : ℕ) : ((asmCube d L).card : ℝ) ≤ ((2 * L + 1 : ℕ) : ℝ) ^ d := by
  have h : (asmCube d L).card ≤ (2 * L + 1) ^ d := by
    unfold asmCube
    rw [Finset.card_subtype]
    refine (Finset.card_filter_le _ _).trans ?_
    rw [Fintype.card_piFinset]
    simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    refine le_of_eq ?_
    congr 1
    omega
  exact_mod_cast h

lemma asm_enorm_le_cube {d L : ℕ} (a : Lattice d) (h : ∀ i, |a i| ≤ (L : ℤ)) :
    Lattice.enorm a ≤ Real.sqrt d * L := by
  unfold Lattice.enorm Lattice.toEuc
  rw [EuclideanSpace.norm_eq]
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  rw [show Real.sqrt d * L = Real.sqrt (d * (L : ℝ) ^ 2) by
    rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq hL]]
  refine Real.sqrt_le_sqrt ?_
  have : ∀ i : Fin d, ‖((a i : ℤ) : ℝ)‖ ^ 2 ≤ (L : ℝ) ^ 2 := by
    intro i
    rw [Real.norm_eq_abs]
    have : |((a i : ℤ) : ℝ)| ≤ L := by exact_mod_cast h i
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  calc ∑ i : Fin d, ‖((a i : ℤ) : ℝ)‖ ^ 2 ≤ ∑ _i : Fin d, (L : ℝ) ^ 2 := Finset.sum_le_sum fun i _ => this i
    _ = d * (L : ℝ) ^ 2 := by simp

/-- `⟨a⟩ ≤ J L` on the cube, `J = 1 + 2π√d`. -/
lemma asm_jp_le_cube {d L : ℕ} (hL : 1 ≤ L) (a : Lattice d) (h : ∀ i, |a i| ≤ (L : ℤ)) :
    Lattice.jp a ≤ (1 + 2 * Real.pi * Real.sqrt d) * L := by
  have he := asm_enorm_le_cube a h
  have he0 : 0 ≤ Lattice.enorm a := norm_nonneg _
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hpi := Real.pi_pos
  have h1 : Lattice.jp a ≤ 1 + 2 * Real.pi * Lattice.enorm a := by
    unfold Lattice.jp
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [mul_nonneg hpi.le he0]
  have h2 : 2 * Real.pi * Lattice.enorm a ≤ 2 * Real.pi * (Real.sqrt d * L) :=
    mul_le_mul_of_nonneg_left he (by positivity)
  have hs : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  nlinarith [mul_nonneg hpi.le hs, mul_nonneg (mul_nonneg hpi.le hs) (sub_nonneg.2 hL1)]

/-- `(∑_{a ∈ cube} ⟨a⟩^r)² ≤ Z L^{2d+2r}`. -/
lemma asm_sum_w_sq {d L : ℕ} (hL : 1 ≤ L) {r : ℝ} (hr : 0 ≤ r) :
    (∑ a ∈ asmCube d L, Lattice.jp a.1 ^ r) ^ 2 ≤
      ((3 : ℝ) ^ d * (1 + 2 * Real.pi * Real.sqrt d) ^ r) ^ 2 * (L : ℝ) ^ (2 * (d : ℝ) + 2 * r) := by
  set J : ℝ := 1 + 2 * Real.pi * Real.sqrt d with hJ
  have hJ0 : 0 ≤ J := by positivity
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hterm : ∀ a ∈ asmCube d L, Lattice.jp a.1 ^ r ≤ J ^ r * (L : ℝ) ^ r := by
    intro a ha
    rw [← Real.mul_rpow hJ0 hL0.le]
    exact Real.rpow_le_rpow (Torus.jp_pos a.1).le (asm_jp_le_cube hL a.1 (mem_asmCube.1 ha)) hr
  have hsum : ∑ a ∈ asmCube d L, Lattice.jp a.1 ^ r ≤ (3 : ℝ) ^ d * J ^ r * ((L : ℝ) ^ (d : ℝ) * (L : ℝ) ^ r) := by
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hc := card_asmCube_le d L
    have h2 : ((2 * L + 1 : ℕ) : ℝ) ≤ 3 * L := by push_cast; linarith
    have hc2 : ((asmCube d L).card : ℝ) ≤ (3 * (L : ℝ)) ^ d :=
      hc.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) h2 d)
    have hpos : 0 ≤ J ^ r * (L : ℝ) ^ r := by positivity
    calc ((asmCube d L).card : ℝ) * (J ^ r * (L : ℝ) ^ r) ≤ (3 * (L : ℝ)) ^ d * (J ^ r * (L : ℝ) ^ r) :=
          mul_le_mul_of_nonneg_right hc2 hpos
      _ = _ := by
          rw [mul_pow, Real.rpow_natCast]
          ring
  have h0 : 0 ≤ ∑ a ∈ asmCube d L, Lattice.jp a.1 ^ r :=
    Finset.sum_nonneg fun a _ => Real.rpow_nonneg (Torus.jp_pos a.1).le _
  calc (∑ a ∈ asmCube d L, Lattice.jp a.1 ^ r) ^ 2 ≤ ((3 : ℝ) ^ d * J ^ r * ((L : ℝ) ^ (d : ℝ) * (L : ℝ) ^ r)) ^ 2 :=
        pow_le_pow_left₀ h0 hsum 2
    _ = ((3 : ℝ) ^ d * J ^ r) ^ 2 * (L : ℝ) ^ (2 * (d : ℝ) + 2 * r) := by
        rw [mul_pow, ← Real.rpow_add hL0, show 2 * (d : ℝ) + 2 * r = ((d : ℝ) + r) * 2 by ring,
          Real.rpow_mul hL0.le, Real.rpow_two]

/-! ### Coefficients from the `E_r`-norm -/

section Er

variable {d : ℕ} {r : ℝ}

lemma asm_fc_eLpNorm {P : Measure Ω} (Z : Ω → NegSobolev d r) (hZm : Measurable Z) (q : ℝ≥0∞) (N : ℝ) (a : NonzeroLattice d)
    (h : eLpNorm (fun ω => ‖Z ω‖) q P ≤ ENNReal.ofReal N) :
    eLpNorm (fun ω => NegSobolev.fourierCoeff (Z ω) a) q P ≤
      ENNReal.ofReal (Lattice.jp a.1 ^ r * N) := by
  have hj : 0 ≤ Lattice.jp a.1 ^ r := Real.rpow_nonneg (Torus.jp_pos a.1).le _
  have h1 : eLpNorm (fun ω => NegSobolev.fourierCoeff (Z ω) a) q P ≤
      eLpNorm (Lattice.jp a.1 ^ r • fun ω => ‖Z ω‖) q P := by
    refine eLpNorm_mono (asm_meas_fc hZm a).aestronglyMeasurable fun ω => ?_
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs, abs_norm, abs_of_nonneg hj]
    exact asm_fc_abs_le (Z ω) a
  refine h1.trans ?_
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hj, ENNReal.ofReal_mul hj]
  exact mul_le_mul' le_rfl h

end Er

end HRS.MC.QRSpec.Asm

end
