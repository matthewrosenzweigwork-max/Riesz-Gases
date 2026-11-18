import HRS.Sections.QuenchAux23

/-!
# Packet QUENCH (Q27), part 24: the window series identity (`E:eq:window-spectral`)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Qch

open HRS.Sec7

variable {d : ℕ}

section Series

variable {s β β₀ m T : ℝ}

/-- `t ↦ e^{-λ t}` on `[0,T]`. -/
def fexp (lam T : ℝ) : C(Set.Icc (0 : ℝ) T, ℝ) := ⟨fun t => Real.exp (-lam * (t : ℝ)), by fun_prop⟩

lemma fexp_apply (lam : ℝ) (t : Set.Icc (0 : ℝ) T) : fexp lam T t = Real.exp (-lam * (t : ℝ)) := rfl

lemma norm_fexp_le {lam : ℝ} (hlam : 0 ≤ lam) : ‖fexp lam T‖ ≤ 1 := by
  refine (ContinuousMap.norm_le _ zero_le_one).2 fun t => ?_
  rw [fexp_apply, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.2 (by nlinarith [t.2.1])

lemma modePath_eq (k : PosHalf d) (b : Bool) (lam : ℝ) (hl : lam = lamMode d s β k.1) :
    modePath m T lam (modeFn k.1 b) =
      (sgn b * Lattice.jp k.1 ^ (-m)) • (pathOf (m := m) (fexp lam T) (idx k b) : PathSpace d m T) := by
  have hj := jp_idx k b
  refine ContinuousMap.ext fun t => ?_
  show Real.exp (-lam * (t : ℝ)) • NegSobolev.ofFun m (modeFn k.1 b) =
    (sgn b * Lattice.jp k.1 ^ (-m)) • (fexp lam T t • esingle m (idx k b))
  rw [modeFn_eq k b, ofFun_mode, fexp_apply, smul_smul, smul_smul, hj]
  congr 1
  ring

lemma norm_modePath_le (k : PosHalf d) (b : Bool) {lam : ℝ} (hl : 0 ≤ lam) (hl' : lam = lamMode d s β k.1) :
    ‖modePath m T lam (modeFn k.1 b)‖ ≤ Lattice.jp k.1 ^ (-m) := by
  rw [modePath_eq k b lam hl', norm_smul]
  have h1 := norm_pathOf_le (m := m) (fexp lam T) (idx k b)
  have h2 := norm_fexp_le (T := T) hl
  have h3 : ‖sgn b * Lattice.jp k.1 ^ (-m)‖ = Lattice.jp k.1 ^ (-m) := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (Torus.jp_pos _) _)]
    cases b <;> simp [sgn]
  rw [h3]
  calc Lattice.jp k.1 ^ (-m) * ‖(pathOf (fexp lam T) (idx k b) : PathSpace d m T)‖
      ≤ Lattice.jp k.1 ^ (-m) * 1 :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (Real.rpow_nonneg (Torus.jp_pos _).le _)
    _ = _ := mul_one _

lemma lamMode_idx' (s β : ℝ) (k : PosHalf d) (b : Bool) : lamMode d s β (idx k b).1 = lamMode d s β k.1 := by
  unfold lamMode; rw [enorm_idx, rieszCoeff_idx]

lemma deltaVar_idx' (s β β₀ : ℝ) (k : PosHalf d) (b : Bool) :
    deltaVar d s β β₀ (idx k b).1 = deltaVar d s β β₀ k.1 := (deltaVar_idx β β₀ k b).symm

lemma M_smul (M : PathSpace d m T [×2]→L[ℝ] ℝ) (c : ℝ) (x : PathSpace d m T) :
    M ![c • x, c • x] = c ^ 2 * M ![x, x] := by
  rw [← bilinOfMulti_apply, ← bilinOfMulti_apply]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

/-- sum over the indices `(k,b)`. -/
lemma tsum_idx (F : NonzeroLattice d → ℝ) (hF : Summable F) :
    ∑' j, F j = ∑' k : PosHalf d, (F (idx k true) + F (idx k false)) := by
  have h1 : Summable (fun c => F (equiv d c)) := (equiv d).summable_iff.2 hF
  rw [← (equiv d).tsum_eq F, h1.tsum_prod]
  refine tsum_congr fun k => ?_
  rw [tsum_fintype, Fintype.sum_bool]
  rfl

lemma summable_idx (F : NonzeroLattice d → ℝ) (hF : Summable F) :
    Summable fun k : PosHalf d => (F (idx k true) + F (idx k false)) := by
  have h1 : Summable (F ∘ (equiv d)) := (equiv d).summable_iff.2 hF
  refine h1.prod.congr fun k => ?_
  rw [tsum_fintype, Fintype.sum_bool]
  rfl

end Series

end Qch

end HRS
