import HRS.MC.S7PIDDefs

/-!
# Packet PI-D, `s7_PID_gradprod`: gradients of the real modes and the pointwise form of `∇e_k·∇e_l`

Helpers `S7PIDR_*` (namespace `HRS.MC.Sec7.S7PIDR`).  Pure Fourier analysis on the torus, no dynamics.

Route: `∇ realMode k (x) = (2π√2 σ_k(x)) • k` where `σ_k = -sin(2π k·x)` on the positive half-lattice and
`σ_k = cos(2π k·x)` on the negative half, hence `∇e_k·∇e_l = 8π² (k·l) σ_k σ_l`, which is bounded by
`2⟨k⟩⟨l⟩` (from `2π|k| ≤ ⟨k⟩`, `Lattice.jp`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIDR

open HRS HRS.Sec7 HRS.MC.Sec7.PID

variable {d : ℕ}

theorem S7PIDR_toEuc_add (a b : Lattice d) :
    Lattice.toEuc (a + b) = Lattice.toEuc a + Lattice.toEuc b := by
  ext i
  simp [Lattice.toEuc]

theorem S7PIDR_toEuc_neg (a : Lattice d) : Lattice.toEuc (-a) = -Lattice.toEuc a := by
  ext i
  simp [Lattice.toEuc]

theorem S7PIDR_dot_eq (a : Lattice d) (y : Euc d) :
    Lattice.dot a y = inner ℝ (Lattice.toEuc a) y := by
  simp [PiLp.inner_apply, Lattice.dot, Lattice.toEuc, mul_comm]

theorem S7PIDR_enorm_nonneg (a : Lattice d) : 0 ≤ Lattice.enorm a := norm_nonneg _

theorem S7PIDR_enorm_neg (a : Lattice d) : Lattice.enorm (-a) = Lattice.enorm a := by
  unfold Lattice.enorm
  rw [S7PIDR_toEuc_neg, norm_neg]

theorem S7PIDR_jp_neg (a : Lattice d) : Lattice.jp (-a) = Lattice.jp a := by
  unfold Lattice.jp
  rw [S7PIDR_enorm_neg]

theorem S7PIDR_jp_sq (a : Lattice d) :
    Lattice.jp a ^ 2 = 1 + 4 * Real.pi ^ 2 * Lattice.enorm a ^ 2 := by
  unfold Lattice.jp
  rw [Real.sq_sqrt (by positivity)]

theorem S7PIDR_two_pi_enorm_le (a : Lattice d) :
    2 * Real.pi * Lattice.enorm a ≤ Lattice.jp a := by
  have hE := S7PIDR_enorm_nonneg a
  calc 2 * Real.pi * Lattice.enorm a = Real.sqrt ((2 * Real.pi * Lattice.enorm a) ^ 2) :=
        (Real.sqrt_sq (by positivity)).symm
    _ ≤ Real.sqrt (1 + 4 * Real.pi ^ 2 * Lattice.enorm a ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith)
    _ = Lattice.jp a := rfl

theorem S7PIDR_enorm_add_sq (a b : Lattice d) :
    Lattice.enorm (a + b) ^ 2 ≤ 2 * Lattice.enorm a ^ 2 + 2 * Lattice.enorm b ^ 2 := by
  unfold Lattice.enorm
  rw [S7PIDR_toEuc_add, norm_add_pow_two_real]
  have h := abs_le.mp (abs_real_inner_le_norm (Lattice.toEuc a) (Lattice.toEuc b))
  nlinarith [sq_nonneg (‖Lattice.toEuc a‖ - ‖Lattice.toEuc b‖), h.1, h.2]

/-- `⟨a+b⟩² ≤ 2⟨a⟩²⟨b⟩²`: the frequencies `±k ± l` of the gradient product are `√2`-controlled. -/
theorem S7PIDR_jp_add_sq_le (a b : Lattice d) :
    Lattice.jp (a + b) ^ 2 ≤ 2 * (Lattice.jp a * Lattice.jp b) ^ 2 := by
  rw [mul_pow, S7PIDR_jp_sq, S7PIDR_jp_sq, S7PIDR_jp_sq]
  have h := S7PIDR_enorm_add_sq a b
  have hp : 0 ≤ 4 * Real.pi ^ 2 := by positivity
  have hq : 0 ≤ Real.pi ^ 4 * Lattice.enorm a ^ 2 * Lattice.enorm b ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h hp]

theorem S7PIDR_hasGrad_cos (A c : ℝ) (a z : Euc d) :
    HasGradientAt (fun y : Euc d => A * Real.cos (c * inner ℝ a y))
      ((-(A * c * Real.sin (c * inner ℝ a z))) • a) z := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h1 : HasFDerivAt (fun y : Euc d => inner ℝ a y) (innerSL ℝ a) z :=
    (innerSL ℝ a).hasFDerivAt
  have h2 := ((h1.const_mul c).cos).const_mul A
  convert h2 using 1
  ext y
  simp [InnerProductSpace.toDual_apply_apply, real_inner_smul_left]
  ring

theorem S7PIDR_hasGrad_sin (A c : ℝ) (a z : Euc d) :
    HasGradientAt (fun y : Euc d => A * Real.sin (c * inner ℝ a y))
      ((A * c * Real.cos (c * inner ℝ a z)) • a) z := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h1 : HasFDerivAt (fun y : Euc d => inner ℝ a y) (innerSL ℝ a) z :=
    (innerSL ℝ a).hasFDerivAt
  have h2 := ((h1.const_mul c).sin).const_mul A
  convert h2 using 1
  ext y
  simp [InnerProductSpace.toDual_apply_apply, real_inner_smul_left]
  ring

open Classical in
/-- The trigonometric factor of `∇ realMode k`: `-sin(2π k·x)` on the positive half-lattice,
`cos(2π k·x)` on the negative one. -/
def S7PIDR_sig (k : NonzeroLattice d) (x : Torus d) : ℝ :=
  if Lattice.IsPosHalf k.1 then -Torus.sinMode k.1 x else Torus.cosMode k.1 x

theorem S7PIDR_grad_realMode (k : NonzeroLattice d) (x : Torus d) :
    Torus.grad (Torus.realMode k) x =
      (2 * Real.pi * Real.sqrt 2 * S7PIDR_sig k x) • Lattice.toEuc k.1 := by
  unfold Torus.grad
  by_cases hp : Lattice.IsPosHalf k.1
  · have hlift : Torus.lift (Torus.realMode k) =
        fun y : Euc d => Real.sqrt 2 * Real.cos (2 * Real.pi * inner ℝ (Lattice.toEuc k.1) y) := by
      funext y
      show Torus.realMode k (Torus.mk y) = _
      unfold Torus.realMode
      rw [if_pos hp, Torus.cosMode_mk, S7PIDR_dot_eq]
    have hG := S7PIDR_hasGrad_cos (Real.sqrt 2) (2 * Real.pi) (Lattice.toEuc k.1) (Torus.rep x)
    have hs : Torus.sinMode k.1 x =
        Real.sin (2 * Real.pi * inner ℝ (Lattice.toEuc k.1) (Torus.rep x)) := by
      have h := Torus.sinMode_mk k.1 (Torus.rep x)
      rw [Torus.mk_rep, S7PIDR_dot_eq] at h
      exact h
    rw [hlift, hG.gradient]
    unfold S7PIDR_sig
    rw [if_pos hp, hs]
    congr 1
    ring
  · have hlift : Torus.lift (Torus.realMode k) =
        fun y : Euc d => Real.sqrt 2 * Real.sin (2 * Real.pi * inner ℝ (Lattice.toEuc k.1) y) := by
      funext y
      show Torus.realMode k (Torus.mk y) = _
      unfold Torus.realMode
      rw [if_neg hp, Torus.sinMode_mk, S7PIDR_dot_eq]
    have hG := S7PIDR_hasGrad_sin (Real.sqrt 2) (2 * Real.pi) (Lattice.toEuc k.1) (Torus.rep x)
    have hc : Torus.cosMode k.1 x =
        Real.cos (2 * Real.pi * inner ℝ (Lattice.toEuc k.1) (Torus.rep x)) := by
      have h := Torus.cosMode_mk k.1 (Torus.rep x)
      rw [Torus.mk_rep, S7PIDR_dot_eq] at h
      exact h
    rw [hlift, hG.gradient]
    unfold S7PIDR_sig
    rw [if_neg hp, hc]
    congr 1
    ring

theorem S7PIDR_gradProd_eq (k l : NonzeroLattice d) (x : Torus d) :
    gradProd k l x = 8 * Real.pi ^ 2 * inner ℝ (Lattice.toEuc k.1) (Lattice.toEuc l.1) *
      (S7PIDR_sig k x * S7PIDR_sig l x) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp only [gradProd]
  rw [S7PIDR_grad_realMode, S7PIDR_grad_realMode, real_inner_smul_left, real_inner_smul_right]
  linear_combination (4 * Real.pi ^ 2 * (S7PIDR_sig k x * S7PIDR_sig l x) *
    inner ℝ (Lattice.toEuc k.1) (Lattice.toEuc l.1)) * h2

theorem S7PIDR_sig_continuous (k : NonzeroLattice d) : Continuous (S7PIDR_sig k) := by
  by_cases hp : Lattice.IsPosHalf k.1
  · have h : S7PIDR_sig k = fun x => -Torus.sinMode k.1 x :=
      funext fun x => by simp [S7PIDR_sig, hp]
    rw [h]
    exact (Torus.continuous_sinMode k.1).neg
  · have h : S7PIDR_sig k = fun x => Torus.cosMode k.1 x :=
      funext fun x => by simp [S7PIDR_sig, hp]
    rw [h]
    exact Torus.continuous_cosMode k.1

theorem S7PIDR_gradProd_continuous (k l : NonzeroLattice d) : Continuous (gradProd k l) := by
  have h : gradProd k l = fun x => 8 * Real.pi ^ 2 * inner ℝ (Lattice.toEuc k.1) (Lattice.toEuc l.1) *
      (S7PIDR_sig k x * S7PIDR_sig l x) := funext (S7PIDR_gradProd_eq k l)
  rw [h]
  exact continuous_const.mul ((S7PIDR_sig_continuous k).mul (S7PIDR_sig_continuous l))

theorem S7PIDR_sig_abs_le (k : NonzeroLattice d) (x : Torus d) : |S7PIDR_sig k x| ≤ 1 := by
  unfold S7PIDR_sig
  split_ifs
  · rw [abs_neg, ← Real.norm_eq_abs]
    exact Torus.norm_sinMode_le k.1 x
  · rw [← Real.norm_eq_abs]
    exact Torus.norm_cosMode_le k.1 x

/-- Pointwise bound `|∇e_k·∇e_l| ≤ 2⟨k⟩⟨l⟩`. -/
theorem S7PIDR_gradProd_abs_le (k l : NonzeroLattice d) (x : Torus d) :
    |gradProd k l x| ≤ 2 * (Lattice.jp k.1 * Lattice.jp l.1) := by
  rw [S7PIDR_gradProd_eq, abs_mul, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 8 * Real.pi ^ 2), abs_mul]
  have hK : |inner ℝ (Lattice.toEuc k.1) (Lattice.toEuc l.1)| ≤
      Lattice.enorm k.1 * Lattice.enorm l.1 := abs_real_inner_le_norm _ _
  have hk := S7PIDR_two_pi_enorm_le k.1
  have hl := S7PIDR_two_pi_enorm_le l.1
  have hEk := S7PIDR_enorm_nonneg k.1
  have hEl := S7PIDR_enorm_nonneg l.1
  have hjk : 0 ≤ Lattice.jp k.1 := (Torus.jp_pos k.1).le
  have hjl : 0 ≤ Lattice.jp l.1 := (Torus.jp_pos l.1).le
  have hsig : |S7PIDR_sig k x| * |S7PIDR_sig l x| ≤ 1 := by
    have h1 := S7PIDR_sig_abs_le k x
    have h2 := S7PIDR_sig_abs_le l x
    nlinarith [abs_nonneg (S7PIDR_sig k x), abs_nonneg (S7PIDR_sig l x)]
  have hprod : (2 * Real.pi * Lattice.enorm k.1) * (2 * Real.pi * Lattice.enorm l.1) ≤
      Lattice.jp k.1 * Lattice.jp l.1 :=
    mul_le_mul hk hl (by positivity) hjk
  have hA : 0 ≤ 8 * Real.pi ^ 2 * |inner ℝ (Lattice.toEuc k.1) (Lattice.toEuc l.1)| := by positivity
  have step1 := mul_le_of_le_one_right hA hsig
  have step2 : 8 * Real.pi ^ 2 * |inner ℝ (Lattice.toEuc k.1) (Lattice.toEuc l.1)| ≤
      8 * Real.pi ^ 2 * (Lattice.enorm k.1 * Lattice.enorm l.1) :=
    mul_le_mul_of_nonneg_left hK (by positivity)
  nlinarith [step1, step2, hprod]

end HRS.MC.Sec7.S7PIDR

end
