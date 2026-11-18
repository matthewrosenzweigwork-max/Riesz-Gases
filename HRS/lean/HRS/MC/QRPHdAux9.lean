import HRS.MC.QRPHdAux5
import HRS.MC.QRPHdAux6

/-!
# Packet HD, part 9: pointwise bound `A_{ab}² ≤ 8 ∑_{σ,ε,τ} 1[b = φ(a)] w(a)` for the Wick coefficients
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped BigOperators ComplexConjugate

namespace HRS.MC.QRSpec.Hd

open HRS

variable {d : ℕ} {s : ℝ}

theorem hdsg_mul_self (b : Bool) : hdsg b * hdsg b = 1 := by cases b <;> simp [hdsg]

theorem hdsg_smul_smul (b : Bool) (x : Lattice d) : hdsg b • hdsg b • x = x := by
  cases b <;> simp [hdsg]

/-- The partner `b = φ(a)` of `a` in the band `σa + εκ + τb = 0`. -/
def hdφ (κ : Lattice d) (σ ε τ : Bool) (c : Lattice d) : Lattice d :=
  -(hdsg τ • (hdsg σ • c + hdsg ε • κ))

/-- The weight of the band term. -/
def hdw (d : ℕ) (s : ℝ) (κ : Lattice d) (σ ε : Bool) (c : Lattice d) : ℝ :=
  (4 * Real.pi ^ 2 * Lattice.enorm κ) ^ 2 * hdD d s (hdsg ε • κ) (hdsg σ • c) ^ 2

theorem hd_cond_iff (σ ε τ : Bool) (a κ b : Lattice d) :
    hdsg σ • a + hdsg ε • κ + hdsg τ • b = 0 ↔ b = hdφ κ σ ε τ a := by
  unfold hdφ
  constructor
  · intro h
    have h1 : hdsg τ • b = -(hdsg σ • a + hdsg ε • κ) := eq_neg_of_add_eq_zero_right h
    calc b = hdsg τ • hdsg τ • b := (hdsg_smul_smul τ b).symm
      _ = _ := by rw [h1, smul_neg]
  · intro h
    rw [h, smul_neg, hdsg_smul_smul]
    abel

theorem hd_enorm_smul_sg (b : Bool) (x : Lattice d) : Lattice.enorm (hdsg b • x) = Lattice.enorm x := by
  cases b
  · simp only [hdsg, Bool.false_eq_true, ite_false, neg_smul, one_smul]
    exact hd_enorm_neg x
  · simp [hdsg]

theorem hd_cf_norm_le (a : Lattice d) (b : Bool) : ‖hdcf a b‖ ≤ 1 := by
  have h2 : Real.sqrt 2 / 2 ≤ 1 := by
    have : Real.sqrt 2 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    linarith
  have h0 : 0 ≤ Real.sqrt 2 / 2 := by positivity
  have hr : ‖Torus.realCoef a‖ ≤ 1 := by
    by_cases hp : Lattice.IsPosHalf a
    · rw [Torus.realCoef_pos hp, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]; exact h2
    · rw [Torus.realCoef_neg hp, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg h0]; exact h2
  cases b
  · simp only [hdcf, Bool.false_eq_true, ite_false, Complex.norm_conj]; exact hr
  · simp only [hdcf, ite_true]; exact hr

theorem hdq_comp (s : ℝ) (c : Lattice d) (i : Fin d) :
    (hdq d s c) i = rieszCoeff d s c * (c i : ℝ) := by
  simp [hdq, Lattice.toEuc]

theorem hdK_norm_le (lam β : Lattice d) :
    ‖hdK d s lam β‖ ≤ 4 * Real.pi ^ 2 * Lattice.enorm lam * ‖hdq d s β - hdq d s (lam + β)‖ := by
  have e : hdK d s lam β = ((-(4 * Real.pi ^ 2) *
      inner ℝ (Lattice.toEuc lam) (hdq d s β - hdq d s (lam + β)) : ℝ) : ℂ) := by
    unfold hdK
    simp only [PiLp.inner_apply, PiLp.sub_apply, hdq_comp, RCLike.inner_apply, conj_trivial]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Lattice.toEuc, Pi.add_apply]
    push_cast
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    linear_combination (↑(lam i) * ↑(rieszCoeff d s β) * ↑(β i) * 4 * ↑Real.pi ^ 2 -
      ↑(lam i) * ↑(rieszCoeff d s (lam + β)) * (↑(lam i) + ↑(β i)) * 4 * ↑Real.pi ^ 2) * hI
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_neg,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * Real.pi ^ 2)]
  have := abs_real_inner_le_norm (Lattice.toEuc lam) (hdq d s β - hdq d s (lam + β))
  have h2 : ‖Lattice.toEuc lam‖ = Lattice.enorm lam := rfl
  rw [h2] at this
  calc 4 * Real.pi ^ 2 * |inner ℝ (Lattice.toEuc lam) (hdq d s β - hdq d s (lam + β))|
      ≤ 4 * Real.pi ^ 2 * (Lattice.enorm lam * ‖hdq d s β - hdq d s (lam + β)‖) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by ring

theorem hdK_norm_le' (α lam β : Lattice d) (h : α + lam + β = 0) :
    ‖hdK d s lam β‖ ≤ 4 * Real.pi ^ 2 * Lattice.enorm lam * hdD d s lam α := by
  refine (hdK_norm_le lam β).trans ?_
  have hβ : β = -(α + lam) := eq_neg_of_add_eq_zero_right h
  have h2 : lam + β = -α := by rw [hβ]; abel
  rw [h2, hβ, hdq_neg, hdq_neg]
  unfold hdD
  have : -hdq d s (α + lam) - -hdq d s α = hdq d s α - hdq d s (α + lam) := by abel
  rw [this]

end HRS.MC.QRSpec.Hd

end
