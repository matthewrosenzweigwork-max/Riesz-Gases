import HRS.MC.FDLE
import HRS.MC.Per

/-!
# Packet D3T1, auxiliary facts: periodization of `φ_t` and torus geometry (Lemma D.3 on `𝕋^d`).

Helpers only; names carry the prefix `d3t_`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HRS.MC.D3T1

open HRS HRS.MC.FDLE HRS.MC.Per

variable {d : ℕ}

/-- `P φ_t ≥ 0`. -/
lemma d3t_per_nonneg {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {t : ℝ} (ht : 0 < t) (x : Torus d) :
    0 ≤ fdlPer (fdlPhiScale ψ t) x :=
  tsum_nonneg fun _ => fdle_phiScale_nonneg hψ ht _

/-- The series defining `P φ_t` has finite support. -/
lemma d3t_summable {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {t : ℝ} (ht : 0 < t) (y : Euc d) :
    Summable fun n : Lattice d => fdlPhiScale ψ t (y + Lattice.toEuc n) := by
  apply summable_of_finite_support
  refine (per_finite_lattice (d := d) (t + ‖y‖)).subset ?_
  intro n hn
  exact per_term_ne_zero (R := t) (r := ‖y‖) (fun x hx => per_phiScale_zero hψ ht hx.le) le_rfl hn

/-- `φ_t(y) ≤ P φ_t (mk y)`. -/
lemma d3t_per_ge {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {t : ℝ} (ht : 0 < t) (y : Euc d) :
    fdlPhiScale ψ t y ≤ fdlPer (fdlPhiScale ψ t) (Torus.mk y) := by
  rw [per_fdlPer_mk]
  have h := (d3t_summable hψ ht y).le_tsum 0 (fun j _ => fdle_phiScale_nonneg hψ ht _)
  have h0 : Lattice.toEuc (0 : Lattice d) = 0 := by ext i; simp [Lattice.toEuc]
  simpa [h0] using h

lemma d3t_circ_norm_le (x : ℝ) : ‖(x : UnitAddCircle)‖ ≤ |x| := by
  rw [UnitAddCircle.norm_eq]
  have := round_le x 0
  simpa using this

/-- The torus distance is at most the norm of any representative. -/
lemma d3t_tdist_mk_le (w : Euc d) : KernelGrad.tdist (Torus.mk w) 0 ≤ ‖w‖ := by
  rw [show KernelGrad.tdist (Torus.mk w) 0 = Real.sqrt (∑ i, ‖(Torus.mk w) i‖ ^ 2) by
    have := CoercAux.tdist_eq_sqrt (Torus.mk w) 0
    simpa using this, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  have h0 : 0 ≤ ‖(Torus.mk w) i‖ := norm_nonneg _
  have : ‖(Torus.mk w) i‖ ≤ |w i| := d3t_circ_norm_le (w i)
  simp only [Real.norm_eq_abs, sq_abs]
  have h2 := pow_le_pow_left₀ h0 this 2
  rwa [sq_abs] at h2

lemma d3t_mk_add (y : Euc d) (n : Lattice d) : Torus.mk (y + Lattice.toEuc n) = Torus.mk y :=
  Torus.lift_periodic (E := Torus d) id y n

/-- `P φ_t (x) = 0` when `t ≤ |x|`. -/
lemma d3t_per_zero {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {t : ℝ} (ht : 0 < t) {x : Torus d}
    (h : t ≤ KernelGrad.tdist x 0) : fdlPer (fdlPhiScale ψ t) x = 0 := by
  unfold fdlPer
  refine (tsum_congr fun n => ?_).trans tsum_zero
  apply per_phiScale_zero hψ ht
  have := d3t_tdist_mk_le (Torus.rep x + Lattice.toEuc n)
  rw [d3t_mk_add, Torus.mk_rep] at this
  linarith

/-- A representative realising the torus distance. -/
lemma d3t_exists_rep (x : Torus d) : ∃ z : Euc d, Torus.mk z = x ∧ ‖z‖ = KernelGrad.tdist x 0 :=
  ⟨KernelGrad.centeredRep x, KernelGrad.mk_centeredRep x, (KernelGrad.tdist_zero_right x).symm⟩

/-- Lower bound by the nearest term. -/
lemma d3t_per_lower {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) (s : ℝ) {c0 : ℝ}
    (hc0 : ∀ y : Euc d, ‖y‖ ≤ 1 / 4 → c0 ≤ fdlPhi ψ y) {t : ℝ} (ht : 0 < t) {x : Torus d}
    {z : Euc d} (hz : Torus.mk z = x) (hzt : ‖t⁻¹ • z‖ ≤ 1 / 4) :
    c0 * (t ^ (-s) / t) ≤ t ^ ((d : ℝ) - s) * fdlPer (fdlPhiScale ψ t) x / t := by
  have h1 := fdle_F_lower s hc0 ht hzt
  have h2 := d3t_per_ge hψ ht z
  rw [hz] at h2
  refine h1.trans ?_
  have : t ^ ((d : ℝ) - s) * fdlPhiScale ψ t z / t ≤ t ^ ((d : ℝ) - s) * fdlPer (fdlPhiScale ψ t) x / t := by
    apply div_le_div_of_nonneg_right _ ht.le
    exact mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg ht.le _)
  exact this

/-- `x = 0` iff `tdist x 0 = 0`; in particular `lam ≤ tdist x 0`, `0 < lam` forces `x ≠ 0`. -/
lemma d3t_ne_zero_of_le {x : Torus d} {lam : ℝ} (hlam : 0 < lam) (h : lam ≤ KernelGrad.tdist x 0) :
    x ≠ 0 := by
  rintro rfl
  rw [CoercAux.tdist_self] at h
  linarith

end HRS.MC.D3T1
