import HRS.MC.S7PIDRGrad
import HRS.Uniform.Q54cAux34

/-!
# Packet PI-D, sub-packet E: real-mode gradient bookkeeping

Helpers `S7PIDE_*` (namespace `HRS.MC.Sec7.S7PIDE`).  Pure Fourier analysis on the torus.

* `S7PIDE_grad_series`: for `U ∈ H^n ∩ C^1`, `n > d/2 + 2`: `(∇U)_i(x) = ∑_k Û_k (∇e_k)_i(x)`
  (from `HRS.Uniform.Q54c.partialDeriv_series`).
* `S7PIDE_prod_hasSum`: if two gradients are expanded with absolutely summable `⟨k⟩`-weighted coefficients
  then `∇U·∇W(x) = ∑_{k,l} a_k b_l (∇e_k·∇e_l)(x)` (a double `HasSum`).
* `S7PIDE_coeff_hasSum`: the real Fourier coefficient `(∇U·∇W)^(j) = ∑_{k,l} a_k b_l (∇e_k·∇e_l)^(j)` (termwise integration).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIDE

open HRS HRS.Sec7 HRS.MC.Sec7.PID

variable {d : ℕ}

theorem S7PIDE_grad_apply (f : Torus d → ℝ) (x : Torus d) (j : Fin d) :
    Torus.grad f x j = Torus.partialDeriv j f x := by
  unfold Torus.grad Torus.partialDeriv
  have h1 := EuclideanSpace.inner_single_right j (1 : ℝ) (gradient (Torus.lift f) (Torus.rep x))
  have h2 := InnerProductSpace.toDual_symm_apply (x := EuclideanSpace.single j (1 : ℝ))
    (y := fderiv ℝ (Torus.lift f) (Torus.rep x))
  simp only [one_mul, RCLike.conj_to_real] at h1
  rw [← h1]
  exact h2

theorem S7PIDE_inner_eq (v w : Euc d) : inner ℝ v w = ∑ i, v i * w i := by
  simp [PiLp.inner_apply, mul_comm]

theorem S7PIDE_grad_comp_le (k : NonzeroLattice d) (x : Torus d) (i : Fin d) :
    |Torus.grad (Torus.realMode k) x i| ≤ Real.sqrt 2 * Lattice.jp k.1 := by
  rw [S7PIDE_grad_apply, ← HRS.Uniform.Q54c.Dmode_rep]
  exact HRS.Uniform.Q54c.abs_Dmode_le k i _

theorem S7PIDE_grad_series {n : ℝ} (hn : (d : ℝ) / 2 + 2 < n) {U : Torus d → ℝ}
    (hU : MemSobolev n U) (hc : Continuous U) (h1 : Torus.IsCk 1 U) (x : Torus d) (i : Fin d) :
    HasSum (fun k : NonzeroLattice d => Torus.funRealCoeff U k * Torus.grad (Torus.realMode k) x i)
      (Torus.grad U x i) := by
  simp_rw [S7PIDE_grad_apply]
  exact HRS.Uniform.Q54c.partialDeriv_series hn hU hc h1 i x

theorem S7PIDE_prod_hasSum (a b : NonzeroLattice d → ℝ) (U W : Torus d → ℝ)
    (ha : Summable fun k => |a k| * Lattice.jp k.1) (hb : Summable fun k => |b k| * Lattice.jp k.1)
    (hU : ∀ x i, HasSum (fun k => a k * Torus.grad (Torus.realMode k) x i) (Torus.grad U x i))
    (hW : ∀ x i, HasSum (fun k => b k * Torus.grad (Torus.realMode k) x i) (Torus.grad W x i))
    (x : Torus d) :
    HasSum (fun p : NonzeroLattice d × NonzeroLattice d => a p.1 * b p.2 * gradProd p.1 p.2 x)
      (inner ℝ (Torus.grad U x) (Torus.grad W x)) := by
  have hnorm : ∀ (c : NonzeroLattice d → ℝ), (Summable fun k => |c k| * Lattice.jp k.1) → ∀ i : Fin d,
      Summable (fun k => ‖c k * Torus.grad (Torus.realMode k) x i‖) := by
    intro c hc i
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) (hc.mul_left (Real.sqrt 2))
    rw [Real.norm_eq_abs, abs_mul]
    calc |c k| * |Torus.grad (Torus.realMode k) x i| ≤ |c k| * (Real.sqrt 2 * Lattice.jp k.1) :=
          mul_le_mul_of_nonneg_left (S7PIDE_grad_comp_le k x i) (abs_nonneg _)
      _ = Real.sqrt 2 * (|c k| * Lattice.jp k.1) := by ring
  have hterm : ∀ i : Fin d, HasSum (fun p : NonzeroLattice d × NonzeroLattice d =>
      (a p.1 * Torus.grad (Torus.realMode p.1) x i) * (b p.2 * Torus.grad (Torus.realMode p.2) x i))
      (Torus.grad U x i * Torus.grad W x i) := by
    intro i
    have hprod : Summable fun p : NonzeroLattice d × NonzeroLattice d =>
        (a p.1 * Torus.grad (Torus.realMode p.1) x i) * (b p.2 * Torus.grad (Torus.realMode p.2) x i) :=
      summable_mul_of_summable_norm
        (f := fun k => a k * Torus.grad (Torus.realMode k) x i)
        (g := fun k => b k * Torus.grad (Torus.realMode k) x i) (hnorm a ha i) (hnorm b hb i)
    exact HasSum.mul (f := fun k => a k * Torus.grad (Torus.realMode k) x i)
      (g := fun k => b k * Torus.grad (Torus.realMode k) x i) (hU x i) (hW x i) hprod
  have hsum : HasSum (fun p : NonzeroLattice d × NonzeroLattice d => ∑ i : Fin d,
      (a p.1 * Torus.grad (Torus.realMode p.1) x i) * (b p.2 * Torus.grad (Torus.realMode p.2) x i))
      (∑ i : Fin d, Torus.grad U x i * Torus.grad W x i) :=
    hasSum_sum (fun i _ => hterm i)
  have e2 : (fun p : NonzeroLattice d × NonzeroLattice d => a p.1 * b p.2 * gradProd p.1 p.2 x) =
      fun p => ∑ i : Fin d,
        (a p.1 * Torus.grad (Torus.realMode p.1) x i) * (b p.2 * Torus.grad (Torus.realMode p.2) x i) := by
    funext p
    unfold gradProd
    rw [S7PIDE_inner_eq, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [S7PIDE_inner_eq, e2]
  exact hsum

theorem S7PIDE_coeff_hasSum (a b : NonzeroLattice d → ℝ) (U W : Torus d → ℝ)
    (ha : Summable fun k => |a k| * Lattice.jp k.1) (hb : Summable fun k => |b k| * Lattice.jp k.1)
    (hU : ∀ x i, HasSum (fun k => a k * Torus.grad (Torus.realMode k) x i) (Torus.grad U x i))
    (hW : ∀ x i, HasSum (fun k => b k * Torus.grad (Torus.realMode k) x i) (Torus.grad W x i))
    (j : NonzeroLattice d) :
    HasSum (fun p : NonzeroLattice d × NonzeroLattice d =>
        a p.1 * b p.2 * Torus.funRealCoeff (gradProd p.1 p.2) j)
      (Torus.funRealCoeff (fun x => inner ℝ (Torus.grad U x) (Torus.grad W x)) j) := by
  set F : NonzeroLattice d × NonzeroLattice d → Torus d → ℝ :=
    fun p x => Torus.realMode j x * (a p.1 * b p.2 * gradProd p.1 p.2 x) with hF
  have hFc : ∀ p, Continuous (F p) := fun p =>
    (Torus.continuous_realMode j).mul (continuous_const.mul (S7PIDR.S7PIDR_gradProd_continuous p.1 p.2))
  have hFi : ∀ p, Integrable (F p) := fun p =>
    (hFc p).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  set B : NonzeroLattice d × NonzeroLattice d → ℝ :=
    fun p => Real.sqrt 2 * (2 * ((|a p.1| * Lattice.jp p.1.1) * (|b p.2| * Lattice.jp p.2.1))) with hB
  have hbd : ∀ p, ∫ x, ‖F p x‖ ≤ B p := by
    intro p
    have h := norm_integral_le_of_norm_le_const (μ := (volume : Measure (Torus d)))
      (f := fun x => ‖F p x‖) (C := B p) (Filter.Eventually.of_forall fun x => by
        rw [norm_norm, hF]
        simp only [Real.norm_eq_abs, abs_mul]
        have h1 := Torus.abs_realMode_le j x
        have h2 := S7PIDR.S7PIDR_gradProd_abs_le p.1 p.2 x
        have h3 : |a p.1| * |b p.2| * |gradProd p.1 p.2 x| ≤
            |a p.1| * |b p.2| * (2 * (Lattice.jp p.1.1 * Lattice.jp p.2.1)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
        have h4 : |Torus.realMode j x| * (|a p.1| * |b p.2| * |gradProd p.1 p.2 x|) ≤
            Real.sqrt 2 * (|a p.1| * |b p.2| * (2 * (Lattice.jp p.1.1 * Lattice.jp p.2.1))) :=
          mul_le_mul h1 h3 (by positivity) (by positivity)
        calc |Torus.realMode j x| * (|a p.1| * |b p.2| * |gradProd p.1 p.2 x|)
            ≤ Real.sqrt 2 * (|a p.1| * |b p.2| * (2 * (Lattice.jp p.1.1 * Lattice.jp p.2.1))) := h4
          _ = B p := by simp only [hB]; ring)
    simp only [probReal_univ, mul_one] at h
    exact (le_abs_self _).trans (by simpa using h)
  have hBsum : Summable B := by
    have hp : Summable (fun p : NonzeroLattice d × NonzeroLattice d =>
        (|a p.1| * Lattice.jp p.1.1) * (|b p.2| * Lattice.jp p.2.1)) :=
      Summable.mul_of_nonneg ha hb (fun k => mul_nonneg (abs_nonneg _) (Torus.jp_pos k.1).le)
        (fun k => mul_nonneg (abs_nonneg _) (Torus.jp_pos k.1).le)
    exact (hp.mul_left 2).mul_left (Real.sqrt 2)
  have hsum : Summable fun p => ∫ x, ‖F p x‖ :=
    Summable.of_nonneg_of_le (fun p => integral_nonneg fun x => norm_nonneg _) hbd hBsum
  have h := hasSum_integral_of_summable_integral_norm hFi hsum
  have e1 : ∀ x, ∑' p, F p x = Torus.realMode j x * inner ℝ (Torus.grad U x) (Torus.grad W x) := fun x =>
    ((S7PIDE_prod_hasSum a b U W ha hb hU hW x).mul_left (Torus.realMode j x)).tsum_eq
  simp_rw [e1] at h
  have e2 : ∀ p, ∫ x, F p x = a p.1 * b p.2 * Torus.funRealCoeff (gradProd p.1 p.2) j := by
    intro p
    have : ∀ x, F p x = (a p.1 * b p.2) * (Torus.realMode j x * gradProd p.1 p.2 x) := fun x => by
      simp only [hF]; ring
    simp_rw [this]
    rw [integral_const_mul]
    rfl
  simp_rw [e2] at h
  exact h

end HRS.MC.Sec7.S7PIDE

end
