import HRS.PDE.ForwardEq
import HRS.PDE.Toolbox.Quadratic

/-!
# Appendix C helper lemmas: the symbol of K_q and the real-basis form (Lemma C.3 setup)

Auxiliary results for `HRS/PDE/Toolbox.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.SymAux

variable {d : ℕ}

/-! ### The symbol of `K_q` is a homogeneous symbol -/

/-- The homogeneous extension of `symbolK d s q` to `ℝ^d`. -/
def symExt (d : ℕ) (s : ℝ) (q : Euc d) (ξ : Euc d) : ℝ :=
  (2 * Real.pi * inner ℝ q ξ) ^ 2 * (rieszConst d s * (2 * Real.pi * ‖ξ‖) ^ (s - (d : ℝ)))

theorem symExt_contDiffOn (d : ℕ) (s : ℝ) (q : Euc d) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (symExt d s q) {ξ | ξ ≠ 0} := by
  intro ξ hξ
  have hξ' : ξ ≠ 0 := hξ
  apply ContDiffAt.contDiffWithinAt
  unfold symExt
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ξ : Euc d => (2 * Real.pi * inner ℝ q ξ) ^ 2) ξ := by
    refine ContDiffAt.pow ?_ 2
    exact contDiffAt_const.mul (contDiffAt_const.inner ℝ contDiffAt_id)
  have hn : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ξ : Euc d => 2 * Real.pi * ‖ξ‖) ξ :=
    contDiffAt_const.mul (contDiffAt_norm ℝ hξ')
  have hpos : 2 * Real.pi * ‖ξ‖ ≠ 0 := by
    have := norm_pos_iff.mpr hξ'
    positivity
  have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun ξ : Euc d => (2 * Real.pi * ‖ξ‖) ^ (s - (d : ℝ))) ξ :=
    ContDiffAt.comp (g := fun x : ℝ => x ^ (s - (d : ℝ))) ξ
      (Real.contDiffAt_rpow_const_of_ne hpos) hn
  exact h1.mul (contDiffAt_const.mul h2)

theorem symExt_neg (d : ℕ) (s : ℝ) (q : Euc d) (ξ : Euc d) :
    symExt d s q (-ξ) = symExt d s q ξ := by
  simp [symExt, inner_neg_right]

/-- `c_{d,s} > 0` for `d ≥ 1` and `0 ≤ s < d` (the proof of `rieszConst_pos` only uses `0 < d`). -/
theorem rieszConst_pos' {d : ℕ} (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    0 < rieszConst d s := by
  have hd' : (0:ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  unfold rieszConst
  split_ifs with h
  · exact mul_pos (mul_pos (by positivity) (by positivity)) (Real.Gamma_pos_of_pos (by positivity))
  · have hs : 0 < s := lt_of_le_of_ne hs0 (Ne.symm h)
    exact div_pos (mul_pos (mul_pos (by positivity) (by positivity))
      (Real.Gamma_pos_of_pos (by linarith))) (Real.Gamma_pos_of_pos (by linarith))

theorem symExt_nonneg {d : ℕ} (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (q : Euc d) (ξ : Euc d) : 0 ≤ symExt d s q ξ := by
  have := rieszConst_pos' hd hs0 hsd
  unfold symExt
  positivity

theorem symExt_smul (d : ℕ) (s : ℝ) (q : Euc d) (c : ℝ) (hc : 0 < c) (ξ : Euc d) :
    symExt d s q (c • ξ) = c ^ (s + 2 - d) * symExt d s q ξ := by
  unfold symExt
  rw [inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  have hπ : 0 < Real.pi := Real.pi_pos
  have e1 : 2 * Real.pi * (c * ‖ξ‖) = c * (2 * Real.pi * ‖ξ‖) := by ring
  have hn : 0 ≤ 2 * Real.pi * ‖ξ‖ := by positivity
  rw [e1, Real.mul_rpow hc.le hn]
  have e2 : c ^ (s + 2 - (d : ℝ)) = c ^ (2 : ℕ) * c ^ (s - (d : ℝ)) := by
    rw [show s + 2 - (d : ℝ) = ((2 : ℕ) : ℝ) + (s - d) by push_cast; ring, Real.rpow_add hc,
      Real.rpow_natCast]
  rw [e2]
  ring

theorem symExt_eq (d : ℕ) (s : ℝ) (q : Euc d) (k : Lattice d) (hk : k ≠ 0) :
    symbolK d s q k = symExt d s q (Lattice.toEuc k) := by
  unfold symbolK symExt rieszCoeff Lattice.enorm
  simp [hk]

theorem symbolK_zero (d : ℕ) (s : ℝ) (q : Euc d) : symbolK d s q 0 = 0 := by
  simp [symbolK, rieszCoeff]

/-! ### The complex coefficient form is the real-basis form -/

theorem re_fcoef_mul_conj {u v : Torus d → ℝ} (hu : Integrable u) (hv : Integrable v)
    (k : Lattice d) :
    (Torus.fcoef u k * conj (Torus.fcoef v k)).re =
      Torus.cosCoeff u k * Torus.cosCoeff v k + Torus.sinCoeff u k * Torus.sinCoeff v k := by
  have hcu : Torus.fcoef u k = ((Torus.cosCoeff u k : ℝ) : ℂ) + ((-Torus.sinCoeff u k : ℝ) : ℂ) * Complex.I :=
    Torus.integral_mode_mul_real hu k
  have hcv : Torus.fcoef v k = ((Torus.cosCoeff v k : ℝ) : ℂ) + ((-Torus.sinCoeff v k : ℝ) : ℂ) * Complex.I :=
    Torus.integral_mode_mul_real hv k
  rw [hcu, hcv]
  simp [Complex.mul_re, Complex.mul_im]

theorem pair_polar {u v : Torus d → ℝ} (hu : Integrable u) (hv : Integrable v)
    (k : NonzeroLattice d) :
    Torus.funRealCoeff u k * Torus.funRealCoeff v k +
      Torus.funRealCoeff u (Torus.negNZ d k) * Torus.funRealCoeff v (Torus.negNZ d k) =
      2 * (Torus.fcoef u k.1 * conj (Torus.fcoef v k.1)).re := by
  rw [re_fcoef_mul_conj hu hv]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hneg := Torus.isPosHalf_neg k.1 k.2
  have e1 : (Torus.negNZ d k).1 = -k.1 := rfl
  rw [Torus.funRealCoeff_eq, Torus.funRealCoeff_eq, Torus.funRealCoeff_eq, Torus.funRealCoeff_eq, e1]
  by_cases hp : Lattice.IsPosHalf k.1
  · have hq : ¬ Lattice.IsPosHalf (-k.1) := fun h => (hneg.mp h) hp
    simp only [hp, hq, ite_true, ite_false, Torus.sinCoeff_neg]
    linear_combination (Torus.cosCoeff u k.1 * Torus.cosCoeff v k.1 +
      Torus.sinCoeff u k.1 * Torus.sinCoeff v k.1) * h2
  · have hq : Lattice.IsPosHalf (-k.1) := hneg.mpr hp
    simp only [hp, hq, ite_true, ite_false, Torus.cosCoeff_neg]
    linear_combination (Torus.cosCoeff u k.1 * Torus.cosCoeff v k.1 +
      Torus.sinCoeff u k.1 * Torus.sinCoeff v k.1) * h2

theorem form_eq_multiplier (𝔪 : Lattice d → ℝ) (h0 : 𝔪 0 = 0)
    (heven : ∀ k, 𝔪 (-k) = 𝔪 k) {u v : Torus d → ℝ} (hu : Integrable u) (hv : Integrable v)
    (hfu : Summable fun k => 𝔪 k * ‖Torus.fcoef u k‖ ^ 2)
    (hfv : Summable fun k => 𝔪 k * ‖Torus.fcoef v k‖ ^ 2) :
    (∑' k, ((𝔪 k : ℝ) : ℂ) * (Torus.fcoef u k * conj (Torus.fcoef v k))).re =
      ∑' k : NonzeroLattice d, 𝔪 k.1 * Torus.funRealCoeff u k * Torus.funRealCoeff v k := by
  set f : Lattice d → ℂ := fun k => ((𝔪 k : ℝ) : ℂ) * (Torus.fcoef u k * conj (Torus.fcoef v k)) with hf
  -- summability of the complex series
  have hsf : Summable f := by
    refine Summable.of_norm_bounded ((hfu.abs.add hfv.abs).mul_left (1 / 2)) (fun k => ?_)
    simp only [hf, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_pow, abs_norm]
    nlinarith [abs_nonneg (𝔪 k), norm_nonneg (Torus.fcoef u k), norm_nonneg (Torus.fcoef v k),
      mul_nonneg (abs_nonneg (𝔪 k)) (sq_nonneg (‖Torus.fcoef u k‖ - ‖Torus.fcoef v k‖))]
  rw [Complex.re_tsum hsf]
  have hsr : Summable fun k => (f k).re := (Complex.hasSum_re hsf.hasSum).summable
  rw [Torus.tsum_lattice _ hsr]
  have hf0 : (f 0).re = 0 := by simp [hf, h0]
  rw [hf0, zero_add]
  -- reduce to the nonzero lattice
  set T : NonzeroLattice d → ℝ := fun k =>
    𝔪 k.1 * Torus.funRealCoeff u k * Torus.funRealCoeff v k with hT
  have hsrN : Summable fun k : NonzeroLattice d => (f k.1).re := (Torus.summable_lattice_iff _).mp hsr
  have hpair : ∀ k : NonzeroLattice d, T k + T (Torus.negNZ d k) = 2 * (f k.1).re := by
    intro k
    have := pair_polar hu hv k
    have he : 𝔪 (Torus.negNZ d k).1 = 𝔪 k.1 := heven k.1
    simp only [hT, he]
    have hre : (f k.1).re = 𝔪 k.1 * (Torus.fcoef u k.1 * conj (Torus.fcoef v k.1)).re := by
      simp only [hf]
      rw [Complex.re_ofReal_mul]
    rw [hre]
    linear_combination 𝔪 k.1 * this
  have hTsum : Summable T := by
    have hS := ((Torus.summable_lattice_iff _).mp (hfu.abs.add hfv.abs))
    refine Summable.of_norm_bounded hS (fun k => ?_)
    have hu2 := Torus.two_mul_norm_fcoef_sq hu k
    have hv2 := Torus.two_mul_norm_fcoef_sq hv k
    set A := Torus.funRealCoeff u k
    set B := Torus.funRealCoeff v k
    set A' := Torus.funRealCoeff u (Torus.negNZ d k)
    set B' := Torus.funRealCoeff v (Torus.negNZ d k)
    simp only [hT, Real.norm_eq_abs, abs_mul, abs_norm, abs_pow]
    have hm := abs_nonneg (𝔪 k.1)
    have habs : |𝔪 k.1| * |A| * |B| ≤ |𝔪 k.1| * (‖Torus.fcoef u k.1‖ ^ 2 + ‖Torus.fcoef v k.1‖ ^ 2) := by
      have h1 : |A| * |B| ≤ (A ^ 2 + B ^ 2) / 2 := by
        nlinarith [sq_nonneg (|A| - |B|), sq_abs A, sq_abs B]
      have h2 : (A ^ 2 + B ^ 2) / 2 ≤ ‖Torus.fcoef u k.1‖ ^ 2 + ‖Torus.fcoef v k.1‖ ^ 2 := by
        nlinarith [sq_nonneg A', sq_nonneg B']
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (h1.trans h2) hm
    nlinarith [habs]
  have hTneg : Summable fun k => T (Torus.negNZ d k) := (Torus.negNZ d).summable_iff.mpr hTsum
  have h2 : ∑' k, (T k + T (Torus.negNZ d k)) = 2 * ∑' k : NonzeroLattice d, (f k.1).re := by
    simp_rw [hpair]
    rw [tsum_mul_left]
  rw [hTsum.tsum_add hTneg, Equiv.tsum_eq (Torus.negNZ d) T] at h2
  show _ = ∑' k, T k
  linarith

end HRS.PDE.SymAux
