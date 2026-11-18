import HRS.MC.S7PIS1Eval
import HRS.MC.S7PIS3Cov1

/-!
# Packet piB, part 2: pointwise derivatives of the propagated modes as an `E_m` functional

For `y ∈ 𝕋^d`, `a < d` let `b_{y,a} ∈ E_m` be the element with real Fourier coefficients `∂_a e_k(y)` (`m` large).
Then for smooth `φ` and `0 ≤ u ≤ t ≤ T` the series `∂_a (U^{u,t}φ)(y) = ∑_j (U^{u,t}φ)^_j ∂_a e_j(y)`
holds (termwise differentiation of the real Fourier series), i.e. `eval b_{y,a} (U^{u,t}φ) = ∂_a (U^{u,t}φ)(y)`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIB

open HRS HRS.PDE HRS.A33 HRS.Sec7 HRS.MC.Sec7.PIE HRS.MC.Sec7.S7PIDV HRS.MC.Sec7.S7PIS1

variable {d : ℕ}

/-- `∂_a e_k (y)` -/
def S7PIB_dmode (a : Fin d) (k : NonzeroLattice d) (y : Torus d) : ℝ :=
  Torus.partialDeriv a (Torus.realMode k) y

theorem S7PIB_cd1 (k : NonzeroLattice d) : ContDiff ℝ 1 (Torus.lift (Torus.realMode k)) := by
  have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift (Torus.realMode k)) :=
    HRS.FieldSingAux.isSmooth_realMode k
  exact h.of_le (by exact_mod_cast le_top)

theorem S7PIB_norm_fderiv_mode_le (k : NonzeroLattice d) (z : Euc d) :
    ‖fderiv ℝ (Torus.lift (Torus.realMode k)) z‖ ≤ 2 * Real.sqrt 2 * Lattice.jp k.1 := by
  have hs : ContDiff ℝ 1 (Torus.lift (Torus.realMode k)) := S7PIB_cd1 k
  have hb := Torus.bddAbove_norm_iteratedFDeriv_lift 1 (Torus.realMode k) hs
  have h1 : ‖iteratedFDeriv ℝ 1 (Torus.lift (Torus.realMode k)) z‖ ≤
      ⨆ x : Euc d, ‖iteratedFDeriv ℝ 1 (Torus.lift (Torus.realMode k)) x‖ := le_ciSup hb z
  have hcb := Torus.cbNorm_realMode_le_aux 1 k
  have h0 : 0 ≤ ⨆ x : Euc d, ‖iteratedFDeriv ℝ 0 (Torus.lift (Torus.realMode k)) x‖ :=
    Real.iSup_nonneg fun _ => norm_nonneg _
  unfold Torus.cbNorm at hcb
  rw [Finset.sum_range_succ, Finset.sum_range_one] at hcb
  rw [norm_iteratedFDeriv_one] at h1
  have : ((1 : ℕ) + 1 : ℝ) * Real.sqrt 2 * Lattice.jp k.1 ^ 1 = 2 * Real.sqrt 2 * Lattice.jp k.1 := by
    push_cast; ring
  rw [this] at hcb
  have hsup1 : (⨆ x : Euc d, ‖iteratedFDeriv ℝ 1 (Torus.lift (Torus.realMode k)) x‖) ≤
      2 * Real.sqrt 2 * Lattice.jp k.1 := by
    have : ((1 : ℕ) + 1 : ℝ) * Real.sqrt 2 * Lattice.jp k.1 ^ 1 = 2 * Real.sqrt 2 * Lattice.jp k.1 := by
      push_cast; ring
    linarith
  exact h1.trans hsup1

theorem S7PIB_dmode_le (a : Fin d) (k : NonzeroLattice d) (y : Torus d) :
    |S7PIB_dmode a k y| ≤ 2 * Real.sqrt 2 * Lattice.jp k.1 := by
  unfold S7PIB_dmode Torus.partialDeriv
  refine (Real.norm_eq_abs _ ▸ (fderiv ℝ (Torus.lift (Torus.realMode k)) (Torus.rep y)).le_opNorm
    (EuclideanSpace.single a (1 : ℝ))).trans ?_
  rw [EuclideanSpace.norm_single]
  simpa using S7PIB_norm_fderiv_mode_le k (Torus.rep y)

theorem S7PIB_summ_jp (s : ℝ) (hs : (d : ℝ) < s) :
    Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-s) := by
  have := summable_jp_rpow (d := d) (s / 2) (by linarith)
  simpa [show 2 * (s / 2) = s by ring] using this

theorem S7PIB_memlp (m : ℝ) (hm : (d : ℝ) < 2 * (m - 1)) (a : Fin d) (y : Torus d) :
    Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * S7PIB_dmode a k y) 2 := by
  rw [Torus.memℓp_two_iff]
  have hs := S7PIB_summ_jp (2 * (m - 1)) hm
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) (hs.mul_left ((2 * Real.sqrt 2) ^ 2))
  have hj := Torus.jp_pos k.1
  have hc := S7PIB_dmode_le a k y
  have hc2 : S7PIB_dmode a k y ^ 2 ≤ (2 * Real.sqrt 2 * Lattice.jp k.1) ^ 2 := by
    rw [← sq_abs (S7PIB_dmode a k y)]
    exact pow_le_pow_left₀ (abs_nonneg _) hc 2
  calc (Lattice.jp k.1 ^ (-m) * S7PIB_dmode a k y) ^ 2
      = (Lattice.jp k.1 ^ (-m)) ^ 2 * S7PIB_dmode a k y ^ 2 := mul_pow _ _ _
    _ ≤ (Lattice.jp k.1 ^ (-m)) ^ 2 * (2 * Real.sqrt 2 * Lattice.jp k.1) ^ 2 :=
        mul_le_mul_of_nonneg_left hc2 (sq_nonneg _)
    _ = (2 * Real.sqrt 2) ^ 2 * ((Lattice.jp k.1 ^ (-m)) ^ 2 * Lattice.jp k.1 ^ 2) := by ring
    _ = (2 * Real.sqrt 2) ^ 2 * Lattice.jp k.1 ^ (-(2 * (m - 1))) := by
        congr 1
        rw [Torus.jp_rpow_sq, ← Real.rpow_natCast (Lattice.jp k.1) 2, ← Real.rpow_add hj]
        congr 1
        push_cast; ring

/-- the element `b_{y,a} ∈ E_m` with Fourier coefficients `∂_a e_k(y)` -/
def S7PIB_bvec (m : ℝ) (a : Fin d) (y : Torus d) : NegSobolev d m :=
  NegSobolev.ofSeq m fun k => S7PIB_dmode a k y

theorem S7PIB_fc_bvec (m : ℝ) (hm : (d : ℝ) < 2 * (m - 1)) (a : Fin d) (y : Torus d)
    (k : NonzeroLattice d) :
    NegSobolev.fourierCoeff (S7PIB_bvec m a y) k = S7PIB_dmode a k y := by
  unfold NegSobolev.fourierCoeff S7PIB_bvec
  rw [NegSobolev.coord_ofSeq_of_mem _ (S7PIB_memlp m hm a y) k, ← mul_assoc,
    ← Real.rpow_add (Torus.jp_pos k.1), add_neg_cancel, Real.rpow_zero, one_mul]

theorem S7PIB_norm_bvec_le (m : ℝ) (hm : (d : ℝ) < 2 * (m - 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : Fin d) (y : Torus d), ‖S7PIB_bvec m a y‖ ≤ C := by
  have hs := S7PIB_summ_jp (2 * (m - 1)) hm
  set K : ℝ := (2 * Real.sqrt 2) ^ 2 * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * (m - 1))) with hK
  refine ⟨Real.sqrt K, Real.sqrt_nonneg _, fun a y => ?_⟩
  obtain ⟨hc2, hn⟩ := NegSobolev.coord_sq (S7PIB_bvec m a y)
  have hco : ∀ k, NegSobolev.coord (S7PIB_bvec m a y) k = Lattice.jp k.1 ^ (-m) * S7PIB_dmode a k y := by
    intro k
    unfold S7PIB_bvec
    exact NegSobolev.coord_ofSeq_of_mem _ (S7PIB_memlp m hm a y) k
  have hle : ∀ k, NegSobolev.coord (S7PIB_bvec m a y) k ^ 2 ≤
      (2 * Real.sqrt 2) ^ 2 * Lattice.jp k.1 ^ (-(2 * (m - 1))) := by
    intro k
    rw [hco k]
    have hj := Torus.jp_pos k.1
    have hc := S7PIB_dmode_le a k y
    have hc2 : S7PIB_dmode a k y ^ 2 ≤ (2 * Real.sqrt 2 * Lattice.jp k.1) ^ 2 := by
      rw [← sq_abs (S7PIB_dmode a k y)]
      exact pow_le_pow_left₀ (abs_nonneg _) hc 2
    calc (Lattice.jp k.1 ^ (-m) * S7PIB_dmode a k y) ^ 2
        = (Lattice.jp k.1 ^ (-m)) ^ 2 * S7PIB_dmode a k y ^ 2 := mul_pow _ _ _
      _ ≤ (Lattice.jp k.1 ^ (-m)) ^ 2 * (2 * Real.sqrt 2 * Lattice.jp k.1) ^ 2 :=
          mul_le_mul_of_nonneg_left hc2 (sq_nonneg _)
      _ = (2 * Real.sqrt 2) ^ 2 * ((Lattice.jp k.1 ^ (-m)) ^ 2 * Lattice.jp k.1 ^ 2) := by ring
      _ = (2 * Real.sqrt 2) ^ 2 * Lattice.jp k.1 ^ (-(2 * (m - 1))) := by
          congr 1
          rw [Torus.jp_rpow_sq, ← Real.rpow_natCast (Lattice.jp k.1) 2, ← Real.rpow_add hj]
          congr 1
          push_cast; ring
  have hsq : ‖S7PIB_bvec m a y‖ ^ 2 ≤ K := by
    rw [hn, hK, ← tsum_mul_left]
    exact hc2.tsum_le_tsum hle (hs.mul_left _)
  exact Real.le_sqrt_of_sq_le hsq

theorem S7PIB_eval_bvec (m : ℝ) (hm : (d : ℝ) < 2 * (m - 1)) (a : Fin d) (y : Torus d)
    (ψ : Torus d → ℝ) :
    NegSobolev.eval (S7PIB_bvec m a y) ψ = ∑' j, Torus.funRealCoeff ψ j * S7PIB_dmode a j y := by
  unfold NegSobolev.eval
  refine tsum_congr fun j => ?_
  rw [S7PIB_fc_bvec m hm a y j, mul_comm]

end HRS.MC.Sec7.S7PIB

end
