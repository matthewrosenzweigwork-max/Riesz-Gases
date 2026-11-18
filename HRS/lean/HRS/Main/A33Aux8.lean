import Mathlib
import HRS.Main.A33Aux7

/-!
# Packet A33, helper 8: the trace-class (Hilbert-Schmidt) estimate for the noise vectors
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace

namespace HRS.A33

open HRS HRS.PDE HRS.PDE.ET

variable {d : ℕ}

theorem a33_sobolevNorm_realMode (m : ℝ) (k : NonzeroLattice d) :
    sobolevNorm m (Torus.realMode k) = Lattice.jp k.1 ^ m := by
  have hmean : Torus.mean (Torus.realMode k) = 0 := Torus.integral_realMode k
  have hcoef : ∀ l : NonzeroLattice d, Torus.funRealCoeff (Torus.realMode k) l =
      if l = k then 1 else 0 := fun l => by
    unfold Torus.funRealCoeff
    rw [Torus.realMode_orthonormal l k]
  unfold sobolevNorm
  rw [hmean]
  have hsum : ∑' l : NonzeroLattice d, Lattice.jp l.1 ^ (2 * m) *
      Torus.funRealCoeff (Torus.realMode k) l ^ 2 = Lattice.jp k.1 ^ (2 * m) := by
    simp_rw [hcoef]
    rw [tsum_eq_single k]
    · simp
    · intro l hl; simp [hl]
  rw [hsum]
  have hj := Torus.jp_pos k.1
  rw [zero_pow two_ne_zero, zero_add, Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
  rw [← Real.rpow_add hj]
  ring_nf

namespace A33Setup

variable (S : A33Setup d)

/-- `‖h_{t,e_k}‖ ≤ K ⟨k⟩^{m_*}`. -/
theorem vec_realMode_norm (q : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, t ∈ Set.Icc 0 S.T → ∀ k : NonzeroLattice d,
      ‖a33_vec S q t (Torus.realMode k)‖ ≤ K * Lattice.jp k.1 ^ (mStar d : ℝ) := by
  haveI := S.rho.nu_finite
  obtain ⟨B, hB0, hB⟩ := S.g_bound' q
  refine ⟨(measureUnivNNReal (a33_nu d S.T S.ρ) : ℝ) ^ ((2 : ENNReal).toReal)⁻¹ * B,
    mul_nonneg (by positivity) hB0, fun {t} ht k => ?_⟩
  have h0 : 0 ≤ B * Lattice.jp k.1 ^ (mStar d : ℝ) :=
    mul_nonneg hB0 (Real.rpow_nonneg (Torus.jp_pos _).le _)
  have := Lp.norm_le_of_ae_bound (μ := a33_nu d S.T S.ρ) (p := 2)
    (f := a33_vec S q t (Torus.realMode k)) h0 (by
      filter_upwards [S.vec_ae q ht (HRS.FieldSingAux.isSmooth_realMode k)] with p hp
      rw [hp]
      have := hB t ht _ (HRS.FieldSingAux.isSmooth_realMode k) p
      rwa [a33_sobolevNorm_realMode] at this)
  calc _ ≤ _ := this
    _ = _ := by ring

/-- The Hilbert-Schmidt condition `∑_k ⟨k⟩^{-2J} ‖h_{t,e_k}‖² < ∞`. -/
theorem trace_summable (q : ℝ) {t : ℝ} (ht : t ∈ Set.Icc 0 S.T) :
    Summable fun k : NonzeroLattice d =>
      (Lattice.jp k.1 ^ (-(S.J : ℝ)) * ‖a33_vec S q t (Torus.realMode k)‖) ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := S.vec_realMode_norm q
  have hd2 : (d : ℝ) < 2 * ((S.J : ℝ) - mStar d) := by
    have h1 : ((mStar d + d : ℕ) : ℝ) ≤ S.J := by exact_mod_cast S.hJ2
    push_cast at h1
    have h2 : (1 : ℝ) ≤ d := by exact_mod_cast S.hd
    linarith
  have hs := (StaticLimitAux.summable_wgt_sq (d := d) (m := (S.J : ℝ) - mStar d) hd2).mul_left (K ^ 2)
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) hs
  have hj := Torus.jp_pos k.1
  have h1 : Lattice.jp k.1 ^ (-(S.J : ℝ)) * ‖a33_vec S q t (Torus.realMode k)‖ ≤
      K * StaticLimitAux.wgt ((S.J : ℝ) - mStar d) k := by
    calc _ ≤ Lattice.jp k.1 ^ (-(S.J : ℝ)) * (K * Lattice.jp k.1 ^ (mStar d : ℝ)) :=
          mul_le_mul_of_nonneg_left (hK ht k) (Real.rpow_nonneg hj.le _)
      _ = K * StaticLimitAux.wgt ((S.J : ℝ) - mStar d) k := by
          unfold StaticLimitAux.wgt
          rw [show Lattice.jp k.1 ^ (-(S.J : ℝ)) * (K * Lattice.jp k.1 ^ (mStar d : ℝ)) =
            K * (Lattice.jp k.1 ^ (-(S.J : ℝ)) * Lattice.jp k.1 ^ (mStar d : ℝ)) by ring,
            ← Real.rpow_add hj]
          congr 2; ring
  calc _ ≤ (K * StaticLimitAux.wgt ((S.J : ℝ) - mStar d) k) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg (Real.rpow_nonneg hj.le _) (norm_nonneg _)) h1 2
    _ = _ := by ring

end A33Setup

end HRS.A33
