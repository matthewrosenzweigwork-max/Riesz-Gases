import HRS.MC.D3T1Aux3
import HRS.PDE.Fourier

/-!
# Packet D3T3, auxiliary facts: Fourier-side Laplacian at the origin, decay of `ψ̂`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HRS.MC.D3T3

open HRS HRS.MC.FDLE HRS.MC.Per

variable {d : ℕ}

/-- Summability of `⟨k⟩^2 |φ̂(k)|` for a smooth function on the torus. -/
lemma d3f_summable_jp2 {φ : Torus d → ℝ} (hφ : ∀ n : ℕ, ContDiff ℝ n (Torus.lift φ)) :
    Summable (fun k : Lattice d => Lattice.jp k ^ 2 * ‖Torus.fcoef φ k‖) := by
  obtain ⟨B, hB⟩ := Torus.fcoef_pow_decay (hφ (d + 3))
  rw [Torus.summable_lattice_iff]
  have hs := summable_jp_rpow (d := d) (((d + 1 : ℕ) : ℝ) / 2)
    (by push_cast; linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)])
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (pow_nonneg (Torus.jp_pos k.1).le _)
    (norm_nonneg _)) (fun k => ?_) (hs.mul_left B)
  have hj := Torus.jp_pos k.1
  have e : Lattice.jp k.1 ^ (-(2 * (((d + 1 : ℕ) : ℝ) / 2))) = (Lattice.jp k.1 ^ (d + 1))⁻¹ := by
    rw [show -(2 * (((d + 1 : ℕ) : ℝ) / 2)) = -((d + 1 : ℕ) : ℝ) by ring, Real.rpow_neg hj.le,
      Real.rpow_natCast]
  rw [e]
  have h := hB k
  have h3 : Lattice.jp k.1 ^ (d + 3) = Lattice.jp k.1 ^ 2 * Lattice.jp k.1 ^ (d + 1) := by
    rw [← pow_add]; ring_nf
  rw [h3] at h
  rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hj _)]
  nlinarith [h]

/-- `Δφ(0) = -4π² ∑ |k|² φ̂(k)` for smooth `φ`, with summability. -/
theorem d3f_lap_zero {φ : Torus d → ℝ} (hφ : ∀ n : ℕ, ContDiff ℝ n (Torus.lift φ)) :
    Summable (fun k : Lattice d => Lattice.enorm k ^ 2 * (Torus.fcoef φ k).re) ∧
    Torus.laplacian φ 0 =
      -(4 * Real.pi ^ 2 * ∑' k : Lattice d, Lattice.enorm k ^ 2 * (Torus.fcoef φ k).re) := by
  have h2 : Torus.IsCk 2 φ := by
    have := hφ 2
    unfold Torus.IsCk
    exact_mod_cast this
  have hjp := d3f_summable_jp2 hφ
  have hle : ∀ k : Lattice d, 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 ≤ Lattice.jp k ^ 2 := by
    intro k
    unfold Lattice.jp
    rw [Real.sq_sqrt (by positivity)]
    linarith
  have hsum1 : Summable (fun k : Lattice d => Lattice.enorm k ^ 2 * (Torus.fcoef φ k).re) := by
    refine Summable.of_norm_bounded (g := fun k => Lattice.jp k ^ 2 * ‖Torus.fcoef φ k‖) hjp
      (fun k => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
    have h1 : Lattice.enorm k ^ 2 ≤ Lattice.jp k ^ 2 := by
      have hp : (1 : ℝ) ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
      have := mul_le_mul_of_nonneg_right hp (sq_nonneg (Lattice.enorm k))
      linarith [hle k]
    exact mul_le_mul h1 (Complex.abs_re_le_norm _) (abs_nonneg _) (sq_nonneg _)
  refine ⟨hsum1, ?_⟩
  -- continuity of the Laplacian
  have hcont : Continuous (Torus.laplacian φ) := by
    have : Torus.laplacian φ = fun x => ∑ j, Torus.partialDeriv j (Torus.partialDeriv j φ) x :=
      funext (HRS.PDE.laplacian_eq_sum φ h2)
    rw [this]
    exact continuous_finset_sum _ fun j _ => HRS.PDE.continuous_partialDeriv j _
      (HRS.PDE.isCk_one_partialDeriv j φ h2)
  have hco := HRS.PDE.coeffOf_laplacian φ h2
  have hsC : Summable fun k : Lattice d => ‖HRS.PDE.coeffOf (Torus.laplacian φ) k‖ := by
    rw [hco]
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) hjp
    simp only [HRS.PDE.laplaceCoeff, HRS.PDE.coeffOf_eq_fcoef, norm_mul, norm_neg, Complex.norm_real,
      Real.norm_eq_abs]
    rw [abs_of_pos (by norm_num : (0:ℝ) < 4), abs_of_nonneg (sq_nonneg Real.pi),
      abs_of_nonneg (sq_nonneg (Lattice.enorm k))]
    exact mul_le_mul_of_nonneg_right (hle k) (norm_nonneg _)
  have hinv := HRS.PDE.toFun_coeffOf (Torus.laplacian φ) hcont hsC
  have h0 := congrFun hinv 0
  rw [← h0]
  unfold HRS.PDE.toFun HRS.PDE.series
  rw [hco]
  have hm0 : ∀ k : Lattice d, Torus.mode k (0 : Torus d) = 1 := fun k => by
    simp [Torus.mode, UnitAddTorus.mFourier]
  simp only [hm0, mul_one, HRS.PDE.laplaceCoeff, HRS.PDE.coeffOf_eq_fcoef]
  have hs : Summable fun k : Lattice d =>
      (-((4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 : ℝ) : ℂ) * Torus.fcoef φ k) := by
    refine Summable.of_norm (hsC.congr fun k => ?_)
    rw [hco]; simp [HRS.PDE.laplaceCoeff, HRS.PDE.coeffOf_eq_fcoef]
  rw [Complex.re_tsum hs, ← tsum_mul_left, ← tsum_neg]
  refine tsum_congr fun k => ?_
  rw [neg_mul, Complex.neg_re, Complex.re_ofReal_mul]
  ring

end HRS.MC.D3T3
