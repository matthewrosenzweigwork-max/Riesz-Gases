import HRS.Commutator.Torus.LEIBTAux12
import HRS.Commutator.Torus.Defs

/-!
# LEIB-T helpers, part 13: Fourier series of a smooth torus function, lifted to `ℝ^d` at scale `η`
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- The frequency `η k ∈ ℝ^d` of the mode `e_k` seen at scale `η`. -/
def leibt_lam (η : ℝ) (k : Lattice d) : 𝔼 := η • Lattice.toEuc k

lemma leibt_norm_lam {η : ℝ} (hη : 0 < η) (k : Lattice d) : ‖leibt_lam η k‖ = η * Lattice.enorm k := by
  unfold leibt_lam Lattice.enorm
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη]

lemma leibt_m_lam (α η : ℝ) (hη : 0 < η) (k : Lattice d) :
    leibt_m α (leibt_lam η k) =
      (((1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2) ^ (α / 2) : ℝ) : ℂ) := by
  unfold leibt_m HRS.Commutator.Whole.XLI.bsymX
  rw [leibt_norm_lam hη]
  congr 3
  ring

lemma leibt_one_add_le_jp {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (k : Lattice d) :
    1 + ‖leibt_lam η k‖ ≤ 2 * Lattice.jp k := by
  rw [leibt_norm_lam hη]
  have he : 0 ≤ Lattice.enorm k := norm_nonneg _
  have hj : Lattice.jp k ^ 2 = 1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 := by
    unfold Lattice.jp
    rw [Real.sq_sqrt (by positivity)]
  have hj0 : 0 ≤ Lattice.jp k := Real.sqrt_nonneg _
  have hpi : 3 < Real.pi := Real.pi_gt_three
  by_contra hcon
  push Not at hcon
  have h1 : 2 * Lattice.jp k < 1 + η * Lattice.enorm k := hcon
  have h2 : (2 * Lattice.jp k) ^ 2 < (1 + η * Lattice.enorm k) ^ 2 := by
    apply pow_lt_pow_left₀ h1 (by positivity) (by norm_num)
  have a : η * Lattice.enorm k ≤ Lattice.enorm k := by nlinarith
  have b : (η * Lattice.enorm k) ^ 2 ≤ Lattice.enorm k ^ 2 :=
    pow_le_pow_left₀ (by positivity) a 2
  have c : 9 ≤ Real.pi ^ 2 := by nlinarith
  have d9 : 9 * Lattice.enorm k ^ 2 ≤ Real.pi ^ 2 * Lattice.enorm k ^ 2 :=
    mul_le_mul_of_nonneg_right c (sq_nonneg _)
  nlinarith [sq_nonneg (Lattice.enorm k - 1)]

lemma leibt_coef_summable {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) {f : Torus d → ℝ}
    (hf : Torus.IsSmooth f) (p : ℕ) :
    Summable fun k : Lattice d => ‖Torus.fcoef f k‖ * (1 + ‖leibt_lam η k‖) ^ p := by
  have hcd : ContDiff ℝ ((p + (d + 1) : ℕ) : ℕ∞) (Torus.lift f) := by
    have := hf
    unfold Torus.IsSmooth Torus.IsCk at this
    exact this.of_le (by exact_mod_cast le_top)
  obtain ⟨B, hB⟩ := Torus.fcoef_pow_decay (n := p + (d + 1)) hcd
  rw [Torus.summable_lattice_iff]
  have hs := summable_jp_rpow (d := d) (((d + 1 : ℕ) : ℝ) / 2) (by push_cast; linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)])
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) (hs.mul_left (B * 2 ^ p))
  have hj := Torus.jp_pos k.1
  have e : Lattice.jp k.1 ^ (-(2 * (((d + 1 : ℕ) : ℝ) / 2))) = (Lattice.jp k.1 ^ (d + 1))⁻¹ := by
    rw [show -(2 * (((d + 1 : ℕ) : ℝ) / 2)) = -((d + 1 : ℕ) : ℝ) by ring, Real.rpow_neg hj.le,
      Real.rpow_natCast]
  rw [e]
  have h1 : (1 + ‖leibt_lam η k.1‖) ^ p ≤ 2 ^ p * Lattice.jp k.1 ^ p := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (leibt_one_add_le_jp hη hη1 k.1) p
  have h2 := hB k
  rw [pow_add] at h2
  have h3 : ‖Torus.fcoef f k.1‖ * Lattice.jp k.1 ^ p ≤ B * (Lattice.jp k.1 ^ (d + 1))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hj _)]
    calc ‖Torus.fcoef f k.1‖ * Lattice.jp k.1 ^ p * Lattice.jp k.1 ^ (d + 1)
        = ‖Torus.fcoef f k.1‖ * (Lattice.jp k.1 ^ p * Lattice.jp k.1 ^ (d + 1)) := by ring
      _ ≤ B := h2
  calc ‖Torus.fcoef f k.1‖ * (1 + ‖leibt_lam η k.1‖) ^ p
      ≤ ‖Torus.fcoef f k.1‖ * (2 ^ p * Lattice.jp k.1 ^ p) := by gcongr
    _ = 2 ^ p * (‖Torus.fcoef f k.1‖ * Lattice.jp k.1 ^ p) := by ring
    _ ≤ 2 ^ p * (B * (Lattice.jp k.1 ^ (d + 1))⁻¹) := by gcongr
    _ = B * 2 ^ p * (Lattice.jp k.1 ^ (d + 1))⁻¹ := by ring

end HRS.Commutator.TorusNote
