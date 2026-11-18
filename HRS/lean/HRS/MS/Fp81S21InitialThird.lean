import HRS.MS.Fp81S21InitialULim3
import HRS.MS.R2SeAux43

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open S45 S99
open HRS.Whole
open HRS (Euc cbNorm)
open HRS.MS.R26T3

/-- The actual initial-law response vector, with coordinates `r26t3_a R (φ j) x`. -/
def fp81s21_initial_ellv {p : Parameters} {δ : ℝ}
    (R : Trajectory p δ) (φ : ℕ → Euc p.d → ℝ) (x : Euc p.d) : SeqL2 :=
  SeqL2.ofSeq (fun j => r26t3_a R (φ j) x)

/-- The actual initial-law response coordinates are square summable, so `ofSeq` does not
fall back to zero. -/
theorem fp81s21_initial_ellv_memlp
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    {φ : ℕ → Euc p.d → ℝ} (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ) (x : Euc p.d) :
    Memℓp (fun j => r26t3_a R (φ j) x) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  let b : ℕ → ℝ := fun j => cbNorm (fp81s21_J1 p.d) (φ j)
  have hb0 : ∀ j, 0 ≤ b j := fun j => by
    dsimp [b]
    exact HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hbs : Summable (fun j => F.K * b j) := hφ.2.mul_left _
  have hbound : ∀ j, |r26t3_a R (φ j) x| ≤ F.K * b j := by
    intro j
    have hs := HRS.MS.Tc5.tc5_cb_sup_le (F.amem j) x
    calc
      |r26t3_a R (φ j) x| ≤ cbNorm (fp81s21_k0 p.d) (r26t3_a R (φ j)) := by
        simpa [Real.norm_eq_abs] using hs
      _ ≤ F.K * b j := by simpa [b] using F.anorm j
  have hs2 : Summable (fun j => (F.K * b j) ^ 2) :=
    S45.s45_summable_sq (fun j => mul_nonneg F.hK (hb0 j)) hbs
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) hs2
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (hbound j) 2

/-- Coordinates of the actual initial-law response vector. -/
theorem fp81s21_initial_ellv_coord
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    {φ : ℕ → Euc p.d → ℝ} (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ) (x : Euc p.d) (j : ℕ) :
    SeqL2.coord (fp81s21_initial_ellv R φ x) j = r26t3_a R (φ j) x :=
  s45_coord_ofSeq (fp81s21_initial_ellv_memlp R hφ F x) j

/-- The actual response vector is bounded in `ℓ²` by the summable feature envelope. -/
theorem fp81s21_initial_ellv_norm_le
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    {φ : ℕ → Euc p.d → ℝ} (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ) (x : Euc p.d) :
    ‖fp81s21_initial_ellv R φ x‖ ≤
      F.K * ∑' j, cbNorm (fp81s21_J1 p.d) (φ j) := by
  let ℓ := fp81s21_initial_ellv R φ x
  let b : ℕ → ℝ := fun j => cbNorm (fp81s21_J1 p.d) (φ j)
  have hbs : Summable (fun j => F.K * b j) := hφ.2.mul_left _
  have hcoord : ∀ j, |SeqL2.coord ℓ j| ≤ F.K * b j := by
    intro j
    rw [fp81s21_initial_ellv_coord R hφ F x j]
    have hs := HRS.MS.Tc5.tc5_cb_sup_le (F.amem j) x
    calc
      |r26t3_a R (φ j) x| ≤ cbNorm (fp81s21_k0 p.d) (r26t3_a R (φ j)) := by
        simpa [Real.norm_eq_abs] using hs
      _ ≤ F.K * b j := by simpa [b] using F.anorm j
  have hcoordsum : Summable (fun j => |SeqL2.coord ℓ j|) :=
    Summable.of_norm_bounded hbs (fun j => by
      rw [Real.norm_eq_abs]
      simpa only [abs_abs] using hcoord j)
  have hvec : Summable (fun j => SeqL2.coord ℓ j • s45_e1 j (1 : ℝ)) :=
    Summable.of_norm_bounded hbs (fun j => by
      rw [norm_smul, s99_e1_norm, mul_one, Real.norm_eq_abs]
      exact hcoord j)
  have hnormsum : Summable (fun j => ‖SeqL2.coord ℓ j • s45_e1 j (1 : ℝ)‖) := by
    simpa only [norm_smul, Real.norm_eq_abs, s99_e1_norm, mul_one] using hcoordsum
  have hs := S99.s99_coord_hasSum ℓ
  calc
    ‖ℓ‖ = ‖∑' j, SeqL2.coord ℓ j • s45_e1 j (1 : ℝ)‖ := by rw [hs.tsum_eq]
    _ ≤ ∑' j, ‖SeqL2.coord ℓ j • s45_e1 j (1 : ℝ)‖ := norm_tsum_le_tsum_norm hnormsum
    _ = ∑' j, |SeqL2.coord ℓ j| := by
      refine tsum_congr fun j => ?_
      rw [norm_smul, s99_e1_norm, mul_one, Real.norm_eq_abs]
    _ ≤ ∑' j, F.K * b j := hcoordsum.tsum_le_tsum hcoord hbs
    _ = F.K * ∑' j, b j := by rw [← tsum_mul_left]

#print axioms fp81s21_initial_ellv_memlp
#print axioms fp81s21_initial_ellv_coord
#print axioms fp81s21_initial_ellv_norm_le

end HRS.Fp81.S21

end
