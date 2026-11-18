import HRS.MD.EQ29Vocab
import HRS.MD.EQGaussLift

/-!
# EQ-INTERP packet, part 1: path energies, lower semicontinuity, the Hölder interpolation in the Fourier series

* `ce q F`: the squared `E_q`-energy `∑_k ⟨k⟩^{-2q} F̂(k)²` (in `ℝ≥0∞`) of the Fourier coefficients of `F ∈ E_m` (`EQ29.coordEnergy`);
* `qSq q w = sup_t ce q (w t)`: the squared `𝒳_{q,T}`-norm of a path in `𝒳_{m,T}`;
* `ce_lsc`, `qSq_lsc`, `qSq_measurable`; `ofReal_norm_sq_eq_ce`;
* `ce_holder`: `ce m ≤ (ce q)^{1-α} (ce m₁)^α` (TeX `P:eq:Sobolev-interpolate`, L4136-4141) and its path version `norm_sq_le_holder`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MD.EQInterp

variable {d : ℕ}

/-- `∑_k ⟨k⟩^{-2q} F̂(k)²` in `ℝ≥0∞`. -/
def ce (q : ℝ) {m : ℝ} (F : NegSobolev d m) : ℝ≥0∞ :=
  HRS.MD.EQ29.coordEnergy q (fun k => NegSobolev.fourierCoeff F k)

/-- The squared `𝒳_{q,T}`-"norm" `sup_{t ∈ [0,T]} ‖w^t‖²_{E_q}` of a path of `𝒳_{m,T}` (`ℝ≥0∞`-valued). -/
def qSq (q : ℝ) {m T : ℝ} (w : PathSpace d m T) : ℝ≥0∞ :=
  ⨆ t : Set.Icc (0 : ℝ) T, ce q (w.at' t)

theorem continuous_coord {m : ℝ} (k : NonzeroLattice d) :
    Continuous fun F : NegSobolev d m => NegSobolev.coord F k := by
  have : Continuous fun f : lp (fun _ : NonzeroLattice d => ℝ) 2 => f k := by
    refine LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun f g => ?_)
    have := lp.norm_apply_le_norm (by norm_num) (f - g) k
    simpa [dist_eq_norm, Real.dist_eq] using this
  exact this

theorem ce_lsc (q m : ℝ) : LowerSemicontinuous fun F : NegSobolev d m => ce q F := by
  simp only [ce, HRS.MD.EQ29.coordEnergy]
  refine lowerSemicontinuous_tsum fun k => ?_
  refine (ENNReal.continuous_ofReal.comp (continuous_const.mul ?_)).lowerSemicontinuous
  simp only [NegSobolev.fourierCoeff]
  exact (continuous_const.mul (continuous_coord k)).pow 2

theorem continuous_at' (m T : ℝ) (t : Set.Icc (0 : ℝ) T) :
    Continuous fun w : PathSpace d m T => w.at' t :=
  (continuous_eval_const (show Set.Icc (0 : ℝ) T from t) :
    Continuous fun w : C(Set.Icc (0 : ℝ) T, NegSobolev d m) => w t)

theorem qSq_lsc (q m T : ℝ) : LowerSemicontinuous fun w : PathSpace d m T => qSq q w := by
  simp only [qSq]
  refine lowerSemicontinuous_iSup fun t => ?_
  exact (ce_lsc q m).comp (continuous_at' m T t)

theorem qSq_measurable (q m T : ℝ) : Measurable fun w : PathSpace d m T => qSq q w :=
  (qSq_lsc q m T).measurable

theorem ofReal_norm_sq_eq_ce {m : ℝ} (F : NegSobolev d m) :
    ENNReal.ofReal (‖F‖ ^ 2) = ce m F := by
  obtain ⟨h1, h2⟩ := NegSobolev.coord_sq F
  rw [h2, ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg _) h1]
  simp only [ce, HRS.MD.EQ29.coordEnergy, NegSobolev.fourierCoeff]
  refine tsum_congr fun k => ?_
  congr 1
  have hj := Torus.jp_pos k.1
  rw [mul_pow, Torus.jp_rpow_sq, ← mul_assoc, show -2 * m = -(2 * m) by ring,
    ← Real.rpow_add hj]
  simp

theorem ce_sub_le {m : ℝ} (q : ℝ) (F G : NegSobolev d m) :
    ce q (F - G) ≤ 2 * ce q F + 2 * ce q G := by
  simp only [ce, HRS.MD.EQ29.coordEnergy]
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun k => ?_
  have hj : 0 ≤ Lattice.jp k.1 ^ (-2 * q) := Real.rpow_nonneg (Torus.jp_pos k.1).le _
  have hc : NegSobolev.fourierCoeff (F - G) k = NegSobolev.fourierCoeff F k - NegSobolev.fourierCoeff G k := by
    simp only [NegSobolev.fourierCoeff]
    have : NegSobolev.coord (F - G) k = NegSobolev.coord F k - NegSobolev.coord G k := rfl
    rw [this]; ring
  rw [hc]
  have e1 : (2 : ℝ≥0∞) * ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * q) * NegSobolev.fourierCoeff F k ^ 2) =
      ENNReal.ofReal (2 * (Lattice.jp k.1 ^ (-2 * q) * NegSobolev.fourierCoeff F k ^ 2)) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  have e2 : (2 : ℝ≥0∞) * ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * q) * NegSobolev.fourierCoeff G k ^ 2) =
      ENNReal.ofReal (2 * (Lattice.jp k.1 ^ (-2 * q) * NegSobolev.fourierCoeff G k ^ 2)) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  rw [e1, e2, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  nlinarith [mul_nonneg hj (sq_nonneg (NegSobolev.fourierCoeff F k + NegSobolev.fourierCoeff G k))]

theorem qSq_sub_le {m T : ℝ} (q : ℝ) (x y : PathSpace d m T) :
    qSq q (x - y) ≤ 2 * qSq q x + 2 * qSq q y := by
  simp only [qSq]
  refine iSup_le fun t => ?_
  have h : (x - y).at' t = x.at' t - y.at' t := rfl
  rw [h]
  refine (ce_sub_le q _ _).trans (add_le_add ?_ ?_)
  · exact mul_le_mul_right (le_iSup (fun t => ce q (x.at' t)) t) _
  · exact mul_le_mul_right (le_iSup (fun t => ce q (y.at' t)) t) _

end HRS.MD.EQInterp
