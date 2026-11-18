import HRS.Commutator.Torus.TPOSAux10

/-!
# T-POS helpers, part 11: the Fourier series `∑_k ĝ_η(k) cos(2πk·x)`

Continuity and Fourier coefficients of the series built from the (absolutely summable) even coefficients `gTcoef`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s η : ℝ}

/-- The Fourier series with coefficients `gTcoef`. -/
def tposH (d : ℕ) (s η : ℝ) (x : Torus d) : ℝ :=
  ∑' k : Lattice d, gTcoef d s η k * Torus.cosMode k x

lemma tposH_continuous (hsum : Summable fun k : Lattice d => |gTcoef d s η k|) :
    Continuous (tposH d s η) := by
  unfold tposH
  refine continuous_tsum (u := fun k : Lattice d => |gTcoef d s η k|)
    (fun k => continuous_const.mul (Torus.continuous_cosMode k)) hsum (fun k x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have := abs_cosMode_le k x
  calc |gTcoef d s η k| * |Torus.cosMode k x| ≤ |gTcoef d s η k| * 1 :=
        mul_le_mul_of_nonneg_left this (abs_nonneg _)
    _ = _ := mul_one _

lemma tposH_fcoef (hsum : Summable fun k : Lattice d => |gTcoef d s η k|) (k : Lattice d) :
    Torus.fcoef (tposH d s η : Torus d → ℝ) k = ((gTcoef d s η k : ℝ) : ℂ) := by
  set c : Lattice d → ℝ := fun l => gTcoef d s η l with hc
  set F : Lattice d → Torus d → ℂ := fun l x => Torus.mode (-k) x * (((c l * Torus.cosMode l x : ℝ)) : ℂ)
    with hF
  have hFcont : ∀ l, Continuous (F l) := fun l =>
    (Torus.continuous_mode _).mul (Complex.continuous_ofReal.comp
      (continuous_const.mul (Torus.continuous_cosMode l)))
  have hFint : ∀ l, Integrable (F l) := fun l =>
    (hFcont l).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hFnorm : ∀ l x, ‖F l x‖ ≤ |c l| := by
    intro l x
    simp only [hF]
    rw [norm_mul, Torus.norm_mode, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    have := abs_cosMode_le l x
    calc |c l| * |Torus.cosMode l x| ≤ |c l| * 1 := mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = _ := mul_one _
  have hsumF : Summable fun l => ∫ x, ‖F l x‖ := by
    refine Summable.of_nonneg_of_le (fun l => integral_nonneg fun x => norm_nonneg _) (fun l => ?_) hsum
    calc ∫ x, ‖F l x‖ ≤ ∫ x : Torus d, |c l| :=
          integral_mono (hFint l).norm (integrable_const _) (fun x => hFnorm l x)
      _ = _ := by simp [hc]
  have hsw := integral_tsum_of_summable_integral_norm hFint hsumF
  have hpt : ∀ x : Torus d, ∑' l, F l x = Torus.mode (-k) x * ((tposH d s η x : ℝ) : ℂ) := by
    intro x
    have hs : Summable fun l => c l * Torus.cosMode l x := by
      refine Summable.of_norm_bounded hsum (fun l => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have := abs_cosMode_le l x
      calc |c l| * |Torus.cosMode l x| ≤ |c l| * 1 := mul_le_mul_of_nonneg_left this (abs_nonneg _)
        _ = _ := mul_one _
    simp only [hF]
    rw [tsum_mul_left, ← Complex.ofReal_tsum]
    rfl
  unfold Torus.fcoef
  simp_rw [← hpt]
  rw [← hsw]
  have hl : ∀ l, ∫ x, F l x = (c l : ℂ) * (((if l = k then 1 else 0) + (if l = -k then 1 else 0)) / 2) := by
    intro l
    simp only [hF]
    have : ∀ x : Torus d, Torus.mode (-k) x * (((c l * Torus.cosMode l x : ℝ)) : ℂ) =
        (c l : ℂ) * (Torus.mode (-k) x * ((Torus.cosMode l x : ℝ) : ℂ)) := by
      intro x; push_cast; ring
    simp_rw [this]
    rw [integral_const_mul, KernelAux.integral_mode_cos]
  simp_rw [hl]
  have hneg : c (-k) = c k := tpos_gTcoef_neg k
  have hsplit : ∀ l, (c l : ℂ) * (((if l = k then 1 else 0) + (if l = -k then 1 else 0)) / 2) =
      (if l = k then (c k : ℂ) / 2 else 0) + (if l = -k then (c (-k) : ℂ) / 2 else 0) := by
    intro l
    split_ifs with h1 h2 h2
    · rw [h1, hneg]; ring
    · rw [h1]; ring
    · rw [h2]; ring
    · simp
  simp_rw [hsplit]
  rw [((hasSum_ite_eq k ((c k : ℂ) / 2)).add (hasSum_ite_eq (-k) ((c (-k) : ℂ) / 2))).tsum_eq, hneg]
  simp only [hc]
  push_cast
  ring

lemma tposH_zero (hsum : Summable fun k : Lattice d => |gTcoef d s η k|) :
    tposH d s η 0 = gTorus0 d s η := by
  unfold tposH gTorus0
  refine tsum_congr fun k => ?_
  have : Torus.cosMode k (0 : Torus d) = 1 := by
    have h0 : (0 : Torus d) = Torus.mk 0 := by funext i; simp [Torus.mk]
    rw [h0, Torus.cosMode_mk]
    simp [Lattice.dot]
  rw [this, mul_one]

end HRS.Commutator.TorusNote
