import Mathlib

/-!
# Worker U8 aux 19: `L^p` norm of a function with polynomial decay
-/

noncomputable section

open MeasureTheory

namespace HRS.U8

variable {d : ℕ}

theorem u8_decay_memLp (γ p : ℝ) (hp : 0 < p) (hγp : (d : ℝ) < γ * p) :
    MemLp (fun x : EuclideanSpace ℝ (Fin d) => (1 + ‖x‖) ^ (-γ)) (ENNReal.ofReal p) volume := by
  have hm : AEStronglyMeasurable (fun x : EuclideanSpace ℝ (Fin d) => (1 + ‖x‖) ^ (-γ)) volume :=
    ((measurable_const.add measurable_norm).pow_const _).aestronglyMeasurable
  rw [← integrable_norm_rpow_iff hm (by simpa using hp) ENNReal.ofReal_ne_top]
  have hint := integrable_one_add_norm (E := EuclideanSpace ℝ (Fin d)) (μ := volume)
    (r := γ * p) (by simpa using hγp)
  refine hint.congr (Filter.Eventually.of_forall (fun x => ?_))
  have h0 : 0 ≤ 1 + ‖x‖ := by positivity
  show (1 + ‖x‖) ^ (-(γ * p)) = ‖(1 + ‖x‖) ^ (-γ)‖ ^ (ENNReal.ofReal p).toReal
  rw [ENNReal.toReal_ofReal hp.le, Real.norm_of_nonneg (Real.rpow_nonneg h0 _),
    ← Real.rpow_mul h0]
  congr 1; ring

theorem u8_decay_bound (γ p : ℝ) (hp : 0 < p) (hγp : (d : ℝ) < γ * p) (c : ℝ) (hc : 0 ≤ c)
    (w : EuclideanSpace ℝ (Fin d) → ℝ) (hw : AEStronglyMeasurable w volume)
    (hb : ∀ x, |w x| ≤ c * (1 + ‖x‖) ^ (-γ)) :
    MemLp w (ENNReal.ofReal p) volume ∧
      eLpNorm w (ENNReal.ofReal p) volume ≤ ENNReal.ofReal c *
        eLpNorm (fun x : EuclideanSpace ℝ (Fin d) => (1 + ‖x‖) ^ (-γ)) (ENNReal.ofReal p) volume := by
  have hmem := u8_decay_memLp (d := d) γ p hp hγp
  have hmono : eLpNorm w (ENNReal.ofReal p) volume ≤
      eLpNorm (c • fun x : EuclideanSpace ℝ (Fin d) => (1 + ‖x‖) ^ (-γ)) (ENNReal.ofReal p) volume :=
    eLpNorm_mono_real hw (fun x => by
      simpa [Pi.smul_apply, smul_eq_mul] using hb x)
  refine ⟨?_, ?_⟩
  · exact (hmem.const_smul c).of_le hw (Filter.Eventually.of_forall (fun x => by
      simpa [Real.norm_eq_abs] using (hb x).trans (le_abs_self _)))
  · rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hc] at hmono
    exact hmono

end HRS.U8
