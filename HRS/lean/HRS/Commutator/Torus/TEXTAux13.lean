import HRS.Commutator.Torus.TEXTAux12
import HRS.Energy.Commutator.Basic

/-!
# T-EXT-A helpers, part 13: `embedding_T`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s : ℝ}

lemma text_enorm_zero : Lattice.enorm (0 : Lattice d) = 0 := by
  unfold Lattice.enorm
  have : Lattice.toEuc (0 : Lattice d) = 0 := by ext i; simp [Lattice.toEuc]
  rw [this, norm_zero]

theorem text_embedding_main (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Torus d → Euc d) (F : ℝ), 0 ≤ F → Commutator.HasFracBound d v F →
      ∃ w : Torus d → Euc d, IsFracDeriv (((d : ℝ) - s) / 2) v w ∧
        eLpNorm w (ENNReal.ofReal (2 * d / ((d : ℝ) - s - 2))) volume ≤ ENNReal.ofReal (C * F) := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  set σ : ℝ := (s + 1) / 2 with hσ
  have hσpos : 0 < σ := by rw [hσ]; linarith
  set p : ℝ≥0∞ := ENNReal.ofReal (2 * d / ((d : ℝ) - 1)) with hp
  set q : ℝ≥0∞ := ENNReal.ofReal (2 * d / ((d : ℝ) - s - 2)) with hq
  have hd1' : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  have hd2' : (0 : ℝ) < (d : ℝ) - s - 2 := by linarith
  have hp1 : 1 < p := by
    rw [hp, ENNReal.one_lt_ofReal, one_lt_div hd1']; linarith
  have hpq : p < q := by
    rw [hp, hq, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    rw [div_lt_div_iff₀ hd1' hd2']
    nlinarith
  have hqt : q < ⊤ := ENNReal.ofReal_lt_top
  have hrel : q⁻¹ = p⁻¹ - ENNReal.ofReal (σ / d) := by
    rw [hp, hq, ← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_inv_of_pos (by positivity),
      ← ENNReal.ofReal_sub _ (by positivity)]
    congr 1
    field_simp
    ring
  obtain ⟨Ch, hChpos, hCh⟩ := text_hls_main hd1 σ p q hp1 hpq hqt hσpos hrel
  refine ⟨d * Ch, by positivity, fun v F hF hfb => ?_⟩
  obtain ⟨w₀, hw₀, hnorm⟩ := hfb
  have hw₀mem : MemLp w₀ p volume :=
    memLp_iff.2 (lt_of_le_of_lt hnorm ENNReal.ofReal_lt_top)
  have hw₀m : AEStronglyMeasurable w₀ volume := hw₀mem.aestronglyMeasurable
  have hcomp : ∀ j : Fin d, AEStronglyMeasurable (fun x => w₀ x j) volume := fun j =>
    (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable hw₀m
  have hfmem : ∀ j : Fin d, eLpNorm (fun x => w₀ x j) p volume ≤ ENNReal.ofReal F := fun j => by
    refine le_trans (eLpNorm_mono (hcomp j) fun x => ?_) hnorm
    rw [Real.norm_eq_abs]
    simpa using PiLp.norm_apply_le (w₀ x) j
  have hf0 : ∀ j : Fin d, Torus.fcoef (fun x => w₀ x j) 0 = 0 := fun j => by
    rw [hw₀ j 0]
    rw [text_enorm_zero, mul_zero, Real.zero_rpow (by positivity)]
    simp
  have hex : ∀ j : Fin d, ∃ h : Torus d → ℝ, MemLp h q volume ∧ Torus.fcoef h 0 = 0 ∧
      (∀ k : Lattice d, k ≠ 0 → Torus.fcoef h k =
        (((2 * Real.pi * Lattice.enorm k) ^ (-σ) : ℝ) : ℂ) * Torus.fcoef (fun x => w₀ x j) k) ∧
      eLpNorm h q volume ≤ ENNReal.ofReal Ch * eLpNorm (fun x => w₀ x j) p volume := fun j =>
    hCh (fun x => w₀ x j) (memLp_iff.2 (lt_of_le_of_lt (hfmem j) ENNReal.ofReal_lt_top)) (hf0 j)
  choose h hmem h0 hcoef hhn using hex
  refine ⟨fun x => WithLp.toLp 2 (fun j => h j x), ?_, ?_⟩
  · intro j k
    have hfun : (fun x => (WithLp.toLp 2 (fun j => h j x) : Euc d) j) = h j := by
      funext x; simp
    rw [hfun]
    by_cases hk : k = 0
    · subst hk
      rw [h0 j]
      rw [text_enorm_zero, mul_zero, Real.zero_rpow (by
        have : (0 : ℝ) < ((d : ℝ) - s) / 2 := by linarith
        exact this.ne')]
      simp
    · rw [hcoef j k hk, hw₀ j k, ← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add (by
        have : 0 < Lattice.enorm k := by
          unfold Lattice.enorm
          rw [norm_pos_iff]
          intro h0; apply hk; funext i
          have := congrFun (congrArg (fun v : Euc d => (v : Fin d → ℝ)) h0) i
          simpa [Lattice.toEuc] using this
        positivity)]
      congr 3
      rw [hσ]; ring
  · have hwm : AEStronglyMeasurable (fun x => (WithLp.toLp 2 (fun j => h j x) : Euc d)) volume := by
      refine AEMeasurable.aestronglyMeasurable ?_
      exact (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.comp_aemeasurable
        (aemeasurable_pi_iff.2 fun j => (hmem j).aemeasurable)
    have hle : ∀ x, ‖(WithLp.toLp 2 (fun j => h j x) : Euc d)‖ ≤
        ‖(∑ j : Fin d, fun x => ‖h j x‖) x‖ := by
      intro x
      have h1 := Whole.cmxHLS_norm_toLp_le (d := d) (fun j => h j x)
      refine h1.trans (le_of_eq ?_)
      rw [Finset.sum_apply, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun j _ => norm_nonneg _)]
      simp [Real.norm_eq_abs]
    calc eLpNorm (fun x => (WithLp.toLp 2 (fun j => h j x) : Euc d)) q volume
        ≤ eLpNorm (∑ j : Fin d, fun x => ‖h j x‖) q volume := eLpNorm_mono hwm hle
      _ ≤ ∑ j : Fin d, eLpNorm (fun x => ‖h j x‖) q volume :=
          eLpNorm_sum_le (hp1.trans hpq).le
      _ ≤ ∑ _j : Fin d, ENNReal.ofReal Ch * ENNReal.ofReal F := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [eLpNorm_norm _ (hmem j).aestronglyMeasurable]
          exact (hhn j).trans (mul_le_mul' le_rfl (hfmem j))
      _ = ENNReal.ofReal (d * Ch * F) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hChpos.le,
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring

end HRS.Commutator.TorusNote
