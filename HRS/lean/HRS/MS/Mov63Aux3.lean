import HRS.MS.Mov63Aux2
import HRS.MS.MovForceTie

/-!
# S6.3, packet N1 (part 3): force bounds for `v ∈ Σ^m` (non-Schwartz)

Namespace `HRS.MS.Mov63`, helper prefix `mn_`.

* `mn_force_bound`: for a thermal equilibrium `ρ`, `j m : ℕ` with `d/2 + j + 2 < m`, there is `C` (independent of `v`) such that every
  CONTINUOUS `v ∈ Σ^m` (`MemOsc m v`) is `C^{j+2}` with `‖D^k v‖_∞ ≤ C ‖v‖_{Σ^m}` (`k ≤ j+2`) and the force `F = ∇g*(√ρ v)` is `C^{j+1}`,
  `div F + ⟨∇log ρ, F⟩ ∈ C_b^j`, `‖F‖_{C_b^{j+1}} + ‖div F + ⟨∇log ρ, F⟩‖_{C_b^j} ≤ C ‖v‖_{Σ^m}`.

The hypothesis `Continuous v` is not removable for free: `movForce` (the cancellation convention `ρ y - ρ x` near the diagonal) reads the pointwise
value `h x`, so it is not a.e.-invariant by definition; for the class `MovInSmallClass` (field `regular`) `v_t` is continuous.
Everything is stated with the `MemOsc` guard (`oscNorm` is junk off `MemOsc`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce

variable {d : ℕ}

/-- **`mn_force_bound`**: the force bounds of S6.1 (third assertion) for non-Schwartz `v ∈ Σ^m ∩ C^0`. -/
theorem mn_force_bound {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β q : ℝ)
    (hβ : 0 < β) (hq : 0 < q) (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ)
    (j m : ℕ) (hm : (d : ℝ) / 2 + j + 2 < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : Euc d → ℝ, Continuous v → MemOsc (m : ℝ) v →
      ContDiff ℝ ((j + 2 : ℕ) : WithTop ℕ∞) v ∧
      (∀ k ≤ j + 2, ∀ x : Euc d, ‖iteratedFDeriv ℝ k v x‖ ≤ C * oscNorm (m : ℝ) v) ∧
      ContDiff ℝ (j + 1) (movForce d s (fun x => Real.sqrt (ρ x) * v x)) ∧
      MemCb j (fun x => movDiv (movForce d s (fun y => Real.sqrt (ρ y) * v y)) x +
        inner ℝ (gradient (fun y => Real.log (ρ y)) x)
          (movForce d s (fun y => Real.sqrt (ρ y) * v y) x)) ∧
      cbNormVecE (j + 1) (movForce d s (fun x => Real.sqrt (ρ x) * v x)) +
        ENNReal.ofReal (cbNorm j (fun x => movDiv (movForce d s (fun y => Real.sqrt (ρ y) * v y)) x +
          inner ℝ (gradient (fun y => Real.log (ρ y)) x)
            (movForce d s (fun y => Real.sqrt (ρ y) * v y) x))) ≤
        ENNReal.ofReal (C * oscNorm (m : ℝ) v) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨B, -, hR, -⟩ := HRS.MS.Mov0.mv0_gapref hd hs0 hsd hq hβ hρ
  have hq' : 0 < β * q := mul_pos hβ hq
  obtain ⟨hψs, hgrad, c, hc, hψb⟩ := HRS.MS.Mov0.mv0_sqrt_gauss hq' hR
  obtain ⟨hdlog, M0, hM0⟩ := HRS.MS.Mov0.mv0_dlog_bounds hq'.le hR
  have hM00 : 0 ≤ M0 := by
    have := hM0 0
    simp only [norm_zero, mul_zero, zero_add] at this
    exact (norm_nonneg _).trans this
  have hfs : ContDiff ℝ ∞ (fun x => gradient (fun y => Real.log (ρ y)) x) := by
    have : (fun x => gradient (fun y => Real.log (ρ y)) x) = fun x => (-(β * q)) • x + B x :=
      funext hgrad
    rw [this]
    exact (contDiff_id.const_smul (-(β * q))).add (HRS.MS.Mov0.mov0_B_smooth hR)
  obtain ⟨C0, hC00, hC0⟩ := mov_operators_force_gen hd1 hs0 hsd hc hq'.le hM00 hψs hψb hfs hM0 hdlog j
  obtain ⟨Cs, hCs0, hCs⟩ := mn_sobolev_emb_gen (d := d) (j + 2) m
    (by push_cast; linarith)
  refine ⟨(C0 + 1) * Cs, mul_nonneg (by linarith) hCs0, fun v hvc hv => ?_⟩
  obtain ⟨g, hg, hfg, hb⟩ := hCs v hv
  have hvg : v = g := mn_ae_eq_cont hvc hg.continuous hfg
  subst hvg
  have hosc0 : 0 ≤ oscNorm (m : ℝ) v := Real.sqrt_nonneg _
  obtain ⟨h1, h2, h3⟩ := hC0 v (Cs * oscNorm (m : ℝ) v) (mul_nonneg hCs0 hosc0) hg hb
  have hle : Cs ≤ (C0 + 1) * Cs := by nlinarith
  refine ⟨hg, fun k hk x => ?_, by exact_mod_cast h1, h2, ?_⟩
  · calc ‖iteratedFDeriv ℝ k v x‖ ≤ Cs * oscNorm (m : ℝ) v := hb k hk x
      _ ≤ (C0 + 1) * Cs * oscNorm (m : ℝ) v := mul_le_mul_of_nonneg_right hle hosc0
  · rw [← mul_assoc] at h3
    refine h3.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (by nlinarith) hosc0

end HRS.MS.Mov63
