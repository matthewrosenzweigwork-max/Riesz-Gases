import HRS.MS.SA16QMorrey3

/-!
# S.A.16 (SA16Y7) K1: Morrey's pointwise bound at scale `r`

`sa16y7_morrey_scaled`: for `p > 1`, `n ≥ 1`, `n p > d`, a smooth `v` satisfies, for all `x` and `r > 0`,
`‖v x‖ ≤ C ∑_{k ≤ n} r^{k - d/p} ‖D^k v‖_{L^p}` (dilation of `sa16q_morrey_key`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Q

open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

/-- `L^p` norm of a dilated, translated function. -/
lemma sa16y7_eLpNorm_dil {p : ℝ} (hp : 0 < p) (x : Euc d) {r : ℝ} (hr : 0 < r) {g : Euc d → ℝ}
    (hg : Continuous g) :
    eLpNorm (fun y => g (x + r • y)) (ENNReal.ofReal p) volume =
      ENNReal.ofReal (((r ^ d)⁻¹) ^ (1 / p)) * eLpNorm g (ENNReal.ofReal p) volume := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by simpa using hp
  have hpt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hgd : Continuous (fun y : Euc d => g (x + r • y)) :=
    hg.comp (continuous_const.add (continuous_const_smul r))
  rw [eLpNorm_eq_lintegral_rpow_enorm hp0 hpt hgd.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm hp0 hpt hg.aestronglyMeasurable, ENNReal.toReal_ofReal hp.le]
  have hmeas : Measurable (fun y : Euc d => ‖g y‖ₑ ^ p) :=
    (hg.measurable.enorm).pow_const p
  have := sa16q_scale (d := d) hr x hmeas
  have h1p : (0 : ℝ) ≤ 1 / p := by positivity
  rw [this, ENNReal.mul_rpow_of_nonneg _ _ h1p, ENNReal.ofReal_rpow_of_nonneg (by positivity) h1p]

theorem sa16y7_morrey_scaled (d : ℕ) (hd : 1 ≤ d) (p : ℝ) (hp : 1 < p) (n : ℕ) (hn : 1 ≤ n)
    (hnp : (d : ℝ) / p < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      (v : Euc d → F), ContDiff ℝ ∞ v → ∀ (x : Euc d) (r : ℝ), 0 < r →
      ‖v x‖ₑ ≤ ENNReal.ofReal C * ∑ k ∈ Finset.range (n + 1),
        ENNReal.ofReal (r ^ k * ((r ^ d)⁻¹) ^ (1 / p)) *
          eLpNorm (fun y => ‖iteratedFDeriv ℝ k v y‖) (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC, hK⟩ := sa16q_morrey_key d hd p hp n hn hnp
  refine ⟨C, hC, fun F _ _ _ v hv x r hr => ?_⟩
  have hp0 : 0 < p := by linarith
  set vr : Euc d → F := fun y => v (x + r • y) with hvr
  have hvrs : ContDiff ℝ ∞ vr := by
    have : ContDiff ℝ ∞ (fun y : Euc d => x + r • y) := contDiff_const.add (contDiff_const_smul r)
    exact hv.comp this
  have h0 := hK F vr hvrs 0
  have hv0 : vr 0 = v x := by simp [hvr]
  rw [hv0] at h0
  refine h0.trans ?_
  gcongr with k hk
  have hnorm : ∀ y, ‖iteratedFDeriv ℝ k vr y‖ = r ^ k * ‖iteratedFDeriv ℝ k v (x + r • y)‖ := by
    intro y
    have hw : ContDiff ℝ ∞ (fun z : Euc d => v (x + z)) := hv.comp (contDiff_const.add contDiff_id)
    have h1 : iteratedFDeriv ℝ k vr y = r ^ k • iteratedFDeriv ℝ k (fun z => v (x + z)) (r • y) :=
      by
        have := congrFun (iteratedFDeriv_comp_const_smul (𝕜 := ℝ) (i := k) (f := fun z : Euc d => v (x + z)) r
          (hw.of_le (by exact_mod_cast le_top))) y
        simpa [hvr] using this
    rw [h1, norm_smul, iteratedFDeriv_comp_add_left, Real.norm_of_nonneg (by positivity)]
  have hcont : Continuous (fun y => ‖iteratedFDeriv ℝ k v y‖) :=
    (hv.continuous_iteratedFDeriv (m := k) (by exact_mod_cast le_top)).norm
  have hfun : (fun y => ‖iteratedFDeriv ℝ k vr y‖) =
      fun y => r ^ k * (fun z => ‖iteratedFDeriv ℝ k v z‖) (x + r • y) := funext hnorm
  rw [hfun]
  have hsm : (fun y => r ^ k * (fun z => ‖iteratedFDeriv ℝ k v z‖) (x + r • y)) =
      (r ^ k) • (fun y => (fun z => ‖iteratedFDeriv ℝ k v z‖) (x + r • y)) := by
    funext y; simp
  rw [hsm, eLpNorm_const_smul, sa16y7_eLpNorm_dil hp0 x hr hcont]
  rw [Real.enorm_eq_ofReal (by positivity), ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]

end HRS.Whole.AppendixA.Phase2SA16Q
