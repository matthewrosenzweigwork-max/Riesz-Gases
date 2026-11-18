import HRS.MS.SA12C23

/-!
# S.A.12(c), packet E7.04 (part 8): the globally continuous remainder family

`κ^β(v,z) = D^βÃ(z) - χ̂(v-z) D^βB̃(z)` is jointly continuous and bounded; hence
`H^β(v,x) = ∫_W κ^β(v,z) f(x-z) dz` is jointly continuous in `(v,x)` (dominated convergence with a constant bound
on the finite-measure cell `W`).
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12C

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MH.AdjointRd.Phase2SA12Construction HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRd.Phase2SA12Near

variable {d : ℕ}

theorem sa12c_H_continuous {s L c0 : ℝ} (hL : 0 < L) {q χ χh γ : Euc d → ℝ} (hχ : IsCutoffPair χ χh)
    (hq : ContDiff ℝ ∞ q) (hγ : IsPeriodicRieszKernel d s L γ) {n : ℕ} (β : Fin n → Fin d)
    {f : Euc d → ℝ} (hf : Continuous f) {Bf : ℝ} (hfB : ∀ x, |f x| ≤ Bf) :
    Continuous (fun p : Euc d × Euc d =>
      ∫ z in sa12cWcell d L, sa12cKap s L c0 q χ χh γ β p.1 z * f (p.2 - z)) := by
  have hAs : ContDiff ℝ ∞ (sa12cA s L c0 q χ γ) := sa12cA_contDiff hL hq hχ hγ
  have hBs : ContDiff ℝ ∞ (sa12cB s L χ) := sa12cB_contDiff hL hχ
  have hAβ : Continuous (partialDeriv β (sa12cA s L c0 q χ γ)) := (sa12z3_pd_contDiff_inf hAs β).continuous
  have hBβ : Continuous (partialDeriv β (sa12cB s L χ)) := (sa12z3_pd_contDiff_inf hBs β).continuous
  obtain ⟨KA, hKA⟩ := hAβ.bounded_above_of_compact_support (sa12c_pd_compact (sa12cA_compact hL hχ) β)
  obtain ⟨KB, hKB⟩ := hBβ.bounded_above_of_compact_support (sa12c_pd_compact (sa12cB_compact hL hχ) β)
  have hχc : Continuous χh := hχ.2.1.continuous
  have hχ01 : ∀ x, |χh x| ≤ 1 := fun x => by
    have := hχ.2.2.2.2.1 x
    rw [abs_of_nonneg this.1]; exact this.2
  have hWfin := sa12c_W_fin (d := d) hL.le
  have hWm := sa12c_W_meas (d := d) L
  have hB0 : 0 ≤ Bf := (abs_nonneg _).trans (hfB 0)
  refine continuous_of_dominated (μ := volume.restrict (sa12cWcell d L))
    (bound := fun _ => (|KA| + |KB|) * Bf) ?_ ?_ ?_ ?_
  · intro p
    have : Continuous fun z => sa12cKap s L c0 q χ χh γ β p.1 z * f (p.2 - z) := by
      unfold sa12cKap
      exact (hAβ.sub ((hχc.comp (continuous_const.sub continuous_id)).mul hBβ)).mul
        (hf.comp (continuous_const.sub continuous_id))
    exact this.aestronglyMeasurable
  · intro p
    refine Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, abs_mul]
    unfold sa12cKap
    have h1 : |partialDeriv β (sa12cA s L c0 q χ γ) z - χh (p.1 - z) * partialDeriv β (sa12cB s L χ) z| ≤
        |KA| + |KB| := by
      refine (abs_sub _ _).trans ?_
      rw [abs_mul]
      have a1 : |partialDeriv β (sa12cA s L c0 q χ γ) z| ≤ |KA| := by
        have := hKA z; rw [Real.norm_eq_abs] at this; exact this.trans (le_abs_self _)
      have a2 : |χh (p.1 - z)| * |partialDeriv β (sa12cB s L χ) z| ≤ |KB| := by
        have := hKB z; rw [Real.norm_eq_abs] at this
        calc _ ≤ 1 * |partialDeriv β (sa12cB s L χ) z| :=
              mul_le_mul_of_nonneg_right (hχ01 _) (abs_nonneg _)
          _ ≤ |KB| := by rw [one_mul]; exact this.trans (le_abs_self _)
      linarith
    exact mul_le_mul h1 (hfB _) (abs_nonneg _) (by positivity)
  · exact integrableOn_const hWfin
  · refine Eventually.of_forall fun z => ?_
    unfold sa12cKap
    exact (continuous_const.sub ((hχc.comp (continuous_fst.sub continuous_const)).mul continuous_const)).mul
      (hf.comp (continuous_snd.sub continuous_const))

end HRS.MH.AdjointRd.Phase2SA12C
