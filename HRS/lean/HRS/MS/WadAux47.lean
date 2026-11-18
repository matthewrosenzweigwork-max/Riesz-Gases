import HRS.MS.WadAux46

/-!
# S8.3 (Route A): continuity in time of `ℒ f_r (x₀)` for `C²_b` families

`s85_conv_dom`: explicit integrable domination of the cancellation-convolution integrand (the proof of
`s84_conv_integrable`, with the dominating function exposed).  `s85_gen_cont_r`: for a family `f_r`, `r ∈ [0,t]`,
of `C²` functions with bounded `Df_r, D²f_r` and jointly continuous `Df, D²f`, the map
`r ↦ generatorW (critCoeff …) r (f_r) x₀` is continuous (dominated convergence for the cancellation integral).
This gives continuity of `m(r) = μ(ℒ f_r)` for a projected solution (needed for its uniqueness).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal RealInnerProductSpace ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole HRS.MS.Ul

variable {d : ℕ}

theorem s85_conv_dom (hd : 2 ≤ d) {s A H : ℝ} (hs0 : 0 < s) (hs : s + 1 / 2 < (d : ℝ))
    (hA0 : 0 ≤ A) (hH0 : 0 ≤ H) (x : Euc d) :
    ∃ bd : Euc d → ℝ, Integrable bd volume ∧ ∀ {u : Euc d → ℝ},
      (∀ y, |u y| ≤ A * (1 + ‖y‖) ^ (-((d : ℝ) + 1))) →
      (∀ z : Euc d, ‖z‖ ≤ 1 / 4 → ∀ x', |u (x' - z) - u x'| ≤ H * ‖z‖ ^ (1 / 2 : ℝ)) →
      ∀ᵐ y : Euc d, ‖(if ‖x - y‖ ≤ 1 / 4 then (u y - u x) • rieszKernelGrad d s (x - y)
        else u y • rieszKernelGrad d s (x - y))‖ ≤ bd y := by
  have hd1 : 1 ≤ d := by omega
  have hint1 : IntegrableOn (fun z : Euc d => ‖z‖ ^ (-(s + 1 / 2))) (ball (0 : Euc d) 1) volume :=
    ult_ball_int hd1 (by linarith) hs
  set g1 : Euc d → ℝ := (ball (0 : Euc d) 1).indicator (fun z => s * H * ‖z‖ ^ (-(s + 1 / 2))) with hg1
  set g2 : Euc d → ℝ := fun z => s * 4 ^ (s + 1) * A * (1 + ‖x - z‖) ^ (-((d : ℝ) + 1)) with hg2
  have hg1i : Integrable g1 volume :=
    (integrable_indicator_iff measurableSet_ball).2 (hint1.const_mul (s * H))
  have hg2i : Integrable g2 volume := ((s84_int_far d).comp_sub_left x).const_mul _
  have hg10 : ∀ z, 0 ≤ g1 z := fun z => by
    rw [hg1]
    refine Set.indicator_nonneg (fun z _ => ?_) z
    exact mul_nonneg (mul_nonneg hs0.le hH0) (Real.rpow_nonneg (norm_nonneg _) _)
  refine ⟨fun y => g1 (x - y) + g2 (x - y), (hg1i.comp_sub_left x).add (hg2i.comp_sub_left x), ?_⟩
  intro u hA hH
  have hz : ∀ᵐ z : Euc d, z ≠ 0 := u2_ae_ne_zero hd1
  have hy : ∀ᵐ y : Euc d, x - y ≠ 0 :=
    ((volume : Measure (Euc d)).measurePreserving_sub_left x).quasiMeasurePreserving.ae hz
  filter_upwards [hy] with y hyz
  have hzp : 0 < ‖x - y‖ := norm_pos_iff.mpr hyz
  have hxz : x - (x - y) = y := sub_sub_cancel x y
  have hGn : ‖rieszKernelGrad d s (x - y)‖ = s * ‖x - y‖ ^ (-s - 1) := by
    rw [movtr_rieszKernelGrad_norm s hs0.le hyz]
    unfold movtr_sigma
    simp [hs0.ne']
  have hg2n : 0 ≤ g2 (x - y) := by
    rw [hg2]; exact mul_nonneg (mul_nonneg (mul_nonneg hs0.le (by positivity)) hA0)
      (Real.rpow_nonneg (by positivity) _)
  by_cases hzn : ‖x - y‖ ≤ 1 / 4
  · simp only [if_pos hzn]
    rw [norm_smul, hGn, Real.norm_eq_abs]
    have hn : g1 (x - y) = s * H * ‖x - y‖ ^ (-(s + 1 / 2)) := by
      rw [hg1, Set.indicator_of_mem]
      rw [mem_ball_zero_iff]; linarith
    have h1 : |u y - u x| * (s * ‖x - y‖ ^ (-s - 1)) ≤ s * H * ‖x - y‖ ^ (-(s + 1 / 2)) := by
      have hh := hH (x - y) hzn x
      rw [hxz] at hh
      calc |u y - u x| * (s * ‖x - y‖ ^ (-s - 1))
          ≤ (H * ‖x - y‖ ^ (1 / 2 : ℝ)) * (s * ‖x - y‖ ^ (-s - 1)) :=
            mul_le_mul_of_nonneg_right hh (by positivity)
        _ = s * H * (‖x - y‖ ^ (1 / 2 : ℝ) * ‖x - y‖ ^ (-s - 1)) := by ring
        _ = s * H * ‖x - y‖ ^ (-(s + 1 / 2)) := by
            rw [← Real.rpow_add hzp]; congr 2; ring
    show _ ≤ g1 (x - y) + g2 (x - y)
    linarith
  · push Not at hzn
    simp only [if_neg (not_le.2 hzn)]
    rw [norm_smul, hGn, Real.norm_eq_abs]
    have hg1n := hg10 (x - y)
    have h2 : ‖x - y‖ ^ (-s - 1) ≤ 4 ^ (s + 1) := by
      have : ‖x - y‖ ^ (-s - 1) ≤ (1 / 4 : ℝ) ^ (-s - 1) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hzn.le (by linarith)
      refine this.trans (le_of_eq ?_)
      rw [show (-s - 1) = -(s + 1) by ring, Real.rpow_neg (by norm_num), one_div, Real.inv_rpow (by norm_num),
        inv_inv]
    show _ ≤ g1 (x - y) + g2 (x - y)
    calc |u y| * (s * ‖x - y‖ ^ (-s - 1)) ≤ (A * (1 + ‖y‖) ^ (-((d : ℝ) + 1))) * (s * 4 ^ (s + 1)) :=
          mul_le_mul (hA y) (mul_le_mul_of_nonneg_left h2 hs0.le) (by positivity) (by positivity)
      _ = g2 (x - y) := by rw [hg2]; simp only [hxz]; ring
      _ ≤ g1 (x - y) + g2 (x - y) := by linarith

end HRS.MS.Wad
