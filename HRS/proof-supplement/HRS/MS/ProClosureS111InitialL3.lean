import HRS.MS.R26T6CI18
import HRS.MS.ProClosureS111InitialFTCBase

/-! Endpoint continuity and Bochner FTC for dominated L³ curves. -/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.MS.ProClosureS111

open HRS.MS.R26T6C
local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

theorem L3_continuousWithinAt_of_dominated
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (w : ℝ → X → ℝ) (G : X → ℝ) (a b r : ℝ)
    (hr : r ∈ Icc a b)
    (hw : ∀ q ∈ Icc a b, MemLp (w q) 3 mu)
    (hcont : ∀ x, ContinuousOn (fun q => w q x) (Icc a b))
    (hbd : ∀ q ∈ Icc a b, ∀ x, |w q x| ≤ G x)
    (hG : MemLp G 3 mu) :
    ContinuousWithinAt (fun q => r26t6c_toLp3 mu (w q)) (Icc a b) r := by
  unfold ContinuousWithinAt
  rw [tendsto_iff_norm_sub_tendsto_zero]
  let l : Filter ℝ := 𝓝[Icc a b] r
  have hev : ∀ᶠ q in l, q ∈ Icc a b := self_mem_nhdsWithin
  let Fn : ℝ → X → ℝ := fun q x => |w q x - w r x| ^ 3
  have hnorm : ∀ᶠ q in l,
      ‖r26t6c_toLp3 mu (w q) - r26t6c_toLp3 mu (w r)‖ ^ 3 =
        ∫ x, Fn q x ∂mu := by
    filter_upwards [hev] with q hq
    have e1 := r26t6c_toLp3_ae (hw q hq)
    have e2 := r26t6c_toLp3_ae (hw r hr)
    rw [r26t6c_Lp_norm_cube mu]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (r26t6c_toLp3 mu (w q))
      (r26t6c_toLp3 mu (w r)), e1, e2] with x h1 h2 h3
    simp only [h1, Pi.sub_apply, h2, h3, Fn]
  have hG3 : Integrable (fun x => (2 * |G x|) ^ 3) mu := by
    have hi := (hG.integrable_norm_pow (by norm_num : (3 : ℕ) ≠ 0)).const_mul 8
    refine hi.congr (ae_of_all _ fun x => ?_)
    simp only [Real.norm_eq_abs]
    ring
  have hint := tendsto_integral_filter_of_dominated_convergence
    (μ := mu) (l := l) (F := Fn) (f := fun _ => (0 : ℝ))
    (fun x => (2 * |G x|) ^ 3) ?_ ?_ hG3 ?_
  · have h0 : Tendsto (fun q => ∫ x, Fn q x ∂mu) l (𝓝 0) := by
      simpa using hint
    have hcubed : Tendsto (fun q =>
        ‖r26t6c_toLp3 mu (w q) - r26t6c_toLp3 mu (w r)‖ ^ 3) l (𝓝 0) :=
      (tendsto_congr' hnorm).2 h0
    have hroot := (Real.continuous_rpow_const
      (by norm_num : (0 : ℝ) ≤ 1 / 3)).tendsto (0 : ℝ) |>.comp hcubed
    have hroot0 : Tendsto (fun q =>
        (‖r26t6c_toLp3 mu (w q) - r26t6c_toLp3 mu (w r)‖ ^ 3) ^
          (1 / 3 : ℝ)) l (𝓝 0) := by
      simpa [Function.comp_def] using hroot
    convert hroot0 using 1
    ext q
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  · filter_upwards [hev] with q hq
    have hm := ((hw q hq).aestronglyMeasurable.sub
      (hw r hr).aestronglyMeasurable).norm.pow 3
    have hpow : ((fun x : X => ‖(w q - w r) x‖) ^ (3 : ℕ)) =
        (fun x : X => ‖(w q - w r) x‖ ^ 3) := by
      funext x
      rfl
    rw [hpow] at hm
    simpa [Fn, Real.norm_eq_abs] using hm
  · filter_upwards [hev] with q hq
    refine ae_of_all _ fun x => ?_
    have h3 : |w q x - w r x| ≤ 2 * |G x| := by
      calc
        _ ≤ |w q x| + |w r x| := abs_sub _ _
        _ ≤ G x + G x := add_le_add (hbd q hq x) (hbd r hr x)
        _ ≤ 2 * |G x| := by linarith [le_abs_self (G x)]
    change |(|w q x - w r x| ^ 3)| ≤ (2 * |G x|) ^ 3
    rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) 3)]
    exact pow_le_pow_left₀ (abs_nonneg _) h3 3
  · refine ae_of_all _ fun x => ?_
    have hh := (((hcont x r hr).tendsto.sub_const (w r x)).abs).pow 3
    simpa [Fn] using hh

theorem L3_FTC_of_pointwise
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (w w' : ℝ → X → ℝ) (G : X → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hw : ∀ q ∈ Icc (0 : ℝ) T, MemLp (w q) 3 mu)
    (hw' : ∀ q ∈ Icc (0 : ℝ) T, MemLp (w' q) 3 mu)
    (hG : MemLp G 3 mu)
    (hcont : ∀ x, ContinuousOn (fun q => w q x) (Icc (0 : ℝ) T))
    (hder : ∀ x q, q ∈ Ioo (0 : ℝ) T →
      HasDerivAt (fun t => w t x) (w' q x) q)
    (hbd : ∀ q ∈ Icc (0 : ℝ) T, ∀ x, |w q x| ≤ G x ∧ |w' q x| ≤ G x) :
    let F := fun t => r26t6c_toLp3 mu (w t)
    let D := fun t => r26t6c_toLp3 mu (w' t)
    StronglyMeasurable (fun t : Icc (0 : ℝ) T => D t) ∧
      IntegrableOn D (Icc (0 : ℝ) T) ∧
      ∀ t ∈ Icc (0 : ℝ) T, F t = F 0 + ∫ v in Icc (0 : ℝ) t, D v := by
  dsimp
  refine bounded_derivative_Icc_FTC (E := Lp ℝ 3 mu)
    (F := fun t => r26t6c_toLp3 mu (w t))
    (G := fun t => r26t6c_toLp3 mu (w' t)) T hT ?_ ?_
    ‖r26t6c_toLp3 mu G‖ ?_
  · intro t ht
    exact L3_continuousWithinAt_of_dominated mu w G 0 T t ht hw hcont
      (fun q hq x => (hbd q hq x).1) hG
  · intro t ht
    exact r26t6c_L3_hasDerivAt mu w w' G 0 T t ht
      (fun q hq => hw q ⟨hq.1.le, hq.2.le⟩)
      (hw' t ⟨ht.1.le, ht.2.le⟩) hG hder
      (fun q hq x => (hbd q ⟨hq.1.le, hq.2.le⟩ x).2)
  · intro t ht
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [r26t6c_toLp3_ae (hw' t ht), r26t6c_toLp3_ae hG] with x h1 h2
    rw [h1, h2, Real.norm_eq_abs, Real.norm_eq_abs]
    exact (hbd t ht x).2.trans (le_abs_self _)

end HRS.MS.ProClosureS111
