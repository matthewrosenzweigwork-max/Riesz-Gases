import HRS.MS.SA16Y4Ct12

/-!
# S.A.16 (SA16Y4) Ct13: the local component seminorms on `WmpSpace`

`sa16y4_loc k R₁ κ Y = ‖1_{B(0,R₁)} Y_κ‖_{L^p}`; it is `1`-Lipschitz (`sa16y4_loc_cont`), `≤ ‖Y‖`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Q Phase2SA16Evolution Phase2SA16Transfer

section Ct13
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

def sa16y4_loc (k : ℕ) (R₁ : ℝ) (κ : WIndex d k) (Y : WmpSpace d k p) : ℝ :=
  (eLpNorm ((Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R₁).indicator (sa16y4_comp k Y κ))
    (ENNReal.ofReal p) volume).toReal

lemma sa16y4_comp_sub (k : ℕ) (Y Y' : WmpSpace d k p) (κ : WIndex d k) :
    sa16y4_comp k (Y - Y') κ =ᵐ[volume] fun x => sa16y4_comp k Y κ x - sa16y4_comp k Y' κ x := by
  filter_upwards [Lp.coeFn_sub (Y : WLp d k p) (Y' : WLp d k p)] with x hx
  show ((((Y - Y' : WmpSpace d k p)) : WLp d k p) : EuclideanSpace ℝ (Fin d) → WIndex d k → ℝ) x κ = _
  rw [show (((Y - Y' : WmpSpace d k p)) : WLp d k p) = (Y : WLp d k p) - (Y' : WLp d k p) from rfl, hx]
  rfl

lemma sa16y4_loc_fin (k : ℕ) (R₁ : ℝ) (κ : WIndex d k) (Y : WmpSpace d k p) :
    eLpNorm ((Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R₁).indicator (sa16y4_comp k Y κ))
      (ENNReal.ofReal p) volume ≠ ⊤ :=
  ((sa16y4_comp_memLp k Y κ).indicator measurableSet_closedBall).eLpNorm_lt_top.ne

lemma sa16y4_loc_le_norm (k : ℕ) (R₁ : ℝ) (κ : WIndex d k) (Y : WmpSpace d k p) :
    sa16y4_loc k R₁ κ Y ≤ ‖Y‖ := by
  have hcoe : MemLp (((Y : WLp d k p)) : EuclideanSpace ℝ (Fin d) → (WIndex d k → ℝ)) (ENNReal.ofReal p) volume :=
    Lp.memLp (Y : WLp d k p)
  have hn : ‖Y‖ = (eLpNorm (((Y : WLp d k p)) : EuclideanSpace ℝ (Fin d) → (WIndex d k → ℝ))
      (ENNReal.ofReal p) volume).toReal := Lp.norm_def (Y : WLp d k p)
  rw [hn]
  refine ENNReal.toReal_mono hcoe.eLpNorm_lt_top.ne (eLpNorm_mono_ae ((sa16y4_comp_aesm k Y κ).indicator measurableSet_closedBall) (Eventually.of_forall fun x => ?_))
  by_cases hx : x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R₁
  · simp only [Set.indicator_of_mem hx]
    exact norm_le_pi_norm (((Y : WLp d k p) : EuclideanSpace ℝ (Fin d) → WIndex d k → ℝ) x) κ
  · simp [Set.indicator_of_notMem hx]

lemma sa16y4_loc_triangle (k : ℕ) (R₁ : ℝ) (κ : WIndex d k) (Y Y' : WmpSpace d k p) :
    sa16y4_loc k R₁ κ Y ≤ sa16y4_loc k R₁ κ Y' + sa16y4_loc k R₁ κ (Y - Y') := by
  have hp1 : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 (le_trans one_le_two (Fact.out : 2 ≤ p))
  set K := Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R₁
  have h1 : eLpNorm (K.indicator (sa16y4_comp k Y κ)) (ENNReal.ofReal p) volume ≤
      eLpNorm (K.indicator (sa16y4_comp k Y' κ)) (ENNReal.ofReal p) volume +
        eLpNorm (K.indicator (sa16y4_comp k (Y - Y') κ)) (ENNReal.ofReal p) volume := by
    have hsub := sa16y4_comp_sub k Y Y' κ
    have e : K.indicator (sa16y4_comp k Y κ) =ᵐ[volume]
        fun x => K.indicator (sa16y4_comp k Y' κ) x + K.indicator (sa16y4_comp k (Y - Y') κ) x := by
      filter_upwards [hsub] with x hx
      by_cases hxK : x ∈ K
      · simp only [Set.indicator_of_mem hxK, hx]; ring
      · simp [Set.indicator_of_notMem hxK]
    rw [eLpNorm_congr_ae e]
    exact eLpNorm_add_le (f := K.indicator (sa16y4_comp k Y' κ)) (g := K.indicator (sa16y4_comp k (Y - Y') κ)) hp1
  have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨sa16y4_loc_fin k R₁ κ Y', sa16y4_loc_fin k R₁ κ (Y - Y')⟩) h1
  rw [ENNReal.toReal_add (sa16y4_loc_fin k R₁ κ Y') (sa16y4_loc_fin k R₁ κ (Y - Y'))] at this
  exact this

lemma sa16y4_loc_cont (k : ℕ) (R₁ : ℝ) (κ : WIndex d k) : Continuous (sa16y4_loc (p := p) k R₁ κ) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun Y Y' => ?_).continuous
  rw [Real.dist_eq, NNReal.coe_one, one_mul, dist_eq_norm, abs_sub_le_iff]
  constructor
  · have := sa16y4_loc_triangle k R₁ κ Y Y'
    have h2 := sa16y4_loc_le_norm k R₁ κ (Y - Y')
    linarith
  · have := sa16y4_loc_triangle k R₁ κ Y' Y
    have h2 := sa16y4_loc_le_norm k R₁ κ (Y' - Y)
    rw [norm_sub_rev] at h2
    linarith
end Ct13

end HRS.Whole.AppendixA.Phase2SA16R
