import HRS.MS.SA16StrongSL3
import HRS.MS.SA16StrongApprox

/-!
# S.A.16 SL10 support: pointwise convergence and linearity of the cutoff operators

`sa16y_dct_conv`: dominated convergence for `∫ κ(z) w_n(x - z)`.
`sa16y_nlCut_tendsto`: if the coefficients `μ_n` and their first derivatives converge pointwise (and are uniformly
bounded), `nlCut δ μ_n u x → nlCut δ μ u x`.
`sa16y_nlCut_sub`: `nlCut` is linear in the coefficient (Schwartz coefficients).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16
open HRS HRS.Whole HRS.Whole.AppendixA

section SL10Aux
variable {d : ℕ}

lemma sa16y_oddCut_eq' {θ a : ℝ} (w : Euc d → ℝ) (i : Fin d) (x : Euc d) :
    oddCut d θ a i w x = ∫ z, sa16s_kr d θ a i z * w (x - z) := by
  have hS : MeasurableSet {z : Euc d | a < ‖z‖} := measurableSet_lt measurable_const measurable_norm
  unfold oddCut sa16s_kr
  simp_rw [sa16s_kernel_eq]
  rw [← integral_indicator hS]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [Set.indicator_mul_left]

lemma sa16y_dct_conv {κ : Euc d → ℝ} (hκ : Measurable κ) {Kb : ℝ} (hκb : ∀ z, |κ z| ≤ Kb)
    {H : Euc d → ℝ} (hH : Integrable H) {w : ℕ → Euc d → ℝ} (hwc : ∀ n, Continuous (w n))
    {w' : Euc d → ℝ} (hwb : ∀ n y, |w n y| ≤ H y)
    (hwl : ∀ y, Tendsto (fun n => w n y) atTop (𝓝 (w' y))) (x : Euc d) :
    Tendsto (fun n => ∫ z, κ z * w n (x - z)) atTop (𝓝 (∫ z, κ z * w' (x - z))) := by
  refine tendsto_integral_of_dominated_convergence (fun z => Kb * H (x - z)) (fun n => ?_)
    ((hH.comp_sub_left x).const_mul Kb) (fun n => Eventually.of_forall fun z => ?_)
    (Eventually.of_forall fun z => ?_)
  · exact hκ.aestronglyMeasurable.mul
      ((hwc n).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul (hκb z) (hwb n _) (abs_nonneg _) ((abs_nonneg _).trans (hκb z))
  · exact (hwl (x - z)).const_mul (κ z)

/-- coordinate derivatives are controlled by the derivative operator norm -/
lemma sa16y_pd_sub_le (f g : Euc d → ℝ) (x : Euc d) {j : ℕ} (r : Fin j → Fin d) :
    |partialDeriv r f x - partialDeriv r g x| ≤
      ‖iteratedFDeriv ℝ j f x - iteratedFDeriv ℝ j g x‖ := by
  have h := (iteratedFDeriv ℝ j f x - iteratedFDeriv ℝ j g x).le_opNorm
    (fun l => EuclideanSpace.single (r l) (1 : ℝ))
  simp only [PiLp.norm_single, norm_one, Finset.prod_const_one, mul_one] at h
  simpa [partialDeriv, Real.norm_eq_abs] using h

lemma sa16y_pd1_tendsto {f : ℕ → Euc d → ℝ} {g : Euc d → ℝ} {j : ℕ}
    (h : ∀ x, Tendsto (fun n => ‖iteratedFDeriv ℝ j (f n) x - iteratedFDeriv ℝ j g x‖) atTop (𝓝 0))
    (r : Fin j → Fin d) (x : Euc d) :
    Tendsto (fun n => partialDeriv r (f n) x) atTop (𝓝 (partialDeriv r g x)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) (h x)
  rw [Real.dist_eq]
  exact sa16y_pd_sub_le (f n) g x r

lemma sa16y_fracCut_eq_conv (hd : 1 ≤ d) {θ a : ℝ} (ha : 0 < a) (hθ : 0 < θ) (v : Euc d → ℝ)
    (hvc : Continuous v) {B : ℝ} (hvb : ∀ y, |v y| ≤ B) (x : Euc d) :
    fracCut d θ a v x = (∫ z, sa16y_kf d θ a z) * v x - sa16j_conv (sa16y_kf d θ a) v x := by
  rw [sa16y_fracCut_eq]
  have := congrFun (sa16y_E_eq (sa16y_kf_int hd ha hθ) hvc hvb) x
  simpa [sa16y_E] using this

lemma sa16y_kf_bound {θ a : ℝ} (ha : 0 < a) (hs : 0 ≤ (d : ℝ) + θ) (z : Euc d) :
    |sa16y_kf d θ a z| ≤ (a ^ ((d : ℝ) + θ))⁻¹ := by
  rw [abs_of_nonneg (sa16y_kf_nonneg θ a z)]
  unfold sa16y_kf
  by_cases hz : z ∈ {z : Euc d | a < ‖z‖}
  · rw [Set.indicator_of_mem hz]
    have hz' : a < ‖z‖ := hz
    exact inv_anti₀ (Real.rpow_pos_of_pos ha _) (Real.rpow_le_rpow ha.le hz'.le hs)
  · rw [Set.indicator_of_notMem hz]
    exact inv_nonneg.2 (Real.rpow_nonneg ha.le _)

lemma sa16y_pd1_continuous (u : 𝓢(Euc d, ℝ)) (j : Fin d) :
    Continuous (partialDeriv (fun _ : Fin 1 => j) (⇑u)) := by
  rw [sa16j_pd_schwartz u (fun _ : Fin 1 => j)]
  exact SchwartzMap.continuous _

lemma sa16y_nlCut_tendsto (hd : 1 ≤ d) {θ δ : ℝ} (hδ : 0 < δ) (hθ : 0 < θ) (lam c gamma : ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) (u : 𝓢(Euc d, ℝ)) (μ : Euc d → ℝ) (hμc : Continuous μ)
    (μs : ℕ → 𝓢(Euc d, ℝ)) {B1 : ℝ}
    (hb0 : ∀ n y, |μs n y| ≤ B1)
    (hb1 : ∀ n (j : Fin d) y, |partialDeriv (fun _ : Fin 1 => j) (⇑(μs n)) y| ≤ B1)
    (hl0 : ∀ y, Tendsto (fun n => μs n y) atTop (𝓝 (μ y)))
    (hl1 : ∀ (j : Fin d) y, Tendsto (fun n => partialDeriv (fun _ : Fin 1 => j) (⇑(μs n)) y) atTop
      (𝓝 (partialDeriv (fun _ : Fin 1 => j) μ y)))
    (x : Euc d) :
    Tendsto (fun n => nlCut d θ δ lam c gamma M (⇑(μs n)) u x) atTop
      (𝓝 (nlCut d θ δ lam c gamma M μ u x)) := by
  have hB10 : 0 ≤ B1 := (abs_nonneg _).trans (hb0 0 0)
  have hH : Integrable (fun y => B1 * |u y|) := (u.integrable.norm.const_mul B1).congr
    (Eventually.of_forall fun y => by simp [Real.norm_eq_abs])
  obtain ⟨Bu, hBu⟩ := sa16j_schwartz_bdd u
  have hs : 0 ≤ (d : ℝ) + θ := by positivity
  -- the fractional part
  have hfrac : Tendsto (fun n => fracCut d θ δ (fun y => μs n y * u y) x) atTop
      (𝓝 (fracCut d θ δ (fun y => μ y * u y) x)) := by
    have hvc : ∀ n, Continuous (fun y => μs n y * u y) := fun n => (μs n).continuous.mul u.continuous
    have hvb : ∀ n y, |μs n y * u y| ≤ B1 * Bu := fun n y => by
      rw [abs_mul]; exact mul_le_mul (hb0 n y) (hBu y) (abs_nonneg _) hB10
    have hvc' : Continuous (fun y => μ y * u y) := hμc.mul u.continuous
    have hvb' : ∀ y, |μ y * u y| ≤ B1 * Bu := fun y => by
      have h1 : |μ y| ≤ B1 := le_of_tendsto' ((hl0 y).abs) (fun n => hb0 n y)
      rw [abs_mul]; exact mul_le_mul h1 (hBu y) (abs_nonneg _) hB10
    have e1 : ∀ n, fracCut d θ δ (fun y => μs n y * u y) x =
        (∫ z, sa16y_kf d θ δ z) * (μs n x * u x) - ∫ z, sa16y_kf d θ δ z * (μs n (x - z) * u (x - z)) := by
      intro n
      rw [sa16y_fracCut_eq_conv hd hδ hθ _ (hvc n) (hvb n) x]
      rfl
    have e2 : fracCut d θ δ (fun y => μ y * u y) x =
        (∫ z, sa16y_kf d θ δ z) * (μ x * u x) - ∫ z, sa16y_kf d θ δ z * (μ (x - z) * u (x - z)) := by
      rw [sa16y_fracCut_eq_conv hd hδ hθ _ hvc' hvb' x]
      rfl
    simp_rw [e1, e2]
    refine Tendsto.sub (((hl0 x).mul_const (u x)).const_mul _) ?_
    exact sa16y_dct_conv (sa16y_kf_meas θ δ) (sa16y_kf_bound hδ hs) hH hvc
      (fun n y => by
        rw [abs_mul]
        exact mul_le_mul (hb0 n y) le_rfl (abs_nonneg _) hB10)
      (fun y => (hl0 y).mul_const (u y)) x
  -- the odd parts
  have hodd : ∀ (i j : Fin d), Tendsto (fun n => oddCut d θ δ i
      (fun y => partialDeriv (fun _ : Fin 1 => j) (⇑(μs n)) y * u y) x) atTop
      (𝓝 (oddCut d θ δ i (fun y => partialDeriv (fun _ : Fin 1 => j) μ y * u y) x)) := by
    intro i j
    simp_rw [sa16y_oddCut_eq']
    refine sa16y_dct_conv (sa16s_kr_meas θ δ i) (Kb := δ ^ (1 - ((d : ℝ) + θ)))
      (fun z => sa16s_kr_abs_le hd hδ hθ i z) hH
      (fun n => (sa16y_pd1_continuous (μs n) j).mul u.continuous)
      (fun n y => by
        show |partialDeriv (fun _ : Fin 1 => j) (⇑(μs n)) y * u y| ≤ B1 * |u y|
        rw [abs_mul]
        exact mul_le_mul (hb1 n j y) le_rfl (abs_nonneg _) hB10)
      (fun y => (hl1 j y).mul_const (u y)) x
  unfold nlCut
  refine Tendsto.add (hfrac.const_mul _) (Tendsto.const_mul _ ?_)
  refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
  exact (hodd i j).const_mul _

lemma sa16y_frac_int (hd : 1 ≤ d) {θ a : ℝ} (ha : 0 < a) (hθ : 0 < θ) (v : 𝓢(Euc d, ℝ)) (x : Euc d) :
    Integrable (fun z => sa16y_kf d θ a z * (v x - v (x - z))) := by
  obtain ⟨B, hB⟩ := sa16j_schwartz_bdd v
  have : ∀ z, sa16y_kf d θ a z * (v x - v (x - z)) =
      sa16y_kf d θ a z * v x - sa16y_kf d θ a z * v (x - z) := fun z => by ring
  simp_rw [this]
  exact ((sa16y_kf_int hd ha hθ).mul_const _).sub (sa16y_E_int (sa16y_kf_int hd ha hθ) v.continuous hB x)

lemma sa16y_fracCut_sub (hd : 1 ≤ d) {θ a : ℝ} (ha : 0 < a) (hθ : 0 < θ) (v w : 𝓢(Euc d, ℝ)) (x : Euc d) :
    fracCut d θ a (fun y => v y - w y) x = fracCut d θ a (⇑v) x - fracCut d θ a (⇑w) x := by
  rw [sa16y_fracCut_eq, sa16y_fracCut_eq, sa16y_fracCut_eq, ← integral_sub (sa16y_frac_int hd ha hθ v x)
    (sa16y_frac_int hd ha hθ w x)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  ring

lemma sa16y_oddCut_sub (hd : 1 ≤ d) {θ a : ℝ} (ha : 0 < a) (hθ : 0 < θ) (i : Fin d) (v w : 𝓢(Euc d, ℝ))
    (x : Euc d) :
    oddCut d θ a i (fun y => v y - w y) x = oddCut d θ a i (⇑v) x - oddCut d θ a i (⇑w) x := by
  rw [sa16y_oddCut_eq', sa16y_oddCut_eq', sa16y_oddCut_eq', ← integral_sub (sa16s_kr_int hd ha hθ i v x)
    (sa16s_kr_int hd ha hθ i w x)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  ring

lemma sa16y_pd_sub {f g : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {j : ℕ}
    (idx : Fin j → Fin d) :
    partialDeriv idx (fun y => f y - g y) = fun y => partialDeriv idx f y - partialDeriv idx g y := by
  funext x
  have hf' : ContDiffAt ℝ j f x := (hf.of_le (by exact_mod_cast le_top)).contDiffAt
  have hg' : ContDiffAt ℝ j g x := (hg.of_le (by exact_mod_cast le_top)).contDiffAt
  have h : (fun y => f y - g y) = f - g := rfl
  unfold partialDeriv
  rw [h, iteratedFDeriv_sub_apply hf' hg']
  rfl

lemma sa16y_nlCut_sub (hd : 1 ≤ d) {θ δ : ℝ} (hδ : 0 < δ) (hθ : 0 < θ) (lam c gamma : ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) (a b u : 𝓢(Euc d, ℝ)) (x : Euc d) :
    nlCut d θ δ lam c gamma M (⇑(a - b)) (⇑u) x =
      nlCut d θ δ lam c gamma M (⇑a) (⇑u) x - nlCut d θ δ lam c gamma M (⇑b) (⇑u) x := by
  have hab : ⇑(a - b) = fun y => a y - b y := by funext y; simp
  have hfr : fracCut d θ δ (fun y => (a - b) y * u y) x =
      fracCut d θ δ (fun y => a y * u y) x - fracCut d θ δ (fun y => b y * u y) x := by
    have := sa16y_fracCut_sub hd hδ hθ (sa16y_mulS a u) (sa16y_mulS b u) x
    rw [sa16y_mulS_apply, sa16y_mulS_apply] at this
    have e : (fun y => (a - b) y * u y) = fun y => a y * u y - b y * u y := by
      funext y; simp [sub_mul]
    rw [e]
    exact this
  have hod : ∀ i j : Fin d, oddCut d θ δ i
      (fun y => partialDeriv (fun _ : Fin 1 => j) (⇑(a - b)) y * u y) x =
      oddCut d θ δ i (fun y => partialDeriv (fun _ : Fin 1 => j) (⇑a) y * u y) x -
        oddCut d θ δ i (fun y => partialDeriv (fun _ : Fin 1 => j) (⇑b) y * u y) x := by
    intro i j
    have := sa16y_oddCut_sub hd hδ hθ i (sa16y_mulS (sa16y_dS a j) u) (sa16y_mulS (sa16y_dS b j) u) x
    rw [sa16y_mulS_apply, sa16y_mulS_apply, sa16y_dS_apply, sa16y_dS_apply] at this
    have ha' : ContDiff ℝ ∞ (⇑a) := a.smooth'
    have hb' : ContDiff ℝ ∞ (⇑b) := b.smooth'
    rw [hab, sa16y_pd_sub ha' hb']
    have e : (fun y => (partialDeriv (fun _ : Fin 1 => j) (⇑a) y -
        partialDeriv (fun _ : Fin 1 => j) (⇑b) y) * u y) =
        fun y => partialDeriv (fun _ : Fin 1 => j) (⇑a) y * u y -
          partialDeriv (fun _ : Fin 1 => j) (⇑b) y * u y := by
      funext y; ring
    rw [e]
    exact this
  unfold nlCut
  have hfr' : fracCut d θ δ (fun y => (⇑(a - b)) y * u y) x = _ := hfr
  rw [hfr']
  simp only [hod, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  ring

end SL10Aux

end HRS.Whole.AppendixA.Phase2SA16
