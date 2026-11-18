/-
# HRS.Equilibrium.Q84bAuxL — packet Q84b: differentiating the canonical row under the integral
-/
import HRS.Equilibrium.Q84bAuxK

open MeasureTheory Filter Topology

noncomputable section

namespace HRS.Q84b

variable {d : ℕ} {s : ℝ}

theorem q84b_xt_dist (x : Torus d) (v : Euc d) (t : ℝ) :
    Torus.eucDist x (Torus.mk (Torus.rep x + t • v)) ≤ |t| * ‖v‖ := by
  have := Q84a.q84a_eucDist_mk_le (Torus.rep x) (Torus.rep x + t • v)
  rw [Torus.mk_rep] at this
  refine this.trans (le_of_eq ?_)
  rw [sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs]

theorem q84b_far_lim (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {ρ : Torus d → ℝ} {Bρ : ℝ}
    (hBρ0 : 0 ≤ Bρ) (hBρ : ∀ x, |ρ x| ≤ Bρ) (hρm : Measurable ρ) {K : ℝ}
    {ψ : Torus d → Torus d → ℝ} (hPs : PsiSize s K ψ) (hmeas : Measurable (Function.uncurry ψ))
    (x : Torus d) (v : Euc d) (hv : 0 < ‖v‖) :
    Tendsto (fun t : ℝ => ∫ z in {z : Torus d | 2 * (|t| * ‖v‖) ≤ Torus.eucDist x z},
        ρ z * (t⁻¹ * (ψ (Torus.mk (Torus.rep x + t • v)) z - ψ x z))) (𝓝[≠] 0)
      (𝓝 (∫ z, ρ z * inner ℝ v (gradFst ψ x z))) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs1 : 1 ≤ s := by rw [hcrit]; linarith
  have hs0 : 0 < s := by linarith
  have hd0 : 0 < d := by omega
  set far : ℝ → Set (Torus d) := fun t => {z : Torus d | 2 * (|t| * ‖v‖) ≤ Torus.eucDist x z}
    with hfar
  have hfarm : ∀ t, MeasurableSet (far t) := fun t =>
    measurableSet_le measurable_const (PairCorrAux.measurable_eucDist' x)
  have hm1 : ∀ y : Torus d, Measurable (fun z => ψ y z) := fun y =>
    hmeas.comp (measurable_const.prodMk measurable_id)
  have e : (fun t : ℝ => ∫ z in far t, ρ z * (t⁻¹ * (ψ (Torus.mk (Torus.rep x + t • v)) z - ψ x z))) =
      fun t : ℝ => ∫ z, (far t).indicator (fun z => ρ z * (t⁻¹ *
        (ψ (Torus.mk (Torus.rep x + t • v)) z - ψ x z))) z :=
    funext fun t => (integral_indicator (hfarm t)).symm
  show Tendsto (fun t : ℝ => ∫ z in far t, ρ z * (t⁻¹ * (ψ (Torus.mk (Torus.rep x + t • v)) z - ψ x z)))
    (𝓝[≠] 0) _
  rw [e]
  have hwi := q84b_w_integrable hd hcrit x
  refine tendsto_integral_filter_of_dominated_convergence
    (fun z => Bρ * (|K| * 2 ^ s * ‖v‖) * wEnv s x z) ?_ ?_ (hwi.const_mul _) ?_
  · refine Eventually.of_forall fun t => ?_
    refine Measurable.aestronglyMeasurable ?_
    exact (hρm.mul (measurable_const.mul ((hm1 _).sub (hm1 x)))).indicator (hfarm t)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := ht
    refine Eventually.of_forall fun z => ?_
    by_cases hz : z ∈ far t
    · rw [Set.indicator_of_mem hz]
      have hz' : 2 * (|t| * ‖v‖) ≤ Torus.eucDist x z := hz
      have hεpos : 0 < |t| * ‖v‖ := mul_pos (abs_pos.2 ht0) hv
      have hxz : x ≠ z := by
        intro h; rw [h, PairCorrAux.eucDist_self'] at hz'; linarith
      have hdist := q84b_xt_dist x v t
      have hmv := q84b_fun_diff hPs hs1 (b := Torus.mk (Torus.rep x + t • v)) hxz
        (by linarith)
      have hwz : 1 ≤ wEnv s x z := PairCorrAux.one_le_wEnv s x z
      have hX : 0 ≤ rTrunc x z ^ (-s) := Real.rpow_nonneg (PairCorrAux.rTrunc_nonneg x z) _
      have h2s : 1 ≤ (2 : ℝ) ^ s := Real.one_le_rpow (by norm_num) hs0.le
      have hA : 0 ≤ 1 + 2 ^ s * rTrunc x z ^ (-s) := by positivity
      have hK : K ≤ |K| := le_abs_self K
      have hKA : K * (1 + 2 ^ s * rTrunc x z ^ (-s)) ≤ |K| * 2 ^ s * wEnv s x z := by
        have : 1 + 2 ^ s * rTrunc x z ^ (-s) ≤ 2 ^ s * wEnv s x z := by
          unfold wEnv; nlinarith
        calc K * (1 + 2 ^ s * rTrunc x z ^ (-s)) ≤ |K| * (1 + 2 ^ s * rTrunc x z ^ (-s)) :=
              mul_le_mul_of_nonneg_right hK hA
          _ ≤ |K| * (2 ^ s * wEnv s x z) := mul_le_mul_of_nonneg_left this (abs_nonneg K)
          _ = _ := by ring
      have hK0 : 0 ≤ K := Q84a.q84a_K_nonneg hPs hxz
      have h1 : |ψ (Torus.mk (Torus.rep x + t • v)) z - ψ x z| ≤
          K * (1 + 2 ^ s * rTrunc x z ^ (-s)) * (|t| * ‖v‖) := by
        rw [abs_sub_comm]
        exact hmv.trans (mul_le_mul_of_nonneg_left hdist (mul_nonneg hK0 hA))
      have hq : |t⁻¹ * (ψ (Torus.mk (Torus.rep x + t • v)) z - ψ x z)| ≤
          |K| * 2 ^ s * wEnv s x z * ‖v‖ := by
        calc |t⁻¹ * (ψ (Torus.mk (Torus.rep x + t • v)) z - ψ x z)|
            = |t|⁻¹ * |ψ (Torus.mk (Torus.rep x + t • v)) z - ψ x z| := by rw [abs_mul, abs_inv]
          _ ≤ |t|⁻¹ * (K * (1 + 2 ^ s * rTrunc x z ^ (-s)) * (|t| * ‖v‖)) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = K * (1 + 2 ^ s * rTrunc x z ^ (-s)) * ‖v‖ := by
              have : |t| ≠ 0 := abs_ne_zero.2 ht0
              field_simp
          _ ≤ |K| * 2 ^ s * wEnv s x z * ‖v‖ := mul_le_mul_of_nonneg_right hKA (norm_nonneg v)
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      calc |ρ z| * |t⁻¹ * (ψ (Torus.mk (Torus.rep x + t • v)) z - ψ x z)|
          ≤ Bρ * (|K| * 2 ^ s * wEnv s x z * ‖v‖) :=
            mul_le_mul (hBρ z) hq (abs_nonneg _) hBρ0
        _ = _ := by ring
    · rw [Set.indicator_of_notMem hz]
      simp only [norm_zero]
      have := PairCorrAux.one_le_wEnv s x z
      positivity
  · filter_upwards [q84b_ae_ne hd0 x] with z hz
    have hxz : x ≠ z := fun h => hz h.symm
    have hlim := (q84b_slope_tendsto hPs hxz v).const_mul (ρ z)
    refine hlim.congr' ?_
    have hdpos : 0 < Torus.eucDist x z := by
      rcases (PairCorrAux.eucDist_nonneg' x z).lt_or_eq with h0 | h0
      · exact h0
      · exact absurd ((PairCorrAux.eucDist_eq_zero' x z).1 h0.symm) hxz
    set δ : ℝ := Torus.eucDist x z / (2 * ‖v‖) with hδ
    have hδ0 : 0 < δ := by positivity
    have hev : ∀ᶠ t : ℝ in 𝓝 0, |t| < δ := by
      have h := (continuous_abs (G := ℝ)).tendsto (0 : ℝ)
      rw [abs_zero] at h
      exact h.eventually (gt_mem_nhds hδ0)
    filter_upwards [hev.filter_mono (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ)))] with t ht
    have hzf : z ∈ far t := by
      show 2 * (|t| * ‖v‖) ≤ Torus.eucDist x z
      have : |t| * ‖v‖ ≤ δ * ‖v‖ := mul_le_mul_of_nonneg_right ht.le hv.le
      have h2 : δ * ‖v‖ = Torus.eucDist x z / 2 := by
        rw [hδ]; field_simp
      linarith
    rw [Set.indicator_of_mem hzf]


theorem q84b_near_lim (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {ρ : Torus d → ℝ} {Bρ : ℝ}
    (hBρ0 : 0 ≤ Bρ) (hBρ : ∀ x, |ρ x| ≤ Bρ) (hρm : Measurable ρ) {K : ℝ}
    {ψ : Torus d → Torus d → ℝ} (hPs : PsiSize s K ψ) (hmeas : Measurable (Function.uncurry ψ))
    (x : Torus d) (v : Euc d) (hv : 0 < ‖v‖) :
    Tendsto (fun t : ℝ => ∫ z in {z : Torus d | Torus.eucDist x z < 2 * (|t| * ‖v‖)},
        ρ z * (t⁻¹ * (ψ (Torus.mk (Torus.rep x + t • v)) z - ψ x z))) (𝓝[≠] 0) (𝓝 0) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by rw [hcrit]; linarith
  set C₁ : ℝ := PairCorrAux.cdR d * (1 / d + 1 / s) with hC₁
  set M : ℝ := Bρ * (2 * (4 * |K| * (3 * ‖v‖) * C₁ * (3 * ‖v‖) ^ s)) with hM
  have hpow : Tendsto (fun t : ℝ => M * |t| ^ s) (𝓝[≠] 0) (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => |t| ^ s) (𝓝 (0 : ℝ)) (𝓝 0) := by
      have habs := (continuous_abs (G := ℝ)).tendsto (0 : ℝ)
      rw [abs_zero] at habs
      have := ((Real.continuousAt_rpow_const (0 : ℝ) s (Or.inr hs0.le)).tendsto).comp habs
      rw [Real.zero_rpow hs0.ne'] at this
      exact this
    have := (h1.mono_left (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ)))).const_mul M
    simpa using this
  refine squeeze_zero_norm' ?_ hpow
  have hev : ∀ᶠ t : ℝ in 𝓝 0, |t| < 1 / (3 * ‖v‖) := by
    have h := (continuous_abs (G := ℝ)).tendsto (0 : ℝ)
    rw [abs_zero] at h
    exact h.eventually (gt_mem_nhds (by positivity))
  filter_upwards [self_mem_nhdsWithin, hev.filter_mono (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ)))]
    with t ht0 ht
  have ht0' : t ≠ 0 := ht0
  have hε0 : 0 < |t| * ‖v‖ := mul_pos (abs_pos.2 ht0') hv
  have h3 : 3 * (|t| * ‖v‖) ≤ 1 := by
    have : |t| * (3 * ‖v‖) ≤ 1 / (3 * ‖v‖) * (3 * ‖v‖) :=
      mul_le_mul_of_nonneg_right ht.le (by positivity)
    rw [one_div, inv_mul_cancel₀ (by positivity)] at this
    linarith
  have hnp := q84b_near_part hd hcrit hBρ0 hBρ hρm hPs hmeas x (Torus.mk (Torus.rep x + t • v))
    hε0 h3 (q84b_xt_dist x v t) ht0'
  refine hnp.trans (le_of_eq ?_)
  have hab : |t| ≠ 0 := abs_ne_zero.2 ht0'
  have e1 : (3 * (|t| * ‖v‖)) ^ s = (3 * ‖v‖) ^ s * |t| ^ s := by
    rw [show 3 * (|t| * ‖v‖) = (3 * ‖v‖) * |t| by ring, Real.mul_rpow (by positivity) (abs_nonneg t)]
  rw [e1]
  simp only [hM, hC₁]
  field_simp


/-- Differentiating the canonical row under the integral sign: `∫ ρ(z) ∇_xψ(x,z) dz = 0`. -/
theorem q84b_grad_slice_mean (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {ρ : Torus d → ℝ}
    (hρ1 : Torus.IsCk 1 ρ) {K : ℝ} {ψ : Torus d → Torus d → ℝ} (hPs : PsiSize s K ψ)
    (hmeas : Measurable (Function.uncurry ψ))
    (hcan : ∀ x, Integrable (fun z => ρ z * ψ x z) ∧ ∫ z, ρ z * ψ x z = 0)
    (x : Torus d) (v : Euc d) :
    ∫ z, ρ z * inner ℝ v (gradFst ψ x z) = 0 := by
  by_cases hv0 : v = 0
  · simp [hv0]
  have hv : 0 < ‖v‖ := norm_pos_iff.2 hv0
  obtain ⟨Bρ, hBρ0, hBρ⟩ := HRS.KernelGrad.isCk_bounded hρ1
  have hρm : Measurable ρ := (HRS.PDE.MFAux.continuous_of_isCk hρ1).measurable
  have hzero : ∀ t : ℝ, ∫ z, ρ z * (t⁻¹ * (ψ (Torus.mk (Torus.rep x + t • v)) z - ψ x z)) = 0 := by
    intro t
    have hi1 := (hcan (Torus.mk (Torus.rep x + t • v))).1
    have hi0 := (hcan x).1
    have e : ∀ z, ρ z * (t⁻¹ * (ψ (Torus.mk (Torus.rep x + t • v)) z - ψ x z)) =
        t⁻¹ * (ρ z * ψ (Torus.mk (Torus.rep x + t • v)) z - ρ z * ψ x z) := fun z => by ring
    simp_rw [e]
    rw [integral_const_mul, integral_sub hi1 hi0, (hcan (Torus.mk (Torus.rep x + t • v))).2,
      (hcan x).2]
    simp
  have hint : ∀ t : ℝ, Integrable (fun z => ρ z * (t⁻¹ * (ψ (Torus.mk (Torus.rep x + t • v)) z -
      ψ x z))) := by
    intro t
    have hi1 := (hcan (Torus.mk (Torus.rep x + t • v))).1
    have hi0 := (hcan x).1
    have := (hi1.sub hi0).const_mul t⁻¹
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only [Pi.sub_apply]; ring
  set far : ℝ → Set (Torus d) := fun t => {z : Torus d | 2 * (|t| * ‖v‖) ≤ Torus.eucDist x z}
    with hfar
  have hfarm : ∀ t, MeasurableSet (far t) := fun t =>
    measurableSet_le measurable_const (PairCorrAux.measurable_eucDist' x)
  have hcompl : ∀ t : ℝ, (far t)ᶜ = {z : Torus d | Torus.eucDist x z < 2 * (|t| * ‖v‖)} := by
    intro t; ext z; simp [hfar, not_le]
  have hsplit : ∀ t : ℝ, (∫ z in far t, ρ z * (t⁻¹ * (ψ (Torus.mk (Torus.rep x + t • v)) z - ψ x z))) +
      ∫ z in {z : Torus d | Torus.eucDist x z < 2 * (|t| * ‖v‖)},
        ρ z * (t⁻¹ * (ψ (Torus.mk (Torus.rep x + t • v)) z - ψ x z)) = 0 := by
    intro t
    rw [← hcompl t, integral_add_compl (hfarm t) (hint t), hzero t]
  have hfar_lim := q84b_far_lim hd hcrit hBρ0 hBρ hρm hPs hmeas x v hv
  have hnear_lim := q84b_near_lim hd hcrit hBρ0 hBρ hρm hPs hmeas x v hv
  have h2 : Tendsto (fun t : ℝ => ∫ z in far t, ρ z * (t⁻¹ * (ψ (Torus.mk (Torus.rep x + t • v)) z -
      ψ x z))) (𝓝[≠] 0) (𝓝 0) := by
    have := hnear_lim.neg
    rw [neg_zero] at this
    refine this.congr fun t => ?_
    have := hsplit t
    linarith
  exact tendsto_nhds_unique hfar_lim h2

end HRS.Q84b
