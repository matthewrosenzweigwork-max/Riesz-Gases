import HRS.MC.D3T3Aux3

/-!
# Packet D3T3, auxiliary facts: the large-scale part `H_λ(x) = ∫_λ^∞ κ(t)(Pφ_t(x) - ∫φ) dt`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal FourierTransform

namespace HRS.MC.D3T3

open HRS HRS.MC.FDLE HRS.MC.Per HRS.MC.D3T1

variable {d : ℕ}

/-- The large-scale part. -/
def Hs (ψ : Euc d → ℝ) (s b lam : ℝ) (x : Torus d) : ℝ :=
  ∫ t in Ioi lam, kap d s b t * (perJ ψ (x, t) - ∫ y, fdlPhi ψ y)

/-- The integrable majorant `b K t^{d-s-1-(2d+2)}`. -/
def hbd (d : ℕ) (s b K : ℝ) (t : ℝ) : ℝ :=
  b * K * t ^ ((d : ℝ) - s - 1 + (-(2 * ((d + 1 : ℕ) : ℝ))))

lemma d3f_hbd_integrableOn {s : ℝ} (hs0 : 0 ≤ s) (b K : ℝ) {lam : ℝ} (hlam : 0 < lam) :
    IntegrableOn (hbd d s b K) (Ioi lam) := by
  refine Integrable.const_mul (integrableOn_Ioi_rpow_of_lt ?_ hlam) _
  push_cast
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  linarith

lemma d3f_bound_pt (hd : 1 ≤ d) {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {s b K : ℝ} (hb : 0 ≤ b)
    (hK : ∀ t : ℝ, 0 < t → ∀ x : Torus d,
      |fdlPer (fdlPhiScale ψ t) x - ∫ y, fdlPhi ψ y| ≤ K * t ^ (-(2 * ((d + 1 : ℕ) : ℝ))))
    {t : ℝ} (ht : 0 < t) (x : Torus d) :
    |kap d s b t * (perJ ψ (x, t) - ∫ y, fdlPhi ψ y)| ≤ hbd d s b K t := by
  rw [d3f_perJ_eq hψ ht, abs_mul, abs_of_nonneg (d3f_kap_nonneg hb ht)]
  calc kap d s b t * |fdlPer (fdlPhiScale ψ t) x - ∫ y, fdlPhi ψ y|
      ≤ kap d s b t * (K * t ^ (-(2 * ((d + 1 : ℕ) : ℝ)))) :=
        mul_le_mul_of_nonneg_left (hK t ht x) (d3f_kap_nonneg hb ht)
    _ = b * K * (t ^ ((d : ℝ) - s) / t * t ^ (-(2 * ((d + 1 : ℕ) : ℝ)))) := by
        simp only [kap]; ring
    _ = hbd d s b K t := by rw [d3f_rpow_comb ht]; rfl

lemma d3f_int_b (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ)
    (k : Lattice d) {b lam : ℝ} (hb0 : 0 < b) (hlam : 0 < lam) :
    Integrable (fun p : Torus d × ℝ =>
      Torus.mode (-k) p.1 * ((kap d s b p.2 * (perJ ψ p - ∫ y, fdlPhi ψ y) : ℝ) : ℂ))
      ((volume : Measure (Torus d)).prod (volume.restrict (Ioi lam))) := by
  obtain ⟨K, hK0, hK⟩ := d3f_unif_bound hd hψ
  have hm := d3f_meas_f hψ k (kap d s b) (d3f_kap_measurable s b) (∫ y, fdlPhi ψ y)
  rw [integrable_prod_iff' hm.aestronglyMeasurable]
  refine ⟨?_, ?_⟩
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun t ht => ?_
    have ht0 : 0 < t := lt_trans hlam ht
    have hcont : Continuous (fun x : Torus d => Torus.mode (-k) x *
        ((kap d s b t * (perJ ψ (x, t) - ∫ y, fdlPhi ψ y) : ℝ) : ℂ)) := by
      have h' : ∀ x : Torus d, perJ ψ (x, t) = fdlPer (fdlPhiScale ψ t) x :=
        fun x => d3f_perJ_eq hψ ht0 x
      simp only [h']
      exact (Torus.continuous_mode _).mul (Complex.continuous_ofReal.comp
        (continuous_const.mul ((per_fdlPer_continuous hψ ht0).sub continuous_const)))
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · refine Integrable.mono' (d3f_hbd_integrableOn (d := d) hs0 b K hlam) ?_ ?_
    · exact (hm.norm.aestronglyMeasurable.prod_swap).integral_prod_right'
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun t ht => ?_
      have ht0 : 0 < t := lt_trans hlam ht
      have hcont : Continuous (fun x : Torus d => ‖Torus.mode (-k) x *
          ((kap d s b t * (perJ ψ (x, t) - ∫ y, fdlPhi ψ y) : ℝ) : ℂ)‖) := by
        have h' : ∀ x : Torus d, perJ ψ (x, t) = fdlPer (fdlPhiScale ψ t) x :=
          fun x => d3f_perJ_eq hψ ht0 x
        simp only [h']
        exact ((Torus.continuous_mode _).mul (Complex.continuous_ofReal.comp
          (continuous_const.mul ((per_fdlPer_continuous hψ ht0).sub continuous_const)))).norm
      have hint : Integrable (fun x : Torus d => ‖Torus.mode (-k) x *
          ((kap d s b t * (perJ ψ (x, t) - ∫ y, fdlPhi ψ y) : ℝ) : ℂ)‖) :=
        hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      have hnn : 0 ≤ ∫ x : Torus d, ‖Torus.mode (-k) x *
          ((kap d s b t * (perJ ψ (x, t) - ∫ y, fdlPhi ψ y) : ℝ) : ℂ)‖ :=
        integral_nonneg fun x => norm_nonneg _
      rw [Real.norm_of_nonneg hnn]
      calc ∫ x : Torus d, ‖Torus.mode (-k) x *
            ((kap d s b t * (perJ ψ (x, t) - ∫ y, fdlPhi ψ y) : ℝ) : ℂ)‖
          ≤ ∫ _ : Torus d, hbd d s b K t :=
            integral_mono hint (integrable_const _) fun x => by
              rw [d3f_norm_mode_mul]
              exact d3f_bound_pt hd hψ hb0.le hK ht0 x
        _ = hbd d s b K t := by simp

lemma d3f_Hs_continuous (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ)
    {b lam : ℝ} (hb0 : 0 < b) (hlam : 0 < lam) : Continuous (Hs ψ s b lam) := by
  obtain ⟨K, hK0, hK⟩ := d3f_unif_bound hd hψ
  unfold Hs
  refine continuous_of_dominated (bound := hbd d s b K) ?_ ?_ (d3f_hbd_integrableOn hs0 b K hlam) ?_
  · intro x
    exact ((d3f_kap_measurable s b).mul
      (((d3f_perJ_measurable hψ).comp (measurable_prodMk_left (x := x))).sub_const _)).aestronglyMeasurable
  · intro x
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun t ht => ?_
    rw [Real.norm_eq_abs]
    exact d3f_bound_pt hd hψ hb0.le hK (lt_trans hlam ht) x
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun t ht => ?_
    have ht0 : 0 < t := lt_trans hlam ht
    have h' : ∀ x : Torus d, perJ ψ (x, t) = fdlPer (fdlPhiScale ψ t) x :=
      fun x => d3f_perJ_eq hψ ht0 x
    simp only [h']
    exact continuous_const.mul ((per_fdlPer_continuous hψ ht0).sub continuous_const)

lemma d3f_nebot (hd : 1 ≤ d) : (𝓝[≠] (0 : Torus d)).NeBot := by
  set i0 : Fin d := ⟨0, hd⟩
  set u : ℕ → Torus d := fun n => Torus.mk (((1 : ℝ) / ((n : ℝ) + 2)) • EuclideanSpace.single i0 (1 : ℝ))
    with hu
  have hlim : Tendsto u atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((1 : ℝ) / ((n : ℝ) + 2))) atTop (𝓝 0) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp (tendsto_add_atTop_nat 2)
      simpa [Function.comp_def] using this
    have h2 : Tendsto (fun n : ℕ => ((1 : ℝ) / ((n : ℝ) + 2)) • EuclideanSpace.single i0 (1 : ℝ))
        atTop (𝓝 ((0 : ℝ) • EuclideanSpace.single i0 (1 : ℝ))) := h1.smul_const _
    rw [zero_smul] at h2
    have h3 := (Torus.continuous_mk (d := d)).continuousAt.tendsto.comp h2
    have h0 : Torus.mk (0 : Euc d) = 0 := by ext i; simp [Torus.mk]
    rw [h0] at h3
    exact h3
  have hne : ∀ n, u n ≠ 0 := by
    intro n h
    have h0 := congrFun h i0
    simp only [hu, Torus.mk] at h0
    rw [Pi.zero_apply] at h0
    simp only [PiLp.single_apply, ite_true, PiLp.smul_apply, smul_eq_mul, mul_one] at h0
    rw [AddCircle.coe_eq_zero_iff] at h0
    obtain ⟨m, hm⟩ := h0
    simp only [zsmul_eq_mul, mul_one] at hm
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    have hlt : 1 / ((n : ℝ) + 2) < 1 := by
      rw [div_lt_one (by positivity)]; linarith
    have h1 : (0 : ℝ) < m := by rw [hm]; exact hpos
    have h2 : (m : ℝ) < 1 := by rw [hm]; exact hlt
    have h3 : 0 < m := by exact_mod_cast h1
    have h4 : m < 1 := by exact_mod_cast h2
    omega
  have : Tendsto u atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hne⟩
  exact this.neBot

end HRS.MC.D3T3
