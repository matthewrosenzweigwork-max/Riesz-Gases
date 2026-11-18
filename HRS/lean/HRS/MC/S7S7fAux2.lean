import HRS.MC.S7S7fAux1

/-!
# Packet S7f, helper 2: the covariance of `G` along the modes and the Gaussian contraction expansion

For `G` as in `static_field`: `E[G_k G_l] = s7_Cmode r ρ a k l` (the response is the mode datum `a_l`), the weights
`|C_{kl}| ≤ C b_k b_l`, and for every continuous bilinear form `T` on `E_r`
`E T(G, G) = ∑_k ∑_l C_{kl} T(ε_k, ε_l)` (finite truncations `truncE K`, dominated convergence).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7f

open HRS HRS.Sec7 HRS.MC.SEdge HRS.StaticLimitAux HRS.MC.Sec7.S7d HRS.MC.Sec7.S7c

variable {d : ℕ} {s : ℝ} {r : ℝ}

theorem s7f_phi_bound (hr : r = 2 * (d : ℝ) + 6) (k : NonzeroLattice d) (x : Torus d) :
    |s7_phi r k x| ≤ Real.sqrt 2 * s7_b k := by
  have hjp := Torus.jp_pos k.1
  have h1 : Lattice.jp k.1 ^ (-r) ≤ s7_b k :=
    (Real.rpow_le_rpow_of_exponent_le (Torus.jp_ge_one _) (by linarith)).trans
      (s7c_jp_exp_le hr k)
  have h2 : s7_phi r k x = Lattice.jp k.1 ^ (-r) * Torus.realMode k x := rfl
  rw [h2, abs_mul, abs_of_nonneg (Real.rpow_nonneg hjp.le _), mul_comm]
  exact mul_le_mul (Torus.abs_realMode_le k x) h1 (Real.rpow_nonneg hjp.le _) (Real.sqrt_nonneg _)

theorem s7f_b_nonneg (k : NonzeroLattice d) : 0 ≤ s7_b k := (s7d_b_pos k).le

theorem s7f_abs_integral_le {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {f : X → ℝ} {C : ℝ} (h : ∀ x, |f x| ≤ C) : |∫ x, f x ∂μ| ≤ C := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := C)
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact h x)
  simpa using this

theorem s7f_cmode_bound (hr : r = 2 * (d : ℝ) + 6) {γ : ℝ} {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ)
    {a : NonzeroLattice d → Torus d → ℝ} {v : NonzeroLattice d → Fin d → Torus d → ℝ} {C₀ : ℝ}
    (hmode : s7_ModeData d s γ ρ r a v C₀) :
    ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ k l, |s7_Cmode r ρ a k l| ≤ Cc * (s7_b k * s7_b l) := by
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  obtain ⟨C₀', Cd, hC0, hCd, ha, -, -⟩ := s7d_mode_bounds hr hmode
  refine ⟨Real.sqrt 2 * C₀', by positivity, fun k l => ?_⟩
  unfold s7_Cmode
  refine s7f_abs_integral_le _ (fun x => ?_)
  rw [abs_mul]
  calc |s7_phi r k x| * |a l x| ≤ (Real.sqrt 2 * s7_b k) * (C₀' * s7_b l) :=
        mul_le_mul (s7f_phi_bound hr k x) (ha l x) (abs_nonneg _)
          (mul_nonneg (Real.sqrt_nonneg _) (s7f_b_nonneg k))
    _ = _ := by ring

theorem s7f_cov (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ} (hγ : 0 ≤ γ)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
    {a : NonzeroLattice d → Torus d → ℝ} {v : NonzeroLattice d → Fin d → Torus d → ℝ} {C₀ : ℝ}
    (hmode : s7_ModeData d s γ ρ r a v C₀)
    (G : Measure (NegSobolev d r)) [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianWithCov r G fun φ ψ =>
      ∫ x, φ x * responseRep (periodicRiesz d s) (withDensityReal ρ) γ ψ x ∂(withDensityReal ρ))
    (k l : NonzeroLattice d) :
    ∫ y, NegSobolev.coord y k * NegSobolev.coord y l ∂G = s7_Cmode r ρ a k l := by
  have h := hG.2 (s7_phi r k) (s7_phi r l) (HRS.MC.Sec7.S7a.s7a_phi_smooth r k)
    (HRS.MC.Sec7.S7a.s7a_phi_smooth r l)
  have hrep : ∀ x, responseRep (periodicRiesz d s) (withDensityReal ρ) γ (s7_phi r l) x = a l x := fun x =>
    HRS.MC.Sec7.S7e.s7e_responseRep_eq_of_eq hd hs0 hs hγ hρ
      (s7d_memLp_smooth hρ (HRS.MC.Sec7.S7a.s7a_phi_smooth r l))
      (HRS.Q66.q66_cont_of_smooth (hmode.smooth_a l)) (by simpa [pair] using hmode.mean_zero l)
      (hmode.resp l) x
  simp_rw [s7d_eval_phi] at h
  rw [h]
  unfold s7_Cmode
  exact integral_congr_ae (Eventually.of_forall fun x => by simp only [hrep])

theorem s7f_cmode_symm (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ} (hγ : 0 ≤ γ)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
    {a : NonzeroLattice d → Torus d → ℝ} {v : NonzeroLattice d → Fin d → Torus d → ℝ} {C₀ : ℝ}
    (hmode : s7_ModeData d s γ ρ r a v C₀)
    (G : Measure (NegSobolev d r)) [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianWithCov r G fun φ ψ =>
      ∫ x, φ x * responseRep (periodicRiesz d s) (withDensityReal ρ) γ ψ x ∂(withDensityReal ρ))
    (k l : NonzeroLattice d) : s7_Cmode r ρ a k l = s7_Cmode r ρ a l k := by
  rw [← s7f_cov hd hs0 hs hγ hρ hmode G hG k l, ← s7f_cov hd hs0 hs hγ hρ hmode G hG l k]
  exact integral_congr_ae (Eventually.of_forall fun y => mul_comm _ _)

theorem s7f_truncE_eq (K : Finset (NonzeroLattice d)) (y : NegSobolev d r) :
    truncE K y = ∑ k ∈ K, NegSobolev.coord y k • s7_eps r k := rfl

theorem s7f_bilin_trunc (T : NegSobolev d r →L[ℝ] NegSobolev d r →L[ℝ] ℝ) (K : Finset (NonzeroLattice d))
    (y : NegSobolev d r) :
    T (truncE K y) (truncE K y) = ∑ k ∈ K, ∑ l ∈ K,
      (NegSobolev.coord y k * NegSobolev.coord y l) * T (s7_eps r k) (s7_eps r l) := by
  rw [s7f_truncE_eq]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem s7f_gauss_expand (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hr : r = 2 * (d : ℝ) + 6)
    {γ : ℝ} (hγ : 0 ≤ γ) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
    {a : NonzeroLattice d → Torus d → ℝ} {v : NonzeroLattice d → Fin d → Torus d → ℝ} {C₀ : ℝ}
    (hmode : s7_ModeData d s γ ρ r a v C₀)
    (G : Measure (NegSobolev d r)) [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianWithCov r G fun φ ψ =>
      ∫ x, φ x * responseRep (periodicRiesz d s) (withDensityReal ρ) γ ψ x ∂(withDensityReal ρ))
    (T : NegSobolev d r →L[ℝ] NegSobolev d r →L[ℝ] ℝ) :
    ∫ y, T y y ∂G = ∑' k, ∑' l, s7_Cmode r ρ a k l * T (s7_eps r k) (s7_eps r l) := by
  classical
  have : IsGaussian G := hG.1.1
  obtain ⟨Cc, hCc0, hCc⟩ := s7f_cmode_bound hr hρ hmode
  have hb := s7d_b_summable (d := d)
  have hbound : ∀ k l, |s7_Cmode r ρ a k l * T (s7_eps r k) (s7_eps r l)| ≤
      (Cc * ‖T‖) * (s7_b k * s7_b l) := by
    intro k l
    have h1 : |T (s7_eps r k) (s7_eps r l)| ≤ ‖T‖ := by
      have h3 := (T (s7_eps r k)).le_opNorm (s7_eps r l)
      have h2 := T.le_opNorm (s7_eps r k)
      rw [Real.norm_eq_abs, HRS.MC.Sec7.S7e.s7e_eps_norm, mul_one] at h3
      rw [HRS.MC.Sec7.S7e.s7e_eps_norm, mul_one] at h2
      exact h3.trans h2
    rw [abs_mul]
    calc |s7_Cmode r ρ a k l| * |T (s7_eps r k) (s7_eps r l)| ≤
          (Cc * (s7_b k * s7_b l)) * ‖T‖ :=
          mul_le_mul (hCc k l) h1 (abs_nonneg _) (mul_nonneg hCc0
            (mul_nonneg (s7f_b_nonneg k) (s7f_b_nonneg l)))
      _ = _ := by ring
  obtain ⟨hsum, -, hrow⟩ := s7f_tsum2 hb s7f_b_nonneg hbound
  have hcont : Continuous (fun y : NegSobolev d r => T y y) :=
    T.continuous.clm_apply continuous_id
  have hlim : Tendsto (fun K : Finset (NonzeroLattice d) => ∫ y, T (truncE K y) (truncE K y) ∂G)
      atTop (𝓝 (∫ y, T y y ∂G)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun y => ‖T‖ * ‖y‖ ^ 2) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun K =>
        ((T.continuous.comp (s7d_truncE_continuous K)).clm_apply
          (s7d_truncE_continuous K)).aestronglyMeasurable
    · refine Eventually.of_forall fun K => Eventually.of_forall fun y => ?_
      have h3 := (T (truncE K y)).le_opNorm (truncE K y)
      have h2 := T.le_opNorm (truncE K y)
      have h4 := s7c_norm_trunc_le K y
      have h5 : ‖T (truncE K y)‖ ≤ ‖T‖ * ‖y‖ := h2.trans (mul_le_mul_of_nonneg_left h4 (norm_nonneg _))
      calc ‖T (truncE K y) (truncE K y)‖ ≤ ‖T (truncE K y)‖ * ‖truncE K y‖ := h3
        _ ≤ (‖T‖ * ‖y‖) * ‖y‖ := mul_le_mul h5 h4 (norm_nonneg _) (by positivity)
        _ = _ := by ring
    · exact (gaussian_sqnorm_integrable hG.1).const_mul _
    · refine Eventually.of_forall fun y => ?_
      exact (hcont.tendsto y).comp (s7c_tendsto_trunc y)
  have hLp : ∀ k : NonzeroLattice d, MemLp (fun y : NegSobolev d r => NegSobolev.coord y k) 2 G := fun k =>
    IsGaussian.memLp_dual G (negCoordCLM (m := r) k) 2 (by simp)
  have hint : ∀ k l : NonzeroLattice d,
      Integrable (fun y : NegSobolev d r => NegSobolev.coord y k * NegSobolev.coord y l) G :=
    fun k l => (hLp k).integrable_mul (hLp l)
  have hfin : ∀ K : Finset (NonzeroLattice d), ∫ y, T (truncE K y) (truncE K y) ∂G =
      ∑ k ∈ K, ∑ l ∈ K, s7_Cmode r ρ a k l * T (s7_eps r k) (s7_eps r l) := by
    intro K
    simp_rw [s7f_bilin_trunc]
    rw [integral_finset_sum _ (fun k _ => integrable_finset_sum _ fun l _ => (hint k l).mul_const _)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finset_sum _ (fun l _ => (hint k l).mul_const _)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_mul_const, s7f_cov hd hs0 hs hγ hρ hmode G hG k l]
  have hpair : Tendsto (fun K : Finset (NonzeroLattice d) =>
      ∑ k ∈ K, ∑ l ∈ K, s7_Cmode r ρ a k l * T (s7_eps r k) (s7_eps r l)) atTop
      (𝓝 (∑' p : NonzeroLattice d × NonzeroLattice d,
        s7_Cmode r ρ a p.1 p.2 * T (s7_eps r p.1) (s7_eps r p.2))) := by
    have h1 : Tendsto (fun S : Finset (NonzeroLattice d × NonzeroLattice d) =>
        ∑ p ∈ S, s7_Cmode r ρ a p.1 p.2 * T (s7_eps r p.1) (s7_eps r p.2)) atTop
        (𝓝 (∑' p : NonzeroLattice d × NonzeroLattice d,
          s7_Cmode r ρ a p.1 p.2 * T (s7_eps r p.1) (s7_eps r p.2))) := hsum.hasSum
    have h2 : Tendsto (fun K : Finset (NonzeroLattice d) => K ×ˢ K) atTop atTop := by
      refine Filter.tendsto_atTop_atTop.2 fun S => ⟨S.image Prod.fst ∪ S.image Prod.snd, fun K hK p hp => ?_⟩
      rw [Finset.mem_product]
      exact ⟨hK (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp)),
        hK (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp))⟩
    refine (h1.comp h2).congr fun K => ?_
    simp only [Function.comp]
    exact Finset.sum_product K K _
  have := tendsto_nhds_unique (hlim.congr hfin) hpair
  rw [this, ← hrow]

end HRS.MC.Sec7.S7f

end
