import HRS.MC.S7S7cAux9

/-!
# Packet `s7_S7c_hilbert_stein`, helper 10: passage to the limit in the finite-rank identities (Tannery)
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7c

open HRS HRS.Sec7 HRS.MC.SEdge HRS.StaticLimitAux

open Classical

variable {d : ℕ}

theorem s7c_main {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {r : ℝ}
    (hr : r = 2 * (d : ℝ) + 6) {γ : ℝ} (hγ : 0 ≤ γ) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
    {a : NonzeroLattice d → Torus d → ℝ} {v : NonzeroLattice d → Fin d → Torus d → ℝ} {C₀ : ℝ}
    (hmode : s7_ModeData d s γ ρ r a v C₀) {N : ℕ} (hN : 1 ≤ N) {F : NegSobolev d r → ℝ}
    (hF : s7_C2b F) :
    ∫ X, fderiv ℝ F (zetaE r (sed_Q d s N γ ρ) X) (zetaE r (sed_Q d s N γ ρ) X)
        ∂(sed_Q d s N γ ρ) =
      ∑' k : NonzeroLattice d, ∑' l : NonzeroLattice d,
          ∫ X, sed_A (v k) (s7_phi r l) X *
            iteratedFDeriv ℝ 2 F (zetaE r (sed_Q d s N γ ρ) X) ![s7_eps r k, s7_eps r l]
            ∂(sed_Q d s N γ ρ) -
        γ / Real.sqrt N * ∑' k : NonzeroLattice d,
          ∫ X, sed_B d s ρ γ (v k) X * fderiv ℝ F (zetaE r (sed_Q d s N γ ρ) X) (s7_eps r k)
            ∂(sed_Q d s N γ ρ) := by
  obtain ⟨hF2, M1, M2, hM1, hM2, h1, h2⟩ := s7c_C2b_facts hF
  have hr' : (d : ℝ) < 2 * r := by rw [hr]; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  haveI hQ : IsProbabilityMeasure (sed_Q d s N γ ρ) :=
    HRS.MC.SEdge.B4b.b4b_isProb hd hs0 hs hγ hρ N hN
  obtain ⟨CA, hCA0, hCA⟩ := s7c_A_bound hr hmode
  obtain ⟨CB, hCB0, hCB⟩ := s7c_B_mode hd hs0 hs hγ hρ hmode
  have hbsum : Summable (fun k : NonzeroLattice d => s7_b k) :=
    s7c_summable_jp (r := (d : ℝ) + 3) (by linarith)
  have hbnn : ∀ k : NonzeroLattice d, 0 ≤ s7_b k := fun k => by
    unfold s7_b; have := Torus.jp_pos k.1; positivity
  set Q := sed_Q d s N γ ρ with hQdef
  -- bounds and continuity of the integrands in `F`
  have hG2b : ∀ (k l : NonzeroLattice d) (y : NegSobolev d r),
      |fderiv ℝ (fderiv ℝ F) y (s7_eps r k) (s7_eps r l)| ≤ M2 := by
    intro k l y
    calc |fderiv ℝ (fderiv ℝ F) y (s7_eps r k) (s7_eps r l)|
        ≤ ‖fderiv ℝ (fderiv ℝ F) y (s7_eps r k)‖ * ‖s7_eps r l‖ :=
          (Real.norm_eq_abs _).symm.le.trans (ContinuousLinearMap.le_opNorm _ _)
      _ ≤ (‖fderiv ℝ (fderiv ℝ F) y‖ * ‖s7_eps r k‖) * ‖s7_eps r l‖ := by
          gcongr; exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ M2 := by rw [s7c_norm_eps, s7c_norm_eps]; linarith [h2 y]
  have hG2c : ∀ (k l : NonzeroLattice d), Continuous
      (fun y : NegSobolev d r => fderiv ℝ (fderiv ℝ F) y (s7_eps r k) (s7_eps r l)) := by
    intro k l
    have hc : Continuous (fderiv ℝ (fderiv ℝ F)) :=
      (hF2.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
    exact (hc.clm_apply continuous_const).clm_apply continuous_const
  have hG1b : ∀ (k : NonzeroLattice d) (y : NegSobolev d r),
      |fderiv ℝ F y (s7_eps r k)| ≤ M1 := by
    intro k y
    calc |fderiv ℝ F y (s7_eps r k)| ≤ ‖fderiv ℝ F y‖ * ‖s7_eps r k‖ :=
          (Real.norm_eq_abs _).symm.le.trans (ContinuousLinearMap.le_opNorm _ _)
      _ ≤ M1 := by rw [s7c_norm_eps]; linarith [h1 y]
  have hG1c : ∀ (k : NonzeroLattice d), Continuous
      (fun y : NegSobolev d r => fderiv ℝ F y (s7_eps r k)) := fun k =>
    (hF2.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hAint : ∀ k l : NonzeroLattice d, Integrable (sed_A (v k) (s7_phi r l) : Config d N → ℝ) Q :=
    fun k l => Integrable.of_bound (s7c_A_meas hN k l hmode.smooth_v).aestronglyMeasurable
      (CA * s7_b k * s7_b l) (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs]; exact hCA N hN k l X)
  -- the truncated and limiting coefficients
  set AAK : Finset (NonzeroLattice d) → NonzeroLattice d → NonzeroLattice d → ℝ :=
    fun K k l => ∫ X, sed_A (v k) (s7_phi r l) X *
      fderiv ℝ (fderiv ℝ F) (truncE K (zetaE r Q X)) (s7_eps r k) (s7_eps r l) ∂Q with hAAK
  set AAinf : NonzeroLattice d → NonzeroLattice d → ℝ :=
    fun k l => ∫ X, sed_A (v k) (s7_phi r l) X *
      fderiv ℝ (fderiv ℝ F) (zetaE r Q X) (s7_eps r k) (s7_eps r l) ∂Q with hAAinf
  set BBK : Finset (NonzeroLattice d) → NonzeroLattice d → ℝ :=
    fun K k => ∫ X, sed_B d s ρ γ (v k) X * fderiv ℝ F (truncE K (zetaE r Q X)) (s7_eps r k) ∂Q
    with hBBK
  set BBinf : NonzeroLattice d → ℝ :=
    fun k => ∫ X, sed_B d s ρ γ (v k) X * fderiv ℝ F (zetaE r Q X) (s7_eps r k) ∂Q with hBBinf
  have hAAlim : ∀ k l, Tendsto (fun K => AAK K k l) atTop (𝓝 (AAinf k l)) := fun k l =>
    s7c_dct_prod hd hs0 hs hγ hρ hr hN (hG2c k l) (hG2b k l) (hAint k l)
  have hBBlim : ∀ k, Tendsto (fun K => BBK K k) atTop (𝓝 (BBinf k)) := fun k =>
    s7c_dct_prod hd hs0 hs hγ hρ hr hN (hG1c k) (hG1b k) (hCB N hN k).1
  have hAbd : ∀ (Y : Config d N → NegSobolev d r) (k l : NonzeroLattice d),
      ‖∫ X, sed_A (v k) (s7_phi r l) X *
          fderiv ℝ (fderiv ℝ F) (Y X) (s7_eps r k) (s7_eps r l) ∂Q‖ ≤
        M2 * (CA * s7_b k * s7_b l) := by
    intro Y k l
    have := norm_integral_le_of_norm_le_const (μ := Q)
      (f := fun X => sed_A (v k) (s7_phi r l) X *
        fderiv ℝ (fderiv ℝ F) (Y X) (s7_eps r k) (s7_eps r l))
      (C := M2 * (CA * s7_b k * s7_b l)) (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_mul]
        calc _ ≤ (CA * s7_b k * s7_b l) * M2 :=
              mul_le_mul (hCA N hN k l X) (hG2b k l _) (abs_nonneg _) (by
                have := hbnn k; have := hbnn l; positivity)
          _ = _ := by ring)
    simpa using this
  have hBbd : ∀ (Y : Config d N → NegSobolev d r) (k : NonzeroLattice d),
      ‖∫ X, sed_B d s ρ γ (v k) X * fderiv ℝ F (Y X) (s7_eps r k) ∂Q‖ ≤ M1 * (CB * s7_b k) := by
    intro Y k
    obtain ⟨hBi, hBb⟩ := hCB N hN k
    calc ‖∫ X, sed_B d s ρ γ (v k) X * fderiv ℝ F (Y X) (s7_eps r k) ∂Q‖
        ≤ ∫ X, ‖sed_B d s ρ γ (v k) X * fderiv ℝ F (Y X) (s7_eps r k)‖ ∂Q :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ X, |sed_B d s ρ γ (v k) X| * M1 ∂Q := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
            (hBi.abs.mul_const M1) (Filter.Eventually.of_forall fun X => ?_)
          beta_reduce
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_left (hG1b k _) (abs_nonneg _)
      _ = (∫ X, |sed_B d s ρ γ (v k) X| ∂Q) * M1 := integral_mul_const _ _
      _ ≤ (CB * s7_b k) * M1 := mul_le_mul_of_nonneg_right hBb hM1
      _ = _ := by ring
  -- summability of the bounds
  have hbound1 : Summable (fun p : NonzeroLattice d × NonzeroLattice d =>
      M2 * (CA * s7_b p.1 * s7_b p.2)) := by
    have := (hbsum.mul_of_nonneg hbsum (fun k => hbnn k) (fun k => hbnn k)).mul_left (M2 * CA)
    refine this.congr fun p => ?_
    ring
  have hbound2 : Summable (fun k : NonzeroLattice d => M1 * (CB * s7_b k)) :=
    (hbsum.mul_left CB).mul_left M1
  -- Tannery for `A`
  set g1 : Finset (NonzeroLattice d) → NonzeroLattice d × NonzeroLattice d → ℝ :=
    fun K p => if p.1 ∈ K ∧ p.2 ∈ K then AAK K p.1 p.2 else 0 with hg1
  have hT1 : Tendsto (fun K => ∑' p, g1 K p) atTop (𝓝 (∑' p : NonzeroLattice d × NonzeroLattice d,
      AAinf p.1 p.2)) := by
    refine tendsto_tsum_of_dominated_convergence hbound1 (fun p => ?_)
      (Filter.Eventually.of_forall fun K p => ?_)
    · refine (hAAlim p.1 p.2).congr' ?_
      filter_upwards [Filter.eventually_ge_atTop ({p.1, p.2} : Finset (NonzeroLattice d))] with K hK
      have h1' : p.1 ∈ K := hK (by simp)
      have h2' : p.2 ∈ K := hK (by simp)
      simp [hg1, h1', h2']
    · by_cases hp : p.1 ∈ K ∧ p.2 ∈ K
      · simp only [hg1, if_pos hp]
        exact hAbd _ p.1 p.2
      · simp only [hg1, if_neg hp, norm_zero]
        have := hbnn p.1; have := hbnn p.2; positivity
  have hsum1 : ∀ K : Finset (NonzeroLattice d),
      ∑' p, g1 K p = ∑ k ∈ K, ∑ l ∈ K, AAK K k l := by
    intro K
    rw [tsum_eq_sum (s := K ×ˢ K)]
    · rw [Finset.sum_product]
      refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun l hl => ?_
      simp [hg1, hk, hl]
    · intro p hp
      have : ¬ (p.1 ∈ K ∧ p.2 ∈ K) := by simpa [Finset.mem_product] using hp
      simp [hg1, this]
  have hAsum : Summable (fun p : NonzeroLattice d × NonzeroLattice d => AAinf p.1 p.2) :=
    Summable.of_norm_bounded hbound1 fun p => hAbd _ p.1 p.2
  have hAiter : ∑' p : NonzeroLattice d × NonzeroLattice d, AAinf p.1 p.2 =
      ∑' k, ∑' l, AAinf k l :=
    hAsum.tsum_prod' fun k => (hbsum.mul_left (M2 * CA * s7_b k)).of_norm_bounded fun l => by
      have := hAbd (fun X => zetaE r Q X) k l
      refine this.trans (le_of_eq ?_)
      ring
  -- Tannery for `B`
  set g2 : Finset (NonzeroLattice d) → NonzeroLattice d → ℝ :=
    fun K k => if k ∈ K then BBK K k else 0 with hg2
  have hT2 : Tendsto (fun K => ∑' k, g2 K k) atTop (𝓝 (∑' k, BBinf k)) := by
    refine tendsto_tsum_of_dominated_convergence hbound2 (fun k => ?_)
      (Filter.Eventually.of_forall fun K k => ?_)
    · refine (hBBlim k).congr' ?_
      filter_upwards [Filter.eventually_ge_atTop ({k} : Finset (NonzeroLattice d))] with K hK
      have h1' : k ∈ K := hK (by simp)
      simp [hg2, h1']
    · by_cases hp : k ∈ K
      · simp only [hg2, if_pos hp]
        exact hBbd _ k
      · simp only [hg2, if_neg hp, norm_zero]
        have := hbnn k; positivity
  have hsum2 : ∀ K : Finset (NonzeroLattice d), ∑' k, g2 K k = ∑ k ∈ K, BBK K k := by
    intro K
    rw [tsum_eq_sum (s := K)]
    · exact Finset.sum_congr rfl fun k hk => by simp [hg2, hk]
    · intro k hk
      simp [hg2, hk]
  -- the finite-rank identities
  have hfin : ∀ K : Finset (NonzeroLattice d),
      ∫ X, fderiv ℝ F (truncE K (zetaE r Q X)) (truncE K (zetaE r Q X)) ∂Q =
        ∑ k ∈ K, ∑ l ∈ K, AAK K k l - γ / Real.sqrt N * ∑ k ∈ K, BBK K k := by
    intro K
    have := s7c_finite_identity hd hs0 hs hγ hρ hmode hN hF (s7c_kap K)
    rw [← hQdef] at this
    simp only [s7c_Wtr_kap hr' hN Q K] at this
    rw [this]
    have eA : ∀ k : NonzeroLattice d, ∑ c : Fin K.card, AAK K k (s7c_kap K c) = ∑ l ∈ K, AAK K k l :=
      fun k => s7c_sum_kap K (fun l => AAK K k l)
    have eA' : ∑ b : Fin K.card, ∑ c : Fin K.card, AAK K (s7c_kap K b) (s7c_kap K c) =
        ∑ k ∈ K, ∑ l ∈ K, AAK K k l := by
      simp_rw [eA]
      exact s7c_sum_kap K (fun k => ∑ l ∈ K, AAK K k l)
    have eB : ∑ b : Fin K.card, BBK K (s7c_kap K b) = ∑ k ∈ K, BBK K k :=
      s7c_sum_kap K (fun k => BBK K k)
    rw [← eA', ← eB]
  -- the limits
  have hlimL := s7c_lim_L hd hs0 hs hγ hρ hr hN hF
  have hlimR : Tendsto (fun K : Finset (NonzeroLattice d) =>
      ∫ X, fderiv ℝ F (truncE K (zetaE r Q X)) (truncE K (zetaE r Q X)) ∂Q) atTop
      (𝓝 (∑' k, ∑' l, AAinf k l - γ / Real.sqrt N * ∑' k, BBinf k)) := by
    have e1 : Tendsto (fun K : Finset (NonzeroLattice d) => ∑ k ∈ K, ∑ l ∈ K, AAK K k l) atTop
        (𝓝 (∑' k, ∑' l, AAinf k l)) := by
      rw [← hAiter]
      exact hT1.congr fun K => hsum1 K
    have e2 : Tendsto (fun K : Finset (NonzeroLattice d) => ∑ k ∈ K, BBK K k) atTop
        (𝓝 (∑' k, BBinf k)) := hT2.congr fun K => hsum2 K
    exact (e1.sub (e2.const_mul (γ / Real.sqrt N))).congr fun K => (hfin K).symm
  have := tendsto_nhds_unique hlimL hlimR
  rw [this]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rfl

end HRS.MC.Sec7.S7c

end
