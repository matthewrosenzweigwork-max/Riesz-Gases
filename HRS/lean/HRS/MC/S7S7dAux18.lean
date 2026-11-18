import HRS.MC.S7S7dAux17

/-!
# Packet `s7_S7d_uniform_limits`, helper 18: the pair estimate for (R2)
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7d

open HRS HRS.Sec7 HRS.MC.SEdge HRS.StaticLimitAux

variable {d : ℕ} {s : ℝ} {r : ℝ}

theorem s7d_pair_R2 (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hr : r = 2 * (d : ℝ) + 6)
    {γ : ℝ} (hγ : 0 ≤ γ) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
    {a : NonzeroLattice d → Torus d → ℝ} {v : NonzeroLattice d → Fin d → Torus d → ℝ} {C₀ : ℝ}
    (hmode : s7_ModeData d s γ ρ r a v C₀)
    (G : Measure (NegSobolev d r)) [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianWithCov r G fun φ ψ =>
      ∫ x, φ x * responseRep (periodicRiesz d s) (withDensityReal ρ) γ ψ x ∂(withDensityReal ρ))
    {w : Torus d → ℝ} (hw : Torus.IsSmooth w) {τ : NonzeroLattice d → ℝ} (hτ : Summable τ)
    (hτ0 : ∀ j, 0 ≤ τ j) (hτb : ∀ j, |∫ x, a j x * w x ∂(withDensityReal ρ)| ≤ τ j)
    {C2 : ℝ} (hC2 : ∀ N : ℕ, 1 ≤ N → ∫ X, sed_Y (sed_Q d s N γ ρ) w X ^ 2 ∂(sed_Q d s N γ ρ) ≤ C2)
    {η : ℝ} (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N → ∀ f : NegSobolev d r → ℝ, s7d_Cl f → ∀ u u' : NegSobolev d r,
      ‖u‖ ≤ 1 → ‖u'‖ ≤ 1 →
      |∫ X, sed_Y (sed_Q d s N γ ρ) w X *
            iteratedFDeriv ℝ 2 f (zetaE r (sed_Q d s N γ ρ) X) ![u, u'] ∂(sed_Q d s N γ ρ) -
        ∑' j : NonzeroLattice d, (∫ x, a j x * w x ∂(withDensityReal ρ)) *
          ∫ F, iteratedFDeriv ℝ 3 f F ![u, u', s7_eps r j] ∂G| ≤ η := by
  classical
  have hr' : (d : ℝ) < 2 * r := by rw [hr]; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  set δ : ℝ := η / 4 with hδ
  have hδ0 : 0 < δ := by positivity
  have hwc : Continuous w := HRS.Q66.q66_cont_of_smooth hw
  obtain ⟨T, hT0, hT⟩ := s7d_smooth_bdd hw
  set t : NonzeroLattice d → ℝ := fun j => ∫ x, a j x * w x ∂(withDensityReal ρ) with ht
  set S : ℝ := ∑' j, τ j with hS
  have hS0 : 0 ≤ S := tsum_nonneg hτ0
  -- the `Y`-hypotheses of the truncation estimate
  have hQ : ∀ N : ℕ, 1 ≤ N → IsProbabilityMeasure (sed_Q d s N γ ρ) := fun N hN =>
    HRS.MC.SEdge.B4b.b4b_isProb hd hs0 hs hγ hρ N hN
  have hYm : ∀ N, 1 ≤ N → Measurable (sed_Y (sed_Q d s N γ ρ) w) := fun N hN =>
    haveI := hQ N hN
    HRS.MC.Sec7.S7c.s7c_sedY_meas hN _ hwc
  have hYi : ∀ N, 1 ≤ N → Integrable (fun X => |sed_Y (sed_Q d s N γ ρ) w X|) (sed_Q d s N γ ρ) :=
    fun N hN => by
      haveI := hQ N hN
      simpa using s7d_sedY_pow_integrable hN (sed_Q d s N γ ρ) hwc hT 1
  have hY2 : ∀ N, 1 ≤ N → Integrable (fun X => sed_Y (sed_Q d s N γ ρ) w X ^ 2) (sed_Q d s N γ ρ) :=
    fun N hN => by
      haveI := hQ N hN
      simpa [sq_abs] using s7d_sedY_pow_integrable hN (sed_Q d s N γ ρ) hwc hT 2
  obtain ⟨K₁, hK₁⟩ := s7d_W_trunc_err hd hs0 hs hγ hρ hr
    (fun N => sed_Y (sed_Q d s N γ ρ) w) hYm hYi hY2 hC2 hδ0
  have hevG : ∀ᶠ K : Finset (NonzeroLattice d) in atTop,
      ∫ F, min 2 ‖F - truncE K F‖ ∂G < δ / (S + 1) :=
    (tendsto_order.1 (s7d_gauss_trunc_tendsto G)).2 _ (by positivity)
  have hevτ : ∀ᶠ K : Finset (NonzeroLattice d) in atTop, (∑' k, τ k) - ∑ k ∈ K, τ k < δ :=
    (tendsto_order.1 (s7d_tail_tendsto hτ)).2 _ hδ0
  obtain ⟨K, hK⟩ := ((eventually_ge_atTop K₁).and (hevG.and hevτ)).exists
  have hKK₁ : K₁ ⊆ K := hK.1
  have hKG : ∫ F, min 2 ‖F - truncE K F‖ ∂G < δ / (S + 1) := hK.2.1
  have hKτ : (∑' k, τ k) - ∑ k ∈ K, τ k < δ := hK.2.2
  -- finite-dimensional core
  obtain ⟨N₀, hN₀⟩ := s7d_core_R2 (r := r) hd hs0 hs hγ hρ (HRS.MC.Sec7.S7c.s7c_kap K) hw hδ0
  refine ⟨N₀, fun N hN hN1 f hf u u' hu hu' => ?_⟩
  haveI := hQ N hN1
  set Q := sed_Q d s N γ ρ with hQdef
  set Θ : NegSobolev d r → ℝ := fun x => iteratedFDeriv ℝ 2 f x ![u, u'] with hΘdef
  have hΘ : s7d_Th Θ := s7d_Th_D2 hf u u' hu hu'
  -- step A: truncation of `W`
  have hA := hK₁ K hKK₁ N hN1 Θ hΘ
  -- step B: the finite-dimensional core
  have hB := hN₀ N hN hN1 f hf u u' hu hu'
  set κ := HRS.MC.Sec7.S7c.s7c_kap K with hκ
  have hιcs : ∀ X, HRS.MC.Sec7.S7c.s7c_iota r κ (centeredStat Q (fun a => s7_phi r (κ a)) X) =
      truncE K (zetaE r Q X) := fun X => HRS.MC.Sec7.S7c.s7c_Wtr_kap hr' hN1 Q K X
  have hB1 : ∫ X, sed_Y Q w X *
        iteratedFDeriv ℝ 2 f (HRS.MC.Sec7.S7c.s7c_iota r κ
          (centeredStat Q (fun a => s7_phi r (κ a)) X)) ![u, u'] ∂Q =
      ∫ X, sed_Y Q w X * Θ (truncE K (zetaE r Q X)) ∂Q := by
    refine integral_congr_ae (Eventually.of_forall fun X => ?_)
    simp only [hιcs]
    rfl
  rw [hB1] at hB
  -- the Gaussian side of the core
  have hcoef : ∀ c : Fin K.card, (∫ x, w x * responseInverse (periodicRiesz d s) (withDensityReal ρ) γ
      (s7_phi r (κ c)) x ∂(withDensityReal ρ)) = t (κ c) := by
    intro c
    have hae := s7d_respInv_ae hd hs0 hs hγ hρ (s7d_memLp_smooth hρ
      (HRS.MC.Sec7.S7a.s7a_phi_smooth r (κ c)))
      (HRS.Q66.q66_cont_of_smooth (hmode.smooth_a (κ c))) (by simpa [pair] using hmode.mean_zero (κ c))
      (hmode.resp (κ c))
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx, mul_comm]
  set g : NonzeroLattice d → ℝ := fun j => ∫ F, iteratedFDeriv ℝ 3 f F ![u, u', s7_eps r j] ∂G with hg
  set gK : NonzeroLattice d → ℝ := fun j =>
    ∫ F, iteratedFDeriv ℝ 3 f (truncE K F) ![u, u', s7_eps r j] ∂G with hgK
  have hΘ3 : ∀ j, s7d_Th (fun x => iteratedFDeriv ℝ 3 f x ![u, u', s7_eps r j]) := fun j =>
    s7d_Th_D3 hf u u' _ hu hu' (le_of_eq (HRS.MC.Sec7.S7c.s7c_norm_eps r j))
  have hgauss : ∀ c : Fin K.card, ∫ z, iteratedFDeriv ℝ 3 f (HRS.MC.Sec7.S7c.s7c_iota r κ z)
        ![u, u', s7_eps r (κ c)] ∂(multivariateGaussian 0 (sed_Cmat d s γ ρ (fun a => s7_phi r (κ a)))) =
      gK (κ c) := fun c =>
    s7d_gauss_to_G hd hs0 hs hγ hρ hmode K G hG (hΘ3 (κ c)).1
  simp only [hcoef, hgauss] at hB
  rw [HRS.MC.Sec7.S7c.s7c_sum_kap K (fun j => t j * gK j)] at hB
  -- step C: truncation on the Gaussian side
  have hC : |∑ j ∈ K, t j * gK j - ∑ j ∈ K, t j * g j| ≤ δ := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hj : ∀ j ∈ K, |t j * gK j - t j * g j| ≤ τ j * (δ / (S + 1)) := by
      intro j _
      rw [← mul_sub, abs_mul]
      refine mul_le_mul (hτb j) ?_ (abs_nonneg _) (hτ0 j)
      exact (s7d_G_trunc_err G (hΘ3 j) K).trans hKG.le
    refine (Finset.sum_le_sum hj).trans ?_
    rw [← Finset.sum_mul]
    have h1 : ∑ j ∈ K, τ j ≤ S := hτ.sum_le_tsum K (fun j _ => hτ0 j)
    calc (∑ j ∈ K, τ j) * (δ / (S + 1)) ≤ S * (δ / (S + 1)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ δ := by
          rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
          nlinarith
  -- step D: the tail in `j`
  have hD : |∑' j, t j * g j - ∑ j ∈ K, t j * g j| ≤ δ := by
    have hF : ∀ j, |t j * g j| ≤ τ j := fun j => by
      rw [abs_mul]
      calc |t j| * |g j| ≤ τ j * 1 :=
            mul_le_mul (hτb j) (s7d_Th_abs_int G (hΘ3 j)) (abs_nonneg _) (hτ0 j)
        _ = τ j := mul_one _
    exact (s7d_tsum1_tail hτ hF K).trans hKτ.le
  -- assemble
  have hfinal : |(∫ X, sed_Y Q w X * Θ (zetaE r Q X) ∂Q) - ∑' j, t j * g j| ≤ 4 * δ := by
    calc _ = |((∫ X, sed_Y Q w X * Θ (zetaE r Q X) ∂Q) - ∫ X, sed_Y Q w X * Θ (truncE K (zetaE r Q X)) ∂Q) +
          ((∫ X, sed_Y Q w X * Θ (truncE K (zetaE r Q X)) ∂Q) - ∑ j ∈ K, t j * gK j) +
          (∑ j ∈ K, t j * gK j - ∑ j ∈ K, t j * g j) +
          (∑ j ∈ K, t j * g j - ∑' j, t j * g j)| := by congr 1; ring
      _ ≤ |(∫ X, sed_Y Q w X * Θ (zetaE r Q X) ∂Q) - ∫ X, sed_Y Q w X * Θ (truncE K (zetaE r Q X)) ∂Q| +
          |(∫ X, sed_Y Q w X * Θ (truncE K (zetaE r Q X)) ∂Q) - ∑ j ∈ K, t j * gK j| +
          |∑ j ∈ K, t j * gK j - ∑ j ∈ K, t j * g j| + |∑ j ∈ K, t j * g j - ∑' j, t j * g j| := by
          have h4 : ∀ a b c e : ℝ, |a + b + c + e| ≤ |a| + |b| + |c| + |e| := fun a b c e => by
            calc |a + b + c + e| ≤ |a + b + c| + |e| := abs_add_le _ _
              _ ≤ |a| + |b| + |c| + |e| := by linarith [abs_add_three a b c]
          exact h4 _ _ _ _
      _ ≤ δ + δ + δ + δ := by
          refine add_le_add (add_le_add (add_le_add hA hB) hC) ?_
          rw [abs_sub_comm]; exact hD
      _ = 4 * δ := by ring
  have : 4 * δ = η := by rw [hδ]; ring
  rw [this] at hfinal
  exact hfinal

end HRS.MC.Sec7.S7d

end
