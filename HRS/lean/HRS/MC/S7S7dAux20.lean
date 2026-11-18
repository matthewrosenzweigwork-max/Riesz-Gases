import HRS.MC.S7S7dAux19

/-!
# Packet `s7_S7d_uniform_limits`, helper 20: the single-mode estimate for (R3)
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7d

open HRS HRS.Sec7 HRS.MC.SEdge HRS.StaticLimitAux

variable {d : ℕ} {s : ℝ} {r : ℝ}

theorem s7d_B_meas (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ} (hγ : 0 < γ)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {v : Fin d → Torus d → ℝ}
    (hv : ∀ j, Torus.IsSmooth (v j)) {N : ℕ} (hN : 1 ≤ N) :
    Measurable (fun X : Config d N => sed_B d s ρ γ v X) := by
  obtain ⟨B, c, hc, hB⟩ := HRS.MC.SEdge.B2a.sed_B2a_envelope_proof hd hs0 hs hv
  have hsd : s < (d : ℝ) := by
    have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith
  have hvc : ∀ j, Continuous (v j) := fun j => HRS.Q66.q66_cont_of_smooth (hv j)
  have hmeas := HRS.Q66.q66_hv_measurable hsd hvc
  have hsymm := HRS.Q66.q66_hv_symm hsd v
  obtain ⟨e, he⟩ := HRS.MC.SEdge.B3.sed_B3_onb_proof (by omega) hρ
  let D : HRS.Q08.Q08Data d := HRS.MC.SEdge.B9a.b9a_D hd hs0 hs hγ hρ c hc B (HRS.Q66.q66_hv d s v)
    hmeas hsymm hB e he 0 (fun a => Fin.elim0 a) (fun a => Fin.elim0 a)
  exact (HRS.Q08.q08_measurable_stat D N).fst

theorem s7d_pair_R3 (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hr : r = 2 * (d : ℝ) + 6)
    {γ : ℝ} (hγ : 0 < γ) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
    {a : NonzeroLattice d → Torus d → ℝ} {v₀ : NonzeroLattice d → Fin d → Torus d → ℝ} {C₀ : ℝ}
    (hmode : s7_ModeData d s γ ρ r a v₀ C₀)
    (G : Measure (NegSobolev d r)) [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianWithCov r G fun φ ψ =>
      ∫ x, φ x * responseRep (periodicRiesz d s) (withDensityReal ρ) γ ψ x ∂(withDensityReal ρ))
    {v : Fin d → Torus d → ℝ} (hv : ∀ j, Torus.IsSmooth (v j))
    (hB4 : ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      Integrable (fun X => |sed_B d s ρ γ v X| ^ (2 * 2)) (sed_Q d s N γ ρ) ∧
        ∫ X, |sed_B d s ρ γ v X| ^ (2 * 2) ∂(sed_Q d s N γ ρ) ≤ C)
    {C2 : ℝ} (hB2 : ∀ N : ℕ, 1 ≤ N →
      Integrable (fun X => |sed_B d s ρ γ v X| ^ (2 * 1)) (sed_Q d s N γ ρ) ∧
        ∫ X, |sed_B d s ρ γ v X| ^ (2 * 1) ∂(sed_Q d s N γ ρ) ≤ C2)
    {τ : NonzeroLattice d → ℝ} (hτ : Summable τ) (hτ0 : ∀ j, 0 ≤ τ j) {cQ : ℝ} (hcQ : 0 ≤ cQ)
    (hQb : ∀ l j, |sed_Qt d s ρ v (a l) (a j)| ≤ cQ * (τ l * τ j))
    {η : ℝ} (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N → ∀ f : NegSobolev d r → ℝ, s7d_Cl f → ∀ u : NegSobolev d r,
      ‖u‖ ≤ 1 →
      |∫ X, sed_B d s ρ γ v X * fderiv ℝ f (zetaE r (sed_Q d s N γ ρ) X) u ∂(sed_Q d s N γ ρ) -
        (1 / 2) * ∑' l : NonzeroLattice d, ∑' j : NonzeroLattice d,
          sed_Qt d s ρ v (a l) (a j) *
            ∫ F, iteratedFDeriv ℝ 3 f F ![u, s7_eps r l, s7_eps r j] ∂G| ≤ η := by
  classical
  have hr' : (d : ℝ) < 2 * r := by rw [hr]; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  set δ : ℝ := η / 4 with hδ
  have hδ0 : 0 < δ := by positivity
  set S : ℝ := ∑' j, τ j with hS
  have hS0 : 0 ≤ S := tsum_nonneg hτ0
  have hQ : ∀ N : ℕ, 1 ≤ N → IsProbabilityMeasure (sed_Q d s N γ ρ) := fun N hN =>
    HRS.MC.SEdge.B4b.b4b_isProb hd hs0 hs hγ.le hρ N hN
  have hYm : ∀ N, 1 ≤ N → Measurable (sed_B d s ρ γ v (N := N)) := fun N hN =>
    s7d_B_meas hd hs0 hs hγ hρ hv hN
  have hY2 : ∀ N, 1 ≤ N → Integrable (fun X => sed_B d s ρ γ v X ^ 2) (sed_Q d s N γ ρ) :=
    fun N hN => by simpa [sq_abs] using (hB2 N hN).1
  have hYi : ∀ N, 1 ≤ N → Integrable (fun X => |sed_B d s ρ γ v X|) (sed_Q d s N γ ρ) :=
    fun N hN => by
      haveI := hQ N hN
      refine ((hB2 N hN).1.add (integrable_const (1 : ℝ))).mono' (hYm N hN).abs.aestronglyMeasurable
        (Eventually.of_forall fun X => ?_)
      rw [Real.norm_eq_abs, abs_abs]
      show |sed_B d s ρ γ v X| ≤ |sed_B d s ρ γ v X| ^ (2 * 1) + 1
      have h21 : |sed_B d s ρ γ v X| ^ (2 * 1) = |sed_B d s ρ γ v X| ^ 2 := by norm_num
      rw [h21]
      nlinarith [abs_nonneg (sed_B d s ρ γ v X), sq_nonneg (|sed_B d s ρ γ v X| - 1)]
  have hC2 : ∀ N, 1 ≤ N → ∫ X, sed_B d s ρ γ v X ^ 2 ∂(sed_Q d s N γ ρ) ≤ C2 := fun N hN => by
    simpa [sq_abs] using (hB2 N hN).2
  obtain ⟨K₁, hK₁⟩ := s7d_W_trunc_err hd hs0 hs hγ.le hρ hr
    (fun N => sed_B d s ρ γ v (N := N)) hYm hYi hY2 hC2 hδ0
  have hevG : ∀ᶠ K : Finset (NonzeroLattice d) in atTop,
      ∫ F, min 2 ‖F - truncE K F‖ ∂G < δ / (cQ * S ^ 2 + 1) :=
    (tendsto_order.1 (s7d_gauss_trunc_tendsto G)).2 _ (by positivity)
  have hevτ := s7d_tail2_eventually hτ hτ0 hcQ hδ0
  obtain ⟨K, hK⟩ := ((eventually_ge_atTop K₁).and (hevG.and hevτ)).exists
  have hKK₁ : K₁ ⊆ K := hK.1
  have hKG : ∫ F, min 2 ‖F - truncE K F‖ ∂G < δ / (cQ * S ^ 2 + 1) := hK.2.1
  have hKτ : cQ * ((∑' k, τ k) ^ 2 - (∑ k ∈ K, τ k) ^ 2) < δ := hK.2.2
  obtain ⟨N₀, hN₀⟩ := s7d_core_R3 (r := r) hd hs0 hs hγ hρ (HRS.MC.Sec7.S7c.s7c_kap K) hv hB4 hδ0
  refine ⟨N₀, fun N hN hN1 f hf u hu => ?_⟩
  haveI := hQ N hN1
  set Q := sed_Q d s N γ ρ with hQdef
  set Θ : NegSobolev d r → ℝ := fun x => fderiv ℝ f x u with hΘdef
  have hΘ : s7d_Th Θ := s7d_Th_D1 hf u hu
  have hA := hK₁ K hKK₁ N hN1 Θ hΘ
  have hB := hN₀ N hN hN1 f hf u hu
  set κ := HRS.MC.Sec7.S7c.s7c_kap K with hκ
  have hιcs : ∀ X, HRS.MC.Sec7.S7c.s7c_iota r κ (centeredStat Q (fun a => s7_phi r (κ a)) X) =
      truncE K (zetaE r Q X) := fun X => HRS.MC.Sec7.S7c.s7c_Wtr_kap hr' hN1 Q K X
  have hB1 : ∫ X, sed_B d s ρ γ v X *
        fderiv ℝ f (HRS.MC.Sec7.S7c.s7c_iota r κ
          (centeredStat Q (fun a => s7_phi r (κ a)) X)) u ∂Q =
      ∫ X, sed_B d s ρ γ v X * Θ (truncE K (zetaE r Q X)) ∂Q := by
    refine integral_congr_ae (Eventually.of_forall fun X => ?_)
    simp only [hιcs]
    rfl
  rw [hB1] at hB
  -- identification of the coefficients
  have hae : ∀ c : Fin K.card, responseInverse (periodicRiesz d s) (withDensityReal ρ) γ
      (s7_phi r (κ c)) =ᵐ[withDensityReal ρ] a (κ c) := fun c =>
    s7d_respInv_ae hd hs0 hs hγ.le hρ (s7d_memLp_smooth hρ (HRS.MC.Sec7.S7a.s7a_phi_smooth r (κ c)))
      (HRS.Q66.q66_cont_of_smooth (hmode.smooth_a (κ c))) (by simpa [pair] using hmode.mean_zero (κ c))
      (hmode.resp (κ c))
  set g : NonzeroLattice d → NonzeroLattice d → ℝ := fun l j =>
    ∫ F, iteratedFDeriv ℝ 3 f F ![u, s7_eps r l, s7_eps r j] ∂G with hg
  set gK : NonzeroLattice d → NonzeroLattice d → ℝ := fun l j =>
    ∫ F, iteratedFDeriv ℝ 3 f (truncE K F) ![u, s7_eps r l, s7_eps r j] ∂G with hgK
  set q : NonzeroLattice d → NonzeroLattice d → ℝ := fun l j => sed_Qt d s ρ v (a l) (a j) with hq
  have hΘ3 : ∀ l j, s7d_Th (fun x => iteratedFDeriv ℝ 3 f x ![u, s7_eps r l, s7_eps r j]) := fun l j =>
    s7d_Th_D3 hf u _ _ hu (le_of_eq (HRS.MC.Sec7.S7c.s7c_norm_eps r l))
      (le_of_eq (HRS.MC.Sec7.S7c.s7c_norm_eps r j))
  have hgauss : ∀ b c : Fin K.card, ∫ z, iteratedFDeriv ℝ 3 f (HRS.MC.Sec7.S7c.s7c_iota r κ z)
        ![u, s7_eps r (κ b), s7_eps r (κ c)]
        ∂(multivariateGaussian 0 (sed_Cmat d s γ ρ (fun a => s7_phi r (κ a)))) =
      gK (κ b) (κ c) := fun b c =>
    s7d_gauss_to_G hd hs0 hs hγ.le hρ hmode K G hG (hΘ3 (κ b) (κ c)).1
  have hqK : ∀ b c : Fin K.card, sed_Qt d s ρ v
      (responseInverse (periodicRiesz d s) (withDensityReal ρ) γ (s7_phi r (κ b)))
      (responseInverse (periodicRiesz d s) (withDensityReal ρ) γ (s7_phi r (κ c))) = q (κ b) (κ c) :=
    fun b c => s7d_Qt_congr (hae b) (hae c)
  simp only [hgauss, hqK] at hB
  have hsum2 : ∑ b : Fin K.card, ∑ c : Fin K.card, q (κ b) (κ c) * gK (κ b) (κ c) =
      ∑ l ∈ K, ∑ j ∈ K, q l j * gK l j := by
    rw [HRS.MC.Sec7.S7c.s7c_sum_kap K (fun l => ∑ c : Fin K.card, q l (κ c) * gK l (κ c))]
    refine Finset.sum_congr rfl fun l _ => ?_
    exact HRS.MC.Sec7.S7c.s7c_sum_kap K (fun j => q l j * gK l j)
  rw [hsum2] at hB
  -- step C: truncation on the Gaussian side (both indices)
  have hC : |∑ l ∈ K, ∑ j ∈ K, q l j * gK l j - ∑ l ∈ K, ∑ j ∈ K, q l j * g l j| ≤ δ := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hl : ∀ l ∈ K, |∑ j ∈ K, q l j * gK l j - ∑ j ∈ K, q l j * g l j| ≤
        ∑ j ∈ K, cQ * (τ l * τ j) * (δ / (cQ * S ^ 2 + 1)) := by
      intro l _
      rw [← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [← mul_sub, abs_mul]
      refine mul_le_mul (hQb l j) ?_ (abs_nonneg _) (by have := hτ0 l; have := hτ0 j; positivity)
      exact (s7d_G_trunc_err G (hΘ3 l j) K).trans hKG.le
    refine (Finset.sum_le_sum hl).trans ?_
    have e : ∑ l ∈ K, ∑ j ∈ K, cQ * (τ l * τ j) * (δ / (cQ * S ^ 2 + 1)) =
        cQ * (∑ l ∈ K, τ l) ^ 2 * (δ / (cQ * S ^ 2 + 1)) := by
      have h22 : (∑ l ∈ K, τ l) ^ 2 = ∑ l ∈ K, ∑ j ∈ K, τ l * τ j := by
        rw [sq, Finset.sum_mul_sum]
      rw [h22, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [e]
    have h1 : ∑ l ∈ K, τ l ≤ S := hτ.sum_le_tsum K (fun j _ => hτ0 j)
    have h0 : 0 ≤ ∑ l ∈ K, τ l := Finset.sum_nonneg fun j _ => hτ0 j
    have h2 : (∑ l ∈ K, τ l) ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ h0 h1 2
    calc cQ * (∑ l ∈ K, τ l) ^ 2 * (δ / (cQ * S ^ 2 + 1)) ≤ cQ * S ^ 2 * (δ / (cQ * S ^ 2 + 1)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hcQ) (by positivity)
      _ ≤ δ := by
          rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
          nlinarith [mul_nonneg hcQ (sq_nonneg S)]
  have hD : |∑' l, ∑' j, q l j * g l j - ∑ l ∈ K, ∑ j ∈ K, q l j * g l j| ≤ δ := by
    have hF : ∀ l j, |q l j * g l j| ≤ cQ * (τ l * τ j) := fun l j => by
      rw [abs_mul]
      calc |q l j| * |g l j| ≤ cQ * (τ l * τ j) * 1 :=
            mul_le_mul (hQb l j) (s7d_Th_abs_int G (hΘ3 l j)) (abs_nonneg _)
              (by have := hτ0 l; have := hτ0 j; positivity)
        _ = _ := mul_one _
    exact (s7d_tsum2_tail hτ hτ0 hcQ hF K).trans hKτ.le
  have hfinal : |(∫ X, sed_B d s ρ γ v X * Θ (zetaE r Q X) ∂Q) - (1 / 2) * ∑' l, ∑' j, q l j * g l j| ≤ 4 * δ := by
    set Mtr := ∫ X, sed_B d s ρ γ v X * Θ (truncE K (zetaE r Q X)) ∂Q with hMtr
    set L := ∫ X, sed_B d s ρ γ v X * Θ (zetaE r Q X) ∂Q with hL
    set A1 := ∑ l ∈ K, ∑ j ∈ K, q l j * gK l j with hA1
    set A2 := ∑ l ∈ K, ∑ j ∈ K, q l j * g l j with hA2
    set A3 := ∑' l, ∑' j, q l j * g l j with hA3
    have e : L - (1 / 2) * A3 = (L - Mtr) + (Mtr - (1 / 2) * A1) + (1 / 2) * (A1 - A2) +
        (1 / 2) * (A2 - A3) := by ring
    rw [e]
    have h4 : ∀ a b c e : ℝ, |a + b + c + e| ≤ |a| + |b| + |c| + |e| := fun a b c e => by
      calc |a + b + c + e| ≤ |a + b + c| + |e| := abs_add_le _ _
        _ ≤ |a| + |b| + |c| + |e| := by linarith [abs_add_three a b c]
    refine (h4 _ _ _ _).trans ?_
    have h5 : |(1 / 2 : ℝ) * (A1 - A2)| ≤ δ := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; linarith
    have h6 : |(1 / 2 : ℝ) * (A2 - A3)| ≤ δ := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_sub_comm]; linarith
    linarith
  have : 4 * δ = η := by rw [hδ]; ring
  rw [this] at hfinal
  exact hfinal

end HRS.MC.Sec7.S7d

end
