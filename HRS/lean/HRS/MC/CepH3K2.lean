import HRS.MC.CepH3K1

/-!
# Packet CEPH3, part K2: uniform convergence of the regularised functionals and the lower bound for the cylinder Fisher information
-/


open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace
namespace HRS.MC.CepH3
open HRS HRS.MC.Cepa
noncomputable section
variable {N : ℕ} {J : ℝ → Ch N → Ch N} {Φn : ℝ → Ch N → ℝ} {Ψ : Ch N → ℝ} {L : ℝ≥0} {β : ℝ}

lemma h3k_gradUn_eq (h : H3 N β J Φn Ψ L) {n : ℝ} (hn : 0 < n) (z : Ch N) :
    gradient (fun w => Φn n w + Ψ w) z = n • (z - J n z) + gradient Ψ z := by
  have h1 := h.hΦ n z hn
  have h2 : HasGradientAt Ψ (gradient Ψ z) z := ((h.hΨ.differentiable (by norm_num)) z).hasGradientAt
  have h3 : HasGradientAt (fun w => Φn n w + Ψ w) (n • (z - J n z) + gradient Ψ z) z := by
    show HasFDerivAt _ (InnerProductSpace.toDual ℝ (Ch N) (n • (z - J n z) + gradient Ψ z)) z
    rw [map_add]
    exact h1.add h2
  exact h3.gradient

lemma h3k_gradUn_continuous (h : H3 N β J Φn Ψ L) {n : ℝ} (hn : 0 < n) :
    Continuous (gradient (fun w => Φn n w + Ψ w)) := by
  have : gradient (fun w => Φn n w + Ψ w) = fun z => n • (z - J n z) + gradient Ψ z :=
    funext (h3k_gradUn_eq h hn)
  rw [this]
  exact (h.hJ.lip n hn).continuous.add h.hΨL.continuous

theorem h3k_Fn_continuous [NeZero N] (h : H3 N β J Φn Ψ L) {n : ℝ} (hn : 0 < n) (σ₀ : Equiv.Perm (Fin N))
    {ζ : Config 1 N → (Fin N → Euc 1)} (hζ : IsFisherTestField ζ) (δ : ℝ) :
    Continuous (h3j_Fch β (fun w => Φn n w + Ψ w) (h3i_zt σ₀ ζ δ)) := by
  have hzt := h3i_zt_contDiff σ₀ hζ.smooth δ
  have hk : ∀ k : Fin N, Continuous fun z => fderiv ℝ (fun w => h3i_zt σ₀ ζ δ w k) z (EuclideanSpace.single k 1) := by
    intro k
    have hd : ContDiff ℝ ∞ (fun w => h3i_zt σ₀ ζ δ w k) :=
      (contDiff_piLp_apply (p := 2) (i := k)).comp hzt
    exact (hd.continuous_fderiv (by simp)).clm_apply continuous_const
  have hmid : Continuous fun z => inner ℝ (gradient (fun w => Φn n w + Ψ w) z) (h3i_zt σ₀ ζ δ z) :=
    (h3k_gradUn_continuous h hn).inner hzt.continuous
  unfold h3j_Fch
  refine ((continuous_const.mul (continuous_finset_sum _ fun k _ => hk k)).add (continuous_const.mul hmid)).sub ?_
  exact (hzt.continuous.norm).pow 2

theorem h3k_Fn_unif [NeZero N] {D : DynData 1} (h : H3 N D.invβ J Φn Ψ L) (σ₀ : Equiv.Perm (Fin N))
    {ζ : Config 1 N → (Fin N → Euc 1)} (hζ : IsFisherTestField ζ) {δ : ℝ} (hδ : 0 < δ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ cep_cell N,
      |h3j_Fch D.invβ (fun w => Φn n w + Ψ w) (h3i_zt σ₀ ζ δ) z - h3k_Finf D.invβ Ψ σ₀ ζ δ z| ≤ ε := by
  have hβ := h.hβ
  have hzt := h3i_zt_contDiff σ₀ hζ.smooth δ
  obtain ⟨C, hC⟩ := (h3k_S0_compact δ hδ).exists_bound_of_continuousOn hzt.continuous.norm.continuousOn
  set C' := max C 1 with hC'
  have hC'pos : 0 < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set ε' := ε * D.invβ / (2 * C') with hε'
  have hε'pos : 0 < ε' := by positivity
  obtain ⟨n₀, hn₀⟩ := h3b_G_unif h.hJ (h3k_S0_compact δ hδ) (h3k_S0_subset hδ) hε'pos
  filter_upwards [eventually_ge_atTop (max n₀ 1)] with n hn z hz
  have hn1 : (0 : ℝ) < n := by
    have : 1 ≤ n := le_trans (le_max_right _ _) hn
    exact_mod_cast this
  by_cases hz0 : h3i_zt σ₀ ζ δ z = 0
  · have : h3j_Fch D.invβ (fun w => Φn n w + Ψ w) (h3i_zt σ₀ ζ δ) z - h3k_Finf D.invβ Ψ σ₀ ζ δ z = 0 := by
      unfold h3k_Finf h3j_Fch
      rw [hz0]; simp
    rw [this]; simpa using hε.le
  · have hS : z ∈ h3i_Ssup δ := h3k_zt_ne_zero_mem hδ hz0
    have hS0 : z ∈ h3k_S0 δ := ⟨hS, hz.1, hz.2.le⟩
    have hA : z ∈ cep_Alcove N := h3k_S0_subset hδ hS0
    have hG := hn₀ n (le_trans (le_max_left _ _) hn) z hS0
    have hdiff : h3j_Fch D.invβ (fun w => Φn n w + Ψ w) (h3i_zt σ₀ ζ δ) z - h3k_Finf D.invβ Ψ σ₀ ζ δ z =
        2 * D.invβ⁻¹ * inner ℝ ((n : ℝ) • (z - J n z) - h3a_gam z) (h3i_zt σ₀ ζ δ z) := by
      unfold h3k_Finf h3j_Fch
      rw [h3k_gradUn_eq h hn1, h3k_gradU_eq h.hΨ hA, inner_sub_left, inner_add_left, inner_add_left]
      ring
    rw [hdiff, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * D.invβ⁻¹)]
    have h1 : |inner ℝ ((n : ℝ) • (z - J n z) - h3a_gam z) (h3i_zt σ₀ ζ δ z)| ≤ ε' * C' := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      have hCz : ‖h3i_zt σ₀ ζ δ z‖ ≤ C' := by
        have := hC z hS0
        rw [norm_norm] at this
        exact this.trans (le_max_left _ _)
      exact mul_le_mul hG hCz (norm_nonneg _) hε'pos.le
    calc 2 * D.invβ⁻¹ * |inner ℝ ((n : ℝ) • (z - J n z) - h3a_gam z) (h3i_zt σ₀ ζ δ z)|
        ≤ 2 * D.invβ⁻¹ * (ε' * C') := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ε := by rw [hε']; field_simp

lemma h3k_zt_far [NeZero N] {σ₀ : Equiv.Perm (Fin N)} {ζ : Config 1 N → (Fin N → Euc 1)} {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℝ, ∀ z, R ≤ Metric.infDist z (cep_Alcove N) → h3i_zt σ₀ ζ δ z = 0 := by
  refine ⟨1, fun z hz => ?_⟩
  by_contra hne
  have hA : z ∈ cep_Alcove N := h3i_Ssup_subset hδ (h3k_zt_ne_zero_mem hδ hne)
  have : Metric.infDist z (cep_Alcove N) = 0 := Metric.infDist_zero_of_mem hA
  linarith

theorem h3k_cylFisher_lower [NeZero N] {D : DynData 1} (h : H3 N D.invβ J Φn Ψ L) {σ₀ : Equiv.Perm (Fin N)}
    (hΨtot : ∀ (π : Equiv.Perm (Fin N)) (y : Fin N → Euc 1), cep_StrictlyOrdered π y →
      totalPotential D (fun i => Torus.mk (y i)) = cep_chamberPot 1 N (cep_toCh π y) + Ψ (cep_toCh π y))
    {ζ : Config 1 N → (Fin N → Euc 1)} (hζ : IsFisherTestField ζ) {δ : ℝ} (hδ : 0 < δ)
    (hev : ∀ z ∈ cep_Alcove N, ∀ᶠ w in 𝓝 z, h3i_zt σ₀ ζ δ w = h3i_za σ₀ ζ w) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ ν : Measure (Ch N), IsProbabilityMeasure ν → ν (cep_cell N)ᶜ = 0 →
      ENNReal.ofReal (∫ z, h3k_Finf D.invβ Ψ σ₀ ζ δ z ∂ν - ε) ≤
        cep_cylFisher D.invβ (fun w => Φn n w + Ψ w) ν := by
  obtain ⟨B, hB⟩ := h3k_Finf_bdd σ₀ h.hΨ h.hΨL hΨtot hζ hδ hev
  have hFc : Continuous (h3k_Finf D.invβ Ψ σ₀ ζ δ) := h3k_Finf_continuous σ₀ h.hΨ h.hΨL hζ hδ
  filter_upwards [h3k_Fn_unif h σ₀ hζ hδ hε, eventually_ge_atTop 1] with n hn hn1 ν hν hνc
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hFn := h3k_Fn_continuous h hn0 σ₀ hζ δ
  have hae : ∀ᵐ z ∂ν, z ∈ cep_cell N := by
    rw [ae_iff]; exact hνc
  have hint : Integrable (h3k_Finf D.invβ Ψ σ₀ ζ δ) ν :=
    Integrable.mono' (integrable_const B) hFc.aestronglyMeasurable (Eventually.of_forall fun z => by simpa using hB z)
  have hint_n : Integrable (h3j_Fch D.invβ (fun w => Φn n w + Ψ w) (h3i_zt σ₀ ζ δ)) ν := by
    refine Integrable.mono' (integrable_const (B + ε)) hFn.aestronglyMeasurable ?_
    filter_upwards [hae] with z hz
    have h1 := hn z hz
    have h2 := hB z
    rw [Real.norm_eq_abs]
    have := abs_sub_abs_le_abs_sub (h3j_Fch D.invβ (fun w => Φn n w + Ψ w) (h3i_zt σ₀ ζ δ) z)
      (h3k_Finf D.invβ Ψ σ₀ ζ δ z)
    linarith
  have hlow : ∫ z, h3k_Finf D.invβ Ψ σ₀ ζ δ z ∂ν - ε ≤
      ∫ z, h3j_Fch D.invβ (fun w => Φn n w + Ψ w) (h3i_zt σ₀ ζ δ) z ∂ν := by
    have hsub : ∫ z, (h3j_Fch D.invβ (fun w => Φn n w + Ψ w) (h3i_zt σ₀ ζ δ) z - h3k_Finf D.invβ Ψ σ₀ ζ δ z) ∂ν =
        ∫ z, h3j_Fch D.invβ (fun w => Φn n w + Ψ w) (h3i_zt σ₀ ζ δ) z ∂ν - ∫ z, h3k_Finf D.invβ Ψ σ₀ ζ δ z ∂ν :=
      integral_sub hint_n hint
    have hge : ∫ z, (-ε : ℝ) ∂ν ≤ ∫ z, (h3j_Fch D.invβ (fun w => Φn n w + Ψ w) (h3i_zt σ₀ ζ δ) z -
        h3k_Finf D.invβ Ψ σ₀ ζ δ z) ∂ν := by
      refine integral_mono_ae (integrable_const _) (hint_n.sub hint) ?_
      filter_upwards [hae] with z hz
      exact (abs_le.mp (hn z hz)).1
    simp at hge
    linarith
  refine (ENNReal.ofReal_le_ofReal hlow).trans ?_
  exact h3j_cylFisher_ge D.invβ _ ν _ (h3i_zt_contDiff σ₀ hζ.smooth δ) (h3i_zt_periodic σ₀ ζ δ)
    (h3k_zt_far hδ)

end
end HRS.MC.CepH3
