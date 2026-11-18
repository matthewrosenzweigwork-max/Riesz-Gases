import HRS.MC.CepE2PropsAux2

/-!
# Packet CEPE2PROPS: envelope properties of the Moreau envelopes and confinement of `Φ_n + Ψ`

`HRS.MC.CepE2Props.cep_E2_envelope_props_proof` has the statement of `HRS.MC.CepH4.cep_E2_envelope_props`
(duplicated vocabulary: `Ch`, `cep_Alcove`, `cep_chamberPot`, `cep_diag`, with the structure `cep_Yosida` repackaged in
the tie file).
-/

open Set Filter Topology
open scoped NNReal RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE2Props

open HRS.MC.CepE1 HRS.MC.CepE2

theorem cepe2p_gradLip {a : ℝ} (ha : 0 < a) {N : ℕ} {n : ℝ} (hn : 0 < n) :
    LipschitzWith (Real.toNNReal n) (fun z : Ch N => n • (z - cepe2_J ha n z)) := by
  refine LipschitzWith.of_dist_le_mul fun z z' => ?_
  rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hn,
    Real.coe_toNNReal _ hn.le]
  exact mul_le_mul_of_nonneg_left (cepe2_lip ha hn z z') hn.le

theorem cep_E2_envelope_props_proof (a : ℝ) (ha : 0 < a) (N : ℕ) [NeZero N] :
    ∃ (J : ℝ → Ch N → Ch N) (Φn : ℝ → Ch N → ℝ), cep_Yosida a N J ∧
      (∀ n z, 0 < n → HasGradientAt (Φn n) (n • (z - J n z)) z) ∧
      (∀ n z, 0 < n → z ∈ cep_Alcove N → Φn n z ≤ cep_chamberPot a N z) ∧
      (∀ z, z ∈ cep_Alcove N → Filter.Tendsto (fun n : ℕ => Φn n z) Filter.atTop (𝓝 (cep_chamberPot a N z))) ∧
      (∀ n z, 0 < n → Φn n (z + cep_diag N) = Φn n z) ∧
      (∀ n, 0 < n → ContDiff ℝ 1 (Φn n) ∧ LipschitzWith (Real.toNNReal n) (gradient (Φn n))) ∧
      (∃ C : ℝ, ∀ n z, 0 < n → n / 2 * Metric.infDist z (cep_Alcove N) ^ 2 - C ≤ Φn n z) := by
  have hgrad : ∀ n : ℝ, 0 < n → gradient (cepe2_env ha n : Ch N → ℝ) =
      fun z => n • (z - cepe2_J ha n z) :=
    fun n hn => funext fun z => (cepe2_env_hasGradient ha hn z).gradient
  refine ⟨fun n z => cepe2_J ha n z, fun n z => cepe2_env ha n z, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n z hn
    exact (cepe2_J_spec ha hn z).1
  · intro n z hn
    obtain ⟨hA, hF⟩ := cepe2_J_spec ha hn z
    rw [hF, cepe2_gradient_eq hA]
  · intro n hn
    exact cepe2p_gradLip ha hn
  · intro m n x y hm hn
    exact cepe2_yosida ha hm hn x y
  · intro n z hn
    exact cepe2_env_hasGradient ha hn z
  · intro n z hn hz
    exact cepe2_env_le ha hn hz
  · intro z hz
    exact cepe2_env_tendsto ha hz
  · intro n z hn
    have := cepe2p_env_add ha hn z 1
    simpa using this
  · intro n hn
    refine ⟨?_, ?_⟩
    · refine cepe2p_contDiff_of_hasGradientAt (g := fun z => n • (z - cepe2_J ha n z)) ?_
        fun z => cepe2_env_hasGradient ha hn z
      exact (cepe2p_gradLip ha hn).continuous
    · rw [hgrad n hn]
      exact cepe2p_gradLip ha hn
  · refine ⟨(a / N) * cepe2_npairs N * Real.log 2, fun n z hn => ?_⟩
    obtain ⟨hA, -⟩ := cepe2_J_spec ha hn z
    have h1 := cepe2_lower ha.le hA
    have h2 : Metric.infDist z (cep_Alcove N) ≤ ‖z - cepe2_J ha n z‖ := by
      rw [← dist_eq_norm]
      exact Metric.infDist_le_dist_of_mem hA
    have h3 : Metric.infDist z (cep_Alcove N) ^ 2 ≤ ‖z - cepe2_J ha n z‖ ^ 2 :=
      pow_le_pow_left₀ Metric.infDist_nonneg h2 2
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ n / 2)
    show _ ≤ cepe2_env ha n z
    rw [cepe2_env_eq ha hn]
    linarith

variable {N : ℕ}

theorem cep_H4_potential_conf_proof [NeZero N] {Ψ : Ch N → ℝ} {L : ℝ≥0} (hΨ : ContDiff ℝ 1 Ψ)
    (hΨL : LipschitzWith L (gradient Ψ)) (hΨper : ∀ z, Ψ (z + cep_diag N) = Ψ z)
    {Φn : ℝ → Ch N → ℝ} {C : ℝ}
    (hΦlow : ∀ n z, 0 < n → n / 2 * Metric.infDist z (cep_Alcove N) ^ 2 - C ≤ Φn n z) :
    ∀ n : ℝ, (L : ℝ) + 1 ≤ n → ∃ c C' : ℝ, 0 < c ∧
      ∀ z, c * Metric.infDist z (cep_Alcove N) ^ 2 - C' ≤ Φn n z + Ψ z := by
  intro n hn
  have hL0 : (0 : ℝ) ≤ L := L.coe_nonneg
  have hn0 : 0 < n := by linarith
  obtain ⟨B, hB0, hB⟩ := cepe2p_bound_alcove hΨ hΨL hΨper
  refine ⟨1 / 4, C + 2 * B + (L : ℝ) / 2 + (B + L) ^ 2, by norm_num, fun z => ?_⟩
  have hne : (cep_Alcove N).Nonempty := ⟨_, cepe2_base_mem⟩
  set d := Metric.infDist z (cep_Alcove N) with hd
  have hd0 : 0 ≤ d := Metric.infDist_nonneg
  obtain ⟨p, hpA, hpd⟩ := (Metric.infDist_lt_iff hne).1 (show d < d + 1 by linarith)
  obtain ⟨hΨp, hgp⟩ := hB p hpA
  set r := ‖z - p‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg _
  have hr1 : r ≤ d + 1 := by rw [hr, ← dist_eq_norm]; exact hpd.le
  have hdesc := cepe2p_descent hΨ hΨL p z
  have hin : |inner ℝ (gradient Ψ p) (z - p)| ≤ B * r :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hgp hr0)
  have hin' := neg_abs_le (inner ℝ (gradient Ψ p) (z - p))
  have hBr : B * r ≤ B * (d + 1) := mul_le_mul_of_nonneg_left hr1 hB0
  have hr2 : r ^ 2 ≤ (d + 1) ^ 2 := pow_le_pow_left₀ hr0 hr1 2
  have hLr : (L : ℝ) / 2 * r ^ 2 ≤ (L : ℝ) / 2 * (d + 1) ^ 2 :=
    mul_le_mul_of_nonneg_left hr2 (by positivity)
  have hΨz : -B - B * (d + 1) - (L : ℝ) / 2 * (d + 1) ^ 2 ≤ Ψ z := by
    have := neg_abs_le (Ψ p)
    linarith
  have hΦ := hΦlow n z hn0
  have h3 : ((L : ℝ) + 1) / 2 * d ^ 2 ≤ n / 2 * d ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg d)
  nlinarith [sq_nonneg (d / 2 - (B + L))]

end HRS.MC.CepE2Props
