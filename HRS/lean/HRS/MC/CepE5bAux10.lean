import HRS.MC.CepE5bAux9
import HRS.MC.CepE5bAux6

/-!
# Packet CEPE5B, auxiliary 10: the expectation of Itô's formula along the chamber solution

For `g ∈ C²` with `‖Dg(x)‖ ≤ c₀ + c₁‖x‖`, `|g| ≲ 1 + ‖x‖²`, and a solution `Z_t = z₀ + ∫ Bf(Z) + σ' w_t` with
`w = cep_noise π W'` (the relabelled Brownian motion, an `ℱ`-Brownian motion for the filtration clamped at time `0`),
`E g(Z_t) = E g(z₀) + E ∫_0^t d(Z_s) ds`, `d = Dg·Bf + ½ σ'² ∑_k D²g(e_k, e_k)`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MC.CepE5b

open HRS HRS.MC.Cepa HRS.MC.CepE4

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

theorem e5b_sum_single (c : Fin N → ℝ) : ∑ k : Fin N, c k • (e5b_e k : Ch N) = WithLp.toLp 2 c := by
  ext j
  simp [e5b_e, Pi.single_apply]

theorem e5b_ito_mean [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {π : Ω → Equiv.Perm (Fin N)} (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ})
    {T σ' : ℝ} {Z : ℝ → Ω → Ch N} {A : Ω → ℝ}
    (S : E4Setup P ℱ N T σ' (cep_noise π W') Z A) (hT : 0 ≤ T)
    {z0 : Ω → Ch N} (hz0 : Measurable[ℱ 0] z0) {R : ℝ} (hR : ∀ ω, ‖z0 ω‖ ≤ R)
    {Bf : Ch N → Ch N} (hBc : Continuous Bf)
    (heq : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Z t ω = z0 ω + (∫ s in (0 : ℝ)..t, Bf (Z s ω)) + σ' • cep_noise π W' t ω)
    {g : Ch N → ℝ} (hg : ContDiff ℝ 2 g) {cg0 cg1 : ℝ} (hcg0 : 0 ≤ cg0) (hcg1 : 0 ≤ cg1)
    (hgrad : ∀ x, ‖fderiv ℝ g x‖ ≤ cg0 + cg1 * ‖x‖)
    {c0 c1 : ℝ} (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1) (hgb : ∀ x, |g x| ≤ c0 + c1 * ‖x‖ ^ 2)
    {dfun : Ch N → ℝ} (hdq : E4Quad dfun)
    (hd : ∀ x, dfun x = fderiv ℝ g x (Bf x) +
      (1 / 2) * σ' ^ 2 * ∑ k : Fin N, fderiv ℝ (fderiv ℝ g) x (e5b_e k) (e5b_e k))
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    Integrable (fun ω => g (Z t ω)) P ∧
    ∫ ω, g (Z t ω) ∂P = ∫ ω, g (z0 ω) ∂P + ∫ ω, (∫ s in (0 : ℝ)..t, dfun (Z s ω)) ∂P := by
  set ℱ' : Filtration ℝ mΩ := e5b_fil ℱ with hℱ'
  have hB : IsBrownianFiltration P ℱ' (e5b_Wp π W') := e5b_Wp_brownian hW' hπ
  set σ : Fin N → Ch N := fun k => σ' • e5b_e k with hσ
  -- progressive measurability of the path and the drift
  have hZad : Adapted ℱ' (fun s ω => Z (max s 0) ω) := fun s => S.ZF (max s 0) (le_max_right _ _)
  have hZc : ∀ ω, Continuous fun s : ℝ => Z (max s 0) ω := fun ω =>
    (S.Zc ω).comp (continuous_id.max continuous_const)
  have hZprog : IsProgressive ℱ' (fun s ω => Z (max s 0) ω) :=
    ((hZad.stronglyAdapted).isStronglyProgressive_of_continuous hZc).isProgressive
  have hXe : ofNNRealTime (fun (u : ℝ≥0) (ω : Ω) => Z (u : ℝ) ω) = fun s ω => Z (max s 0) ω := by
    funext s ω
    simp [ofNNRealTime, Real.coe_toNNReal']
  have hbe : ofNNRealTime (fun (u : ℝ≥0) (ω : Ω) => Bf (Z (u : ℝ) ω)) = fun s ω => Bf (Z (max s 0) ω) := by
    funext s ω
    simp [ofNNRealTime, Real.coe_toNNReal']
  have hXprog : IsProgressive ℱ' (ofNNRealTime (fun (u : ℝ≥0) (ω : Ω) => Z (u : ℝ) ω)) := by
    rw [hXe]; exact hZprog
  have hbprog : IsProgressive ℱ' (ofNNRealTime (fun (u : ℝ≥0) (ω : Ω) => Bf (Z (u : ℝ) ω))) := by
    rw [hbe]
    exact isProgressive_comp_measurable' (fun s ω => Z (max s 0) ω) hZprog (fun _ y => Bf y)
      (hBc.comp continuous_snd).measurable
  -- the Itô formula
  have hXmeas : ∀ u : ℝ≥0, Measurable (fun ω => Z (u : ℝ) ω) := fun u => S.Zm u
  have hX₀ : ∀ s : ℝ, Measurable[ℱ' s] (fun ω => Z ((0 : ℝ≥0) : ℝ) ω) := fun s => by
    have h0 : Measurable[ℱ 0] (Z 0) := S.ZF 0 le_rfl
    have : (fun ω => Z ((0 : ℝ≥0) : ℝ) ω) = Z 0 := by simp
    rw [this]
    exact h0.mono (e5b_fil_ge ℱ s) le_rfl
  have hbint : ∀ᵐ ω ∂P, IntegrableOn (fun s : ℝ => Bf (Z ((Real.toNNReal s : ℝ≥0) : ℝ) ω)) (Icc 0 T) := by
    refine Eventually.of_forall fun ω => ?_
    have : Continuous fun s : ℝ => Bf (Z ((Real.toNNReal s : ℝ≥0) : ℝ) ω) :=
      hBc.comp ((S.Zc ω).comp (NNReal.continuous_coe.comp continuous_real_toNNReal))
    exact this.continuousOn.integrableOn_Icc
  have hXeq : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, (u : ℝ) ≤ T →
      Z (u : ℝ) ω = Z ((0 : ℝ≥0) : ℝ) ω +
        (∫ s in Icc (0 : ℝ) (u : ℝ), Bf (Z ((Real.toNNReal s : ℝ≥0) : ℝ) ω)) +
        ∑ k, (e5b_Wp π W' u ω k - e5b_Wp π W' 0 ω k) • σ k := by
    filter_upwards [heq] with ω hω u hu
    have h1 := hω (u : ℝ) (NNReal.coe_nonneg u)
    have h0 := hω 0 le_rfl
    have hn0 : cep_noise π W' 0 ω = 0 := by
      ext k
      simp [cep_noise, hW'.zero]
    have hZ0 : Z ((0 : ℝ≥0) : ℝ) ω = z0 ω := by
      rw [NNReal.coe_zero, h0, hn0]
      simp
    rw [hZ0, h1]
    have hint : ∫ s in Icc (0 : ℝ) (u : ℝ), Bf (Z ((Real.toNNReal s : ℝ≥0) : ℝ) ω) =
        ∫ s in (0 : ℝ)..(u : ℝ), Bf (Z s ω) := by
      rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg u), integral_Icc_eq_integral_Ioc]
      refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
      rw [Real.coe_toNNReal _ hs.1.le]
    rw [hint]
    congr 1
    have hnoise : ∑ k, (e5b_Wp π W' u ω k - e5b_Wp π W' 0 ω k) • σ k = σ' • cep_noise π W' (u : ℝ) ω := by
      simp only [hσ, smul_comm _ σ', ← Finset.smul_sum]
      congr 1
      have := e5b_sum_single (N := N) (fun k => e5b_Wp π W' u ω k - e5b_Wp π W' 0 ω k)
      rw [this]
      ext k
      simp [cep_noise, e5b_Wp, hW'.zero]
    rw [hnoise]
  have hito := ito_formula_additive_time_independent (P := P) (ℱ := ℱ') hB hT g hg σ
    (fun (u : ℝ≥0) (ω : Ω) => Z (u : ℝ) ω) hXmeas hX₀ (fun (u : ℝ≥0) (ω : Ω) => Bf (Z (u : ℝ) ω))
    hbprog hbint hXeq
  have hΨ := e5b_progL2 S hT hg hcg0 hcg1 hgrad σ hXprog
  have hloc := localItoIntegral_eq_itoIntegral hB hΨ
  set Ψ := itoIntegrand T Set.univ (fun _ x => g x)
    (ofNNRealTime (fun (u : ℝ≥0) (ω : Ω) => Z (u : ℝ) ω)) (fun _ _ => σ) with hΨdef
  have hmain : ∀ᵐ ω ∂P, g (Z t ω) = g (z0 ω) + (∫ s in (0 : ℝ)..t, dfun (Z s ω)) +
      itoIntegral P ℱ' (e5b_Wp π W') Ψ t ω := by
    filter_upwards [hito, hloc, heq] with ω h1 h2 h3
    have hu : ((Real.toNNReal t : ℝ≥0) : ℝ) = t := Real.coe_toNNReal _ ht0
    have h := h1 (Real.toNNReal t) (by rw [hu]; exact htT)
    have hn0 : cep_noise π W' 0 ω = 0 := by
      ext k
      simp [cep_noise, hW'.zero]
    have hZ0 : Z ((0 : ℝ≥0) : ℝ) ω = z0 ω := by
      have h0 := h3 0 le_rfl
      rw [NNReal.coe_zero, h0, hn0]
      simp
    rw [hu, hZ0, h2 t] at h
    rw [h]
    congr 2
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by rw [← hu]; exact NNReal.coe_nonneg _)]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le ht0] at hs
    rw [Real.coe_toNNReal _ hs.1, hd]
    have hk : ∀ k, fderiv ℝ (fderiv ℝ g) (Z s ω) (σ k) (σ k) =
        σ' ^ 2 * fderiv ℝ (fderiv ℝ g) (Z s ω) (e5b_e k) (e5b_e k) := by
      intro k
      simp only [hσ, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    simp_rw [hk]
    rw [← Finset.mul_sum]
    ring
  have hΨint : Integrable (itoIntegral P ℱ' (e5b_Wp π W') Ψ t) P :=
    (memLp_two_itoIntegral hB hΨ t).integrable one_le_two
  have hz0m : Measurable z0 := hz0.mono (ℱ.le 0) le_rfl
  have hgz0 : Integrable (fun ω => g (z0 ω)) P := by
    refine Integrable.of_bound (C := c0 + c1 * R ^ 2) (hg.continuous.measurable.comp hz0m).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    have h1 : ‖z0 ω‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hR ω) 2
    have := hgb (z0 ω)
    nlinarith [mul_le_mul_of_nonneg_left h1 hc1]
  have hint2 := e4Q_int_inner S ht0 htT hdq
  have hA : Integrable (fun ω => g (z0 ω) + ∫ s in (0 : ℝ)..t, dfun (Z s ω)) P := hgz0.add hint2
  have hsum := hA.add hΨint
  have hI : Integrable (fun ω => g (Z t ω)) P := hsum.congr (hmain.mono fun ω h => h.symm)
  refine ⟨hI, ?_⟩
  rw [integral_congr_ae hmain, integral_add hA hΨint, integral_add hgz0 hint2,
    integral_itoIntegral hB hΨ t]
  simp

end HRS.MC.CepE5b
