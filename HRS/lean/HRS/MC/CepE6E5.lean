import HRS.MC.CepE5bAux10
import HRS.MC.CepE6DCut2
import HRS.MC.CepE6aA3

/-!
# Packet CEPE6E, file 5: pathwise Itô formula for the chamber solution, with the Itô isometry

For `g ∈ C²` with `‖Dg(x)‖ ≤ c₀ + c₁‖x‖` and a chamber solution `Z`, there is `M ∈ L²` (an Itô integral) with
`g(Z_t) = g(z₀) + ∫_0^t (Dg(Z)[B(Z)] + ½ σ'² ∑_k D²g(Z)[e_k,e_k]) ds + M` a.s., and `E M² = E ∫_0^t ∑_k |Dg(Z_s)[σ' e_k]|² ds`.
(This is the body of `e5b_ito_mean` without taking expectations.)
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE6E

open HRS HRS.MC.Cepa HRS.MC.CepE4 HRS.MC.CepE5b

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

theorem cepe6e_ito_pathwise [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {π : Ω → Equiv.Perm (Fin N)} (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ})
    {T σ' : ℝ} {Z : ℝ → Ω → Ch N} {A : Ω → ℝ}
    (S : E4Setup P ℱ N T σ' (cep_noise π W') Z A) (hT : 0 ≤ T)
    {z0 : Ω → Ch N} (hz0 : Measurable[ℱ 0] z0)
    {Bf : Ch N → Ch N} (hBc : Continuous Bf)
    (heq : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Z t ω = z0 ω + (∫ s in (0 : ℝ)..t, Bf (Z s ω)) + σ' • cep_noise π W' t ω)
    {g : Ch N → ℝ} (hg : ContDiff ℝ 2 g) {cg0 cg1 : ℝ} (hcg0 : 0 ≤ cg0) (hcg1 : 0 ≤ cg1)
    (hgrad : ∀ x, ‖fderiv ℝ g x‖ ≤ cg0 + cg1 * ‖x‖)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ∃ M : Ω → ℝ, MemLp M 2 P ∧
      (∀ᵐ ω ∂P, g (Z t ω) = g (z0 ω) + (∫ s in (0 : ℝ)..t, (fderiv ℝ g (Z s ω) (Bf (Z s ω)) +
          (1 / 2) * σ' ^ 2 * ∑ k : Fin N, fderiv ℝ (fderiv ℝ g) (Z s ω) (e5b_e k) (e5b_e k))) + M ω) ∧
      ∫⁻ ω, ‖M ω‖ₑ ^ 2 ∂P = ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) t,
        ∑ k : Fin N, ‖fderiv ℝ g (Z s ω) (σ' • e5b_e k)‖ₑ ^ 2) ∂P := by
  set dfun : Ch N → ℝ := fun x => fderiv ℝ g x (Bf x) +
    (1 / 2) * σ' ^ 2 * ∑ k : Fin N, fderiv ℝ (fderiv ℝ g) x (e5b_e k) (e5b_e k) with hdfun
  have hd : ∀ x, dfun x = fderiv ℝ g x (Bf x) +
      (1 / 2) * σ' ^ 2 * ∑ k : Fin N, fderiv ℝ (fderiv ℝ g) x (e5b_e k) (e5b_e k) := fun x => rfl
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

  refine ⟨itoIntegral P ℱ' (e5b_Wp π W') Ψ t, memLp_two_itoIntegral hB hΨ t, ?_, ?_⟩
  · filter_upwards [hmain] with ω h
    rw [h]
  · rw [lintegral_itoIntegral_sq hB hΨ t]
    unfold sqIntegralOn
    refine lintegral_congr fun ω => ?_
    refine setLIntegral_congr_fun measurableSet_Icc fun s hs => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans htT⟩
    simp only [hΨdef, itoIntegrand, Set.indicator, hsT, Set.mem_univ, if_true, Set.mem_setOf_eq]
    simp [ofNNRealTime, max_eq_left hs.1, hσ]

open HRS.MC.CepE6D in
/-- The sum of the second derivatives `∑_{k<l} χ''_ε(z_l - z_k)` (half the Laplacian of `g_ε`). -/
def lap2 (ε : ℝ) (z : Ch N) : ℝ :=
  ∑ k : Fin N, ∑ l : Fin N, if k < l then chi2 ε (z l - z k) else 0

open HRS.MC.CepE6D in
theorem lap2_continuous (ε : ℝ) : Continuous (lap2 (N := N) ε) := by
  unfold lap2
  refine continuous_finset_sum _ fun k _ => continuous_finset_sum _ fun l _ => ?_
  by_cases hkl : k < l
  · simp only [hkl, if_true]
    exact (chi2_contDiff ε).continuous.comp
      ((EuclideanSpace.proj l).continuous.sub (EuclideanSpace.proj k).continuous)
  · simp only [hkl, if_false]; exact continuous_const

open HRS.MC.CepE6D in
/-- Itô's formula for the cutoff functional `g_ε` along the regularised chamber solution `Z^n`:
the singular-force pairing `∫_0^T ⟨v_ε(Z^n), G_n(Z^n)⟩` equals boundary terms plus an `L²` martingale `M`. -/
theorem cepe6e_ito_gg [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {π : Ω → Equiv.Perm (Fin N)} (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ})
    {a : ℝ} {J : ℝ → Ch N → Ch N} (hJ : cep_Yosida a N J)
    {F : Ch N → Ch N} {L : ℝ≥0} (hF : LipschitzWith L F) (σ' : ℝ)
    {z₀ : Ω → Ch N} (hz₀ : Measurable[ℱ 0] z₀) (hz₀b : ∃ R : ℝ, ∀ ω, ‖z₀ ω‖ ≤ R)
    {Z : ℕ → ℝ → Ω → Ch N}
    (hZ : ∀ n : ℕ, 1 ≤ n → cep_IsChamberSolution P ℱ W' π σ'
      (fun z => -((n : ℝ) • (z - J n z)) + F z) z₀ (Z n))
    {n : ℕ} (hn : 1 ≤ n) {T : ℝ} (hT : 0 ≤ T) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 8) :
    ∃ M : Ω → ℝ, MemLp M 2 P ∧
      (∀ᵐ ω ∂P, ∫ s in (0 : ℝ)..T, ⟪vv ε (Z n s ω), (n : ℝ) • (Z n s ω - J n (Z n s ω))⟫ =
        gg ε (z₀ ω) - gg ε (Z n T ω) + (∫ s in (0 : ℝ)..T, ⟪vv ε (Z n s ω), F (Z n s ω)⟫) +
          σ' ^ 2 * (∫ s in (0 : ℝ)..T, lap2 ε (Z n s ω)) + M ω) ∧
      ∫⁻ ω, ‖M ω‖ₑ ^ 2 ∂P =
        ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) T, ENNReal.ofReal (σ' ^ 2 * ‖vv ε (Z n s ω)‖ ^ 2)) ∂P := by
  classical
  obtain ⟨R, hR⟩ := hz₀b
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hZc, hZF, heq⟩ := hZ n hn
  set G : Ch N → Ch N := fun z => (n : ℝ) • (z - J n z) with hG
  have hGlip := hJ.lip n hnpos
  have hGc : Continuous G := hGlip.continuous
  have hFc : Continuous F := hF.continuous
  have hGb : ∀ z, ‖G z‖ ≤ ‖G 0‖ + ((Real.toNNReal n : ℝ≥0) : ℝ) * ‖z‖ := fun z => e4_lip_growth hGlip z
  have hFb : ∀ z, ‖F z‖ ≤ ‖F 0‖ + (L : ℝ) * ‖z‖ := fun z => e4_lip_growth hF z
  have hBc : Continuous fun z => -G z + F z := hGc.neg.add hFc
  have hBb : ∀ z, ‖-G z + F z‖ ≤ (‖G 0‖ + ‖F 0‖) + (((Real.toNNReal n : ℝ≥0) : ℝ) + L) * ‖z‖ := fun z => by
    have h1 := norm_add_le (-G z) (F z)
    rw [norm_neg] at h1
    have h2 := hGb z
    have h3 := hFb z
    nlinarith
  obtain ⟨A, hS⟩ := e4_setup_of_solution hW' hπ (σ' := σ') hR hBc (by positivity) (by positivity) hBb
    (Z := Z n) hZc hZF heq hT
  have hS' : E4Setup P ℱ N T σ' (cep_noise π W') (e4_clamp (Z n)) A := hS
  have heq' : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → e4_clamp (Z n) t ω = z₀ ω +
      (∫ s in (0 : ℝ)..t, (-G (e4_clamp (Z n) s ω) + F (e4_clamp (Z n) s ω))) +
        σ' • cep_noise π W' t ω := by
    filter_upwards [heq] with ω hω t ht
    have e1 : e4_clamp (Z n) t ω = Z n t ω := by simp [e4_clamp, max_eq_left ht]
    rw [e1, hω t ht]
    congr 2
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le ht] at hs
    simp [e4_clamp, max_eq_left hs.1, hG]
  have hcalc := cepe6d_cutoff_calculus ε hε hε1 N
  have hgrad : ∀ x : Ch N, ‖fderiv ℝ (gg (N := N) ε) x‖ ≤ (N : ℝ) ^ 2 + 0 * ‖x‖ := by
    intro x
    rw [zero_mul, add_zero]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
    rw [fderiv_gg_apply]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hcalc.2.2.2.2.2.1 x) (norm_nonneg _))
  have hg2 : ContDiff ℝ 2 (gg (N := N) ε) := (gg_contDiff ε).of_le (by simp)
  obtain ⟨M, hM2, hM, hMiso⟩ := cepe6e_ito_pathwise hW' hπ hS' hT hz₀ hBc heq' hg2
    (cg0 := (N : ℝ) ^ 2) (cg1 := 0) (by positivity) le_rfl hgrad (t := T) hT le_rfl
  have hclamp : ∀ s : ℝ, 0 ≤ s → ∀ ω, e4_clamp (Z n) s ω = Z n s ω := fun s hs ω => by
    simp [e4_clamp, max_eq_left hs]
  refine ⟨M, hM2, ?_, ?_⟩
  · filter_upwards [hM] with ω hω
    have hZTc : e4_clamp (Z n) T ω = Z n T ω := hclamp T hT ω
    rw [hZTc] at hω
    have hpt : ∀ s ∈ Set.uIcc (0 : ℝ) T,
        (fderiv ℝ (gg ε) (e4_clamp (Z n) s ω) ((fun z => -G z + F z) (e4_clamp (Z n) s ω)) +
          (1 / 2) * σ' ^ 2 * ∑ k : Fin N, fderiv ℝ (fderiv ℝ (gg ε)) (e4_clamp (Z n) s ω) (e5b_e k) (e5b_e k)) =
        (-⟪vv ε (Z n s ω), G (Z n s ω)⟫ + ⟪vv ε (Z n s ω), F (Z n s ω)⟫) +
          σ' ^ 2 * lap2 ε (Z n s ω) := by
      intro s hs
      rw [Set.uIcc_of_le hT] at hs
      rw [hclamp s hs.1 ω, fderiv_gg_apply, inner_add_right, inner_neg_right]
      have h2 := hcalc.2.2.2.2.1 (Z n s ω)
      have h3 : ∑ k : Fin N, fderiv ℝ (fderiv ℝ (gg ε)) (Z n s ω) (e5b_e k) (e5b_e k) =
          2 * lap2 ε (Z n s ω) := h2
      rw [h3]; ring
    rw [intervalIntegral.integral_congr hpt] at hω
    have hc1 : Continuous fun s => ⟪vv ε (Z n s ω), G (Z n s ω)⟫ :=
      ((vv_contDiff (N := N) ε).continuous.comp (hZc ω)).inner (hGc.comp (hZc ω))
    have hc2 : Continuous fun s => ⟪vv ε (Z n s ω), F (Z n s ω)⟫ :=
      ((vv_contDiff (N := N) ε).continuous.comp (hZc ω)).inner (hFc.comp (hZc ω))
    have hc3 : Continuous fun s => lap2 ε (Z n s ω) := (lap2_continuous ε).comp (hZc ω)
    have hi1 : IntervalIntegrable (fun s => -⟪vv ε (Z n s ω), G (Z n s ω)⟫ +
        ⟪vv ε (Z n s ω), F (Z n s ω)⟫) volume 0 T := (hc1.neg.add hc2).intervalIntegrable 0 T
    have hi2 : IntervalIntegrable (fun s => σ' ^ 2 * lap2 ε (Z n s ω)) volume 0 T :=
      (hc3.const_mul (σ' ^ 2)).intervalIntegrable 0 T
    have hi3 : IntervalIntegrable (fun s => -⟪vv ε (Z n s ω), G (Z n s ω)⟫) volume 0 T :=
      hc1.neg.intervalIntegrable 0 T
    have hi4 : IntervalIntegrable (fun s => ⟪vv ε (Z n s ω), F (Z n s ω)⟫) volume 0 T :=
      hc2.intervalIntegrable 0 T
    rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_add hi3 hi4,
      intervalIntegral.integral_neg, intervalIntegral.integral_const_mul] at hω
    show ∫ s in (0 : ℝ)..T, ⟪vv ε (Z n s ω), G (Z n s ω)⟫ = _
    linarith
  · rw [hMiso]
    refine lintegral_congr fun ω => ?_
    refine setLIntegral_congr_fun measurableSet_Icc fun s hs => ?_
    rw [hclamp s hs.1 ω]
    have : ∀ k : Fin N, ‖fderiv ℝ (gg ε) (Z n s ω) (σ' • e5b_e k)‖ₑ ^ 2 =
        ENNReal.ofReal ((σ' * vv ε (Z n s ω) k) ^ 2) := by
      intro k
      rw [fderiv_gg_apply, real_inner_smul_right]
      simp [e5b_e, EuclideanSpace.inner_single_right, Real.enorm_eq_ofReal_abs]
      rw [← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_pow (mul_nonneg (abs_nonneg _) (abs_nonneg _)),
        ← abs_mul, sq_abs]
    simp_rw [this]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)]
    congr 1
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs, mul_pow]
    rw [← Finset.mul_sum]

end HRS.MC.CepE6E
