import HRS.Appendix.B15EAux6

/-!
# Packet B15E, part 7: Stage 1 for `V ∈ C²`

`b15e_regularised_entropy`: for `V ∈ C²` and any global solution `Y` of the level-`M` regularised SDE,
`𝓗_{U^M}(P^t) + invβ ∫_0^t 𝓘_{U^M}(P^r) dr ≤ 𝓗_{U^M}(P^0)`.  Proof: smooth approximants `V_k ≤ V`,
solutions `Y^k` for `D_k = {D with V := V_k}`, the smooth inequality `b15e_reg_ineq_smooth` for each `k`,
`𝓗_{U_k^M}(P^0) ≤ 𝓗_{U^M}(P^0)` (`U_k^M ≤ U^M`), Gronwall convergence `Y^k → Y`, lower semicontinuity.
-/

noncomputable section

open MeasureTheory InformationTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

theorem b15e_regularised_entropy (hNd : 1 ≤ N * d) (D : DynData d) (hβ : 0 < D.invβ)
    (hM : D.M = -(1 : Matrix (Fin d) (Fin d) ℝ)) (hV : Torus.IsCk 2 D.V) (M : ℝ)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ' : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hW' : IsBrownianFiltration P ℱ' W') {Y₀ : Ω → Fin N → Euc d}
    (hY₀ : ∀ t : ℝ, Measurable[ℱ' t] Y₀) {Y : ℝ → Ω → Fin N → Euc d}
    (hY : IsAdditiveSDESolution P ℱ' W' (fun _ => b15c_liftedDriftReg D M) (liftedNoise D) Y₀
      (fun _ => ⊤) Y)
    {T : ℝ} (hT : 0 < T)
    (hfin : b15c_gibbsEntropyGen D.invβ (b15c_potentialReg D M)
      (selectedLaw P (b15c_regProcess Y) 0) < ⊤) :
    ∀ t ∈ Set.Icc 0 T,
      b15c_gibbsEntropyGen D.invβ (b15c_potentialReg D M) (selectedLaw P (b15c_regProcess Y) t)
        + ((ENNReal.ofReal D.invβ * ∫⁻ r in Set.Icc (0 : ℝ) t, b15_fisherInfoGen D.invβ
            (b15c_potentialReg D M) (selectedLaw P (b15c_regProcess Y) r) : ℝ≥0∞) : EReal)
      ≤ b15c_gibbsEntropyGen D.invβ (b15c_potentialReg D M) (selectedLaw P (b15c_regProcess Y) 0) := by
  intro t ht
  have hVc := b15_continuous_of_isCk hV
  obtain ⟨Vk, hVs, hVle, hVge, hVg⟩ := b15e_smooth_approx_below hV
  set ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hεdef
  have hεpos : ∀ k, 0 < ε k := fun k => by positivity
  have hεle : ∀ k, ε k ≤ 1 := fun k => by
    rw [hεdef]; simp only
    rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set Dk : ℕ → DynData d := fun k => b15e_withV D (Vk k) with hDk
  have hVk2 : ∀ k, Torus.IsCk 2 (Dk k).V := fun k => b15e_isCk_of_isSmooth (hVs k)
  -- the regularised solutions for `D_k`
  choose Yk hYk using fun k => b15e_exists_regularised hW' (Dk k) (hVk2 k) M Y₀ hY₀
  -- Gronwall: Y^k → Y uniformly on [0,T]
  obtain ⟨L, hL⟩ := (b15c_liftedDriftReg_isLipschitz_proof (N := N) D hV M).lip T
  have hLip : LipschitzWith L (b15c_liftedDriftReg (N := N) D M) := hL 0 ⟨le_rfl, hT.le⟩
  set δ : ℕ → ℝ := fun k => 2 * (ε k * T) * Real.exp ((2 * (L : ℝ) + 2) * T) with hδdef
  have hδ0 : Tendsto δ atTop (𝓝 0) := by
    have := (hε0.mul_const T).const_mul 2 |>.mul_const (Real.exp ((2 * (L : ℝ) + 2) * T))
    simpa [hδdef] using this
  have hstab : ∀ᵐ ω ∂P, ∀ k, ∀ s ∈ Set.Icc (0 : ℝ) T, ‖Yk k s ω - Y s ω‖ ≤ δ k := by
    rw [ae_all_iff]
    intro k
    have h := b15e_sde_stability (N := N) (d := d) hY (hYk k) hLip (ε := ε k) (hεpos k).le
      (fun y => b15e_liftedDriftReg_sub D (Vk k) M (hεpos k).le (hVg k) y) hT.le
    filter_upwards [h] with ω hω s hs
    refine (hω s hs).trans ?_
    have hexp : Real.exp ((2 * (L : ℝ) + 2) * s) ≤ Real.exp ((2 * (L : ℝ) + 2) * T) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hs.2 (by positivity))
    simp only [hδdef]
    exact mul_le_mul_of_nonneg_left hexp (by have := hεpos k; positivity)
  -- potentials
  set U : Config d N → ℝ := b15c_potentialReg (N := N) D M with hUdef
  set Uk : ℕ → Config d N → ℝ := fun k => b15c_potentialReg (N := N) (Dk k) M with hUkdef
  have hUc : Continuous U := b15c_potentialReg_continuous D hVc M
  have hUkc : ∀ k, Continuous (Uk k) := fun k =>
    b15c_potentialReg_continuous (Dk k) (b15_continuous_of_isCk (hVk2 k)) M
  have hUk_eq : ∀ k, Uk k = fun X => U X + ∑ i, (Vk k - D.V) (X i) := fun k =>
    b15e_potentialReg_withV D (Vk k) M
  have hUk_le : ∀ k X, Uk k X ≤ U X := by
    intro k X
    rw [hUk_eq k]
    have : ∑ i, (Vk k - D.V) (X i) ≤ 0 :=
      Finset.sum_nonpos fun i _ => by simp only [Pi.sub_apply]; linarith [hVle k (X i)]
    linarith
  have hUk_diff : ∀ k X, |Uk k X - U X| ≤ (N : ℝ) * (2 * ε k) := by
    intro k X
    rw [hUk_eq k]
    simp only [add_sub_cancel_left]
    calc |∑ i, (Vk k - D.V) (X i)| ≤ ∑ i, |(Vk k - D.V) (X i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, 2 * ε k := by
          refine Finset.sum_le_sum fun i _ => ?_
          simp only [Pi.sub_apply]
          rw [abs_le]
          constructor <;> linarith [hVle k (X i), hVge k (X i)]
      _ = (N : ℝ) * (2 * ε k) := by simp
  -- marginals
  have hprobY : ∀ r : ℝ, IsProbabilityMeasure (selectedLaw P (b15c_regProcess Y) r) := fun r =>
    b15b_selectedLaw_isProb (fun s => b15c_regProcess_measurable hY s) r
  have hprobYk : ∀ k r, IsProbabilityMeasure (selectedLaw P (b15c_regProcess (Yk k)) r) := fun k r =>
    b15b_selectedLaw_isProb (fun s => b15c_regProcess_measurable (hYk k) s) r
  have hmarg : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ φ : Config d N → ℝ, Continuous φ →
      Tendsto (fun k => ∫ x, φ x ∂(selectedLaw P (b15c_regProcess (Yk k)) r)) atTop
        (𝓝 (∫ x, φ x ∂(selectedLaw P (b15c_regProcess Y) r))) := fun r hr φ hφ =>
    b15e_marginal_tendsto_unif (b := fun k => b15c_liftedDriftReg (Dk k) M)
      (b0 := b15c_liftedDriftReg D M) (σ := liftedNoise D) hYk hY hδ0 hstab hr.1 (hr.2.trans ht.2) hφ
  -- entropy lower semicontinuity
  obtain ⟨B0, hB0⟩ := (isCompact_univ (X := Config d N)).exists_bound_of_continuousOn hUc.continuousOn
  have hH : b15c_gibbsEntropyGen D.invβ U (selectedLaw P (b15c_regProcess Y) t) ≤
      liminf (fun k => b15c_gibbsEntropyGen D.invβ (Uk k) (selectedLaw P (b15c_regProcess (Yk k)) t))
        atTop := by
    haveI := hprobY t
    haveI := hprobYk
    refine b15e_gibbsEntropyGen_liminf_le (B := B0 + (N : ℝ) * 2) hβ hUc hUkc (fun k X => ?_)
      (fun X => ?_) (hmarg t ⟨ht.1, le_rfl⟩)
    · have h1 := hB0 X (mem_univ _)
      rw [Real.norm_eq_abs] at h1
      have h2 := hUk_diff k X
      have h3 : (N : ℝ) * (2 * ε k) ≤ (N : ℝ) * 2 := by
        have := hεle k; have : (0:ℝ) ≤ N := Nat.cast_nonneg N; nlinarith
      calc |Uk k X| = |U X + (Uk k X - U X)| := by ring_nf
        _ ≤ |U X| + |Uk k X - U X| := abs_add_le _ _
        _ ≤ _ := by linarith
    · have h0 : Tendsto (fun k => (N : ℝ) * (2 * ε k)) atTop (𝓝 0) := by
        simpa using (hε0.const_mul 2).const_mul (N : ℝ)
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) h0
      rw [Real.norm_eq_abs]; exact hUk_diff k X
  -- Fisher information
  have hcontU : ∀ ζ, IsFisherTestField ζ → Continuous (b15c_fisherIntegrand D.invβ U ζ) :=
    fun ζ hζ => b15b_fisherIntegrand_continuous_proof _ (b15b_potentialReg_c1 D hV M) hζ
  have hcontUk : ∀ k ζ, IsFisherTestField ζ → Continuous (b15c_fisherIntegrand D.invβ (Uk k) ζ) :=
    fun k ζ hζ => b15b_fisherIntegrand_continuous_proof _ (b15b_potentialReg_c1 (Dk k) (hVk2 k) M) hζ
  have hdiffU : Differentiable ℝ (fun Z : Fin N → Euc d => U (fun i => Torus.mk (Z i))) :=
    (b15c_potentialReg_contDiff D (n := 1) (by exact_mod_cast le_top)
      (ContDiff.of_le hV (by norm_num)) M).differentiable (by norm_num)
  have hunif : ∀ ζ, IsFisherTestField ζ → ∀ ε' > 0, ∀ᶠ k in atTop, ∀ X,
      |b15c_fisherIntegrand D.invβ (Uk k) ζ X - b15c_fisherIntegrand D.invβ U ζ X| ≤ ε' := by
    intro ζ hζ ε' hε'
    obtain ⟨Cζ, hCζ0, hCζ⟩ := b15e_testField_bounded hζ
    have h0 : Tendsto (fun k => 2 * |D.invβ⁻¹| * ((N : ℝ) * (ε k * Cζ))) atTop (𝓝 0) := by
      simpa using (((hε0.mul_const Cζ).const_mul (N : ℝ)).const_mul (2 * |D.invβ⁻¹|))
    filter_upwards [h0.eventually (ge_mem_nhds hε')] with k hk X
    have hg : Differentiable ℝ (Torus.lift (Vk k - D.V)) := by
      have h1 : ContDiff ℝ 2 (Torus.lift (Vk k)) := hVk2 k
      have h2 : ContDiff ℝ 2 (Torus.lift D.V) := hV
      exact (h1.sub h2).differentiable (by norm_num)
    have hgrad : ∀ x, ‖Torus.grad (Vk k - D.V) x‖ ≤ ε k := by
      intro x
      have h1 : ContDiff ℝ 2 (Torus.lift (Vk k)) := hVk2 k
      have h2 : ContDiff ℝ 2 (Torus.lift D.V) := hV
      have e : Torus.grad (Vk k - D.V) x = Torus.grad (Vk k) x - Torus.grad D.V x := by
        unfold Torus.grad gradient
        have : Torus.lift (Vk k - D.V) = Torus.lift (Vk k) - Torus.lift D.V := rfl
        rw [this, fderiv_sub (h1.differentiable (by norm_num) _) (h2.differentiable (by norm_num) _),
          map_sub]
      rw [e]; exact hVg k x
    have := b15e_fisherIntegrand_sub (invβ := D.invβ) hdiffU (Vk k - D.V) hg hgrad ζ hCζ X
    rw [hUk_eq k]
    exact this.trans hk
  have hI : ∫⁻ r in Set.Icc (0 : ℝ) t, b15_fisherInfoGen D.invβ U (selectedLaw P (b15c_regProcess Y) r) ≤
      liminf (fun k => ∫⁻ r in Set.Icc (0 : ℝ) t, b15_fisherInfoGen D.invβ (Uk k)
        (selectedLaw P (b15c_regProcess (Yk k)) r)) atTop := by
    refine b15e_lintegral_liminf_le (fun r hr => ?_) (fun k => ?_)
    · haveI := hprobYk
      exact b15e_fisherInfoGen_liminf_le_unif D.invβ hcontU hcontUk hunif (hmarg r hr)
    · exact (b15e_measurable_fisherInfoGen_reg (hVk2 k) M (T := T) (hYk k)).mono_measure
        (Measure.restrict_mono (Set.Icc_subset_Icc_right ht.2) le_rfl)
  have hP0 : ∀ k, selectedLaw P (b15c_regProcess (Yk k)) 0 = selectedLaw P (b15c_regProcess Y) 0 :=
    fun k => by rw [b15e_selectedLaw_zero_of_init (hYk k), b15e_selectedLaw_zero_of_init hY]
  have := hprobY 0
  have hreg : ∀ k, b15c_gibbsEntropyGen D.invβ (Uk k) (selectedLaw P (b15c_regProcess (Yk k)) t)
      + ((ENNReal.ofReal D.invβ * ∫⁻ r in Set.Icc (0 : ℝ) t, b15_fisherInfoGen D.invβ (Uk k)
          (selectedLaw P (b15c_regProcess (Yk k)) r) : ℝ≥0∞) : EReal)
      ≤ b15c_gibbsEntropyGen D.invβ U (selectedLaw P (b15c_regProcess Y) 0) := by
    intro k
    have hfin_k : b15c_gibbsEntropyGen D.invβ (Uk k) (selectedLaw P (b15c_regProcess (Yk k)) 0) < ⊤ := by
      rw [hP0 k]
      exact lt_of_le_of_lt (b15e_gibbsEntropyGen_mono hβ (hUkc k) hUc (hUk_le k) _) hfin
    have h := b15e_reg_ineq_smooth hNd (Dk k) hβ hM (hVs k) M hW' hY₀ (hYk k) hT hfin_k t ht
    refine h.trans ?_
    rw [hP0 k]
    exact b15e_gibbsEntropyGen_mono hβ (hUkc k) hUc (hUk_le k) _
  exact b15e_limit_core hH hI hreg

end HRS
