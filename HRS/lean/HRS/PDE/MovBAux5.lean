import HRS.PDE.MovBAux4

/-!
# MOVB, part 5: the limit `k → ∞` (`V_k → V` in `C²`)

`movb_smooth_approx` (value/gradient/Laplacian), `movb_exists_approx_solutions` (the level-`M` solutions `Y^k` for `D_k`,
Gronwall, narrow convergence of marginals), `movb_reg_ineq_pos` (the inequality for `V ∈ C²`, `0 < t ≤ T`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

theorem movb_smooth_approx {V : Torus d → ℝ} (hV : Torus.IsCk 2 V) :
    ∃ Vk : ℕ → Torus d → ℝ, (∀ k, Torus.IsSmooth (Vk k)) ∧
      (∀ k x, ‖Torus.grad (Vk k) x - Torus.grad V x‖ ≤ 1 / ((k : ℝ) + 1)) ∧
      (∀ k x, |Torus.laplacian (Vk k) x - Torus.laplacian V x| ≤ 1 / ((k : ℝ) + 1)) := by
  have h := fun k : ℕ => d1_exists_C2_approx (n := d) hV (ε := 1 / ((k : ℝ) + 1)) (by positivity)
  choose ψ hψs hψb using h
  refine ⟨ψ, hψs, fun k x => ?_, fun k x => ?_⟩
  · rw [norm_sub_rev]; exact (hψb k x).2.1
  · rw [abs_sub_comm]; exact (hψb k x).2.2

/-- The level-`M` solutions `Y^k` for the data `D_k = {D with V := V_k}` (same noise and initial value) converge to `Y`:
narrow convergence of all time marginals on `[0,T]`. -/
theorem movb_exists_approx_solutions {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hW' : IsBrownianFiltration P ℱ W') (D : DynData d) (hV : Torus.IsCk 2 D.V) (M : ℝ)
    {T : ℝ} (hT : 0 ≤ T) {Y₀ : Ω → Fin N → Euc d} (hY₀ : ∀ t : ℝ, Measurable[ℱ t] Y₀)
    {Y : ℝ → Ω → (Fin N → Euc d)}
    (hY : IsAdditiveSDESolution P ℱ W' (fun _ => b15c_liftedDriftReg D M) (liftedNoise D) Y₀
      (fun _ => ⊤) Y)
    (Vk : ℕ → Torus d → ℝ) (hVk : ∀ k, Torus.IsCk 2 (Vk k))
    (hVg : ∀ k x, ‖Torus.grad (Vk k) x - Torus.grad D.V x‖ ≤ 1 / ((k : ℝ) + 1)) :
    ∃ Yk : ℕ → ℝ → Ω → (Fin N → Euc d),
      (∀ k, IsAdditiveSDESolution P ℱ W' (fun _ => b15c_liftedDriftReg (b15e_withV D (Vk k)) M)
        (liftedNoise D) Y₀ (fun _ => ⊤) (Yk k)) ∧
      ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ φ : Config d N → ℝ, Continuous φ →
        Tendsto (fun k => ∫ x, φ x ∂(selectedLaw P (b15c_regProcess (Yk k)) r)) atTop
          (𝓝 (∫ x, φ x ∂(selectedLaw P (b15c_regProcess Y) r))) := by
  set ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hεdef
  have hεpos : ∀ k, 0 < ε k := fun k => by positivity
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set Dk : ℕ → DynData d := fun k => b15e_withV D (Vk k) with hDk
  choose Yk hYk using fun k => b15e_exists_regularised hW' (Dk k) (hVk k) M Y₀ hY₀
  refine ⟨Yk, hYk, ?_⟩
  obtain ⟨L, hL⟩ := (b15c_liftedDriftReg_isLipschitz_proof (N := N) D hV M).lip T
  have hLip : LipschitzWith L (b15c_liftedDriftReg (N := N) D M) := hL 0 ⟨le_rfl, hT⟩
  set δ : ℕ → ℝ := fun k => 2 * (ε k * T) * Real.exp ((2 * (L : ℝ) + 2) * T) with hδdef
  have hδ0 : Tendsto δ atTop (𝓝 0) := by
    have := (hε0.mul_const T).const_mul 2 |>.mul_const (Real.exp ((2 * (L : ℝ) + 2) * T))
    simpa [hδdef] using this
  have hstab : ∀ᵐ ω ∂P, ∀ k, ∀ s ∈ Set.Icc (0 : ℝ) T, ‖Yk k s ω - Y s ω‖ ≤ δ k := by
    rw [ae_all_iff]
    intro k
    have h := b15e_sde_stability (N := N) (d := d) hY (hYk k) hLip (ε := ε k) (hεpos k).le
      (fun y => b15e_liftedDriftReg_sub D (Vk k) M (hεpos k).le (hVg k) y) hT
    filter_upwards [h] with ω hω s hs
    refine (hω s hs).trans ?_
    have hexp : Real.exp ((2 * (L : ℝ) + 2) * s) ≤ Real.exp ((2 * (L : ℝ) + 2) * T) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hs.2 (by positivity))
    simp only [hδdef]
    exact mul_le_mul_of_nonneg_left hexp (by have := hεpos k; positivity)
  intro r hr φ hφ
  exact b15e_marginal_tendsto_unif (b := fun k => b15c_liftedDriftReg (Dk k) M)
    (b0 := b15c_liftedDriftReg D M) (σ := liftedNoise D) hYk hY hδ0 hstab hr.1 hr.2 hφ


theorem movb_slice_of_joint {T : ℝ} {S : ℝ → Config d N → ℝ}
    (hS : Continuous fun p : Set.Icc (0 : ℝ) T × Config d N => S p.1 p.2) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) T) : Continuous (S r) :=
  hS.comp (continuous_const.prodMk continuous_id : Continuous fun X : Config d N =>
    ((⟨r, hr⟩ : Set.Icc (0 : ℝ) T), X))

theorem movb_reg_ineq_pos (hN0 : 0 < N) (hNd : 1 ≤ N * d) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    (D : DynData d) (hM : D.M = -(1 : Matrix (Fin d) (Fin d) ℝ)) (hκ : 0 < D.invβ)
    (hV2 : Torus.IsCk 2 D.V) {T : ℝ} (hT : 0 < T) {ρ ρt : ℝ → Torus d → ℝ}
    (hρt : IsC12Test T ρ ρt) (hdens : ∀ r ∈ Set.Icc (0 : ℝ) T, IsProbDensity (ρ r))
    (hpos : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, 0 < ρ r x) (M : ℝ) {Y₀ : Ω → Fin N → Euc d}
    (hY₀ : ∀ t : ℝ, Measurable[ℱ t] Y₀) {Y : ℝ → Ω → (Fin N → Euc d)}
    (hY : IsAdditiveSDESolution P ℱ W' (fun _ => b15c_liftedDriftReg D M) (liftedNoise D) Y₀
      (fun _ => ⊤) Y)
    (hfin : relEntropy (selectedLaw P (b15c_regProcess Y) 0)
      (movT_Q (b15c_gReg d D.s M) D N ρ 0) ≠ ⊤) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    relEntropy (selectedLaw P (b15c_regProcess Y) t) (movT_Q (b15c_gReg d D.s M) D N ρ t) ≠ ⊤ ∧
      (relEntropy (selectedLaw P (b15c_regProcess Y) t) (movT_Q (b15c_gReg d D.s M) D N ρ t)).toReal ≤
        (relEntropy (selectedLaw P (b15c_regProcess Y) 0) (movT_Q (b15c_gReg d D.s M) D N ρ 0)).toReal +
        ∫ r in Set.Icc 0 t, ∫ Z, movT_srcReg D N M ρ ρt r Z ∂(selectedLaw P (b15c_regProcess Y) r) := by
  obtain ⟨Vk, hVs, hVg, hVl⟩ := movb_smooth_approx hV2
  have hVk2 : ∀ k, Torus.IsCk 2 (Vk k) := fun k => movb_isCk_of_smooth' (hVs k)
  obtain ⟨Yk, hYk, hmarg⟩ := movb_exists_approx_solutions hW' D hV2 M hT.le hY₀ hY Vk hVk2 hVg
  obtain ⟨C, hC0, hCdiff⟩ := movb_srcReg_withV_diff hN0 D hM hκ hV2 M hρt hpos
  set ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hεdef
  have hεpos : ∀ k, 0 < ε k := fun k => by positivity
  have hεle : ∀ k, ε k ≤ 1 := fun k => by
    rw [hεdef]; simp only
    rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have htT : t ≤ T := ht.2
  -- probability facts
  have hprobY : ∀ r : ℝ, IsProbabilityMeasure (selectedLaw P (b15c_regProcess Y) r) := fun r =>
    b15b_selectedLaw_isProb (fun s => b15c_regProcess_measurable hY s) r
  have hprobYk : ∀ k r, IsProbabilityMeasure (selectedLaw P (b15c_regProcess (Yk k)) r) := fun k r =>
    b15b_selectedLaw_isProb (fun s => b15c_regProcess_measurable (hYk k) s) r
  have hQprob : ∀ r ∈ Set.Icc (0 : ℝ) T,
      IsProbabilityMeasure (movT_Q (b15c_gReg d D.s M) D N ρ r) := fun r hr => by
    haveI : IsProbabilityMeasure (withDensityReal (ρ r)) := isProb_withDensityReal (hdens r hr)
    have hg : Continuous (b15c_gReg d D.s M) :=
      b15c_isSmooth_continuous (b15c_gReg_isSmooth (b15_one_le_d D) D.hs0 D.hsd M)
    exact modulatedGibbs_prob_of_continuous hg _ _
  -- the initial laws coincide
  have hP0 : ∀ k, selectedLaw P (b15c_regProcess (Yk k)) 0 = selectedLaw P (b15c_regProcess Y) 0 :=
    fun k => by rw [b15e_selectedLaw_zero_of_init (hYk k), b15e_selectedLaw_zero_of_init hY]
  -- the level-k inequalities
  have hlev : ∀ k, relEntropy (selectedLaw P (b15c_regProcess (Yk k)) t)
        (movT_Q (b15c_gReg d D.s M) D N ρ t) ≠ ⊤ ∧
      (relEntropy (selectedLaw P (b15c_regProcess (Yk k)) t)
        (movT_Q (b15c_gReg d D.s M) D N ρ t)).toReal ≤
        (relEntropy (selectedLaw P (b15c_regProcess Y) 0) (movT_Q (b15c_gReg d D.s M) D N ρ 0)).toReal +
        ∫ r in Set.Icc 0 t, ∫ Z, movT_srcReg (b15e_withV D (Vk k)) N M ρ ρt r Z
          ∂(selectedLaw P (b15c_regProcess (Yk k)) r) := by
    intro k
    have hfin_k : relEntropy (selectedLaw P (b15c_regProcess (Yk k)) 0)
        (movT_Q (b15c_gReg d (b15e_withV D (Vk k)).s M) (b15e_withV D (Vk k)) N ρ 0) ≠ ⊤ := by
      rw [hP0 k]; exact hfin
    have := movb_reg_ineq_smooth hNd hN0 hW' (b15e_withV D (Vk k)) hM hκ (hVs k) hT hρt hdens hpos M
      hY₀ (hYk k) hfin_k t ht
    rw [hP0 k] at this
    exact this
  -- joint continuity of the sources, and the continuity of r ↦ ∫ S_r dlaw_r
  have hSc : Continuous fun p : Set.Icc (0 : ℝ) T × Config d N => movT_srcReg D N M ρ ρt p.1 p.2 :=
    movb_srcReg_cont hN0 D hM hκ hV2 M hρt hdens hpos
  have hSkc : ∀ k, Continuous fun p : Set.Icc (0 : ℝ) T × Config d N =>
      movT_srcReg (b15e_withV D (Vk k)) N M ρ ρt p.1 p.2 := fun k =>
    movb_srcReg_cont hN0 (b15e_withV D (Vk k)) hM hκ (hVk2 k) M hρt hdens hpos
  set F : ℝ → ℝ := fun r => ∫ Z, movT_srcReg D N M ρ ρt r Z ∂(selectedLaw P (b15c_regProcess Y) r)
    with hFdef
  set Fk : ℕ → ℝ → ℝ := fun k r => ∫ Z, movT_srcReg (b15e_withV D (Vk k)) N M ρ ρt r Z
    ∂(selectedLaw P (b15c_regProcess (Yk k)) r) with hFkdef
  have hFc : ContinuousOn F (Set.Icc 0 T) := by
    rw [continuousOn_iff_continuous_restrict]
    exact movb_cont_integral hY hT.le hSc
  have hFkc : ∀ k, ContinuousOn (Fk k) (Set.Icc 0 T) := fun k => by
    rw [continuousOn_iff_continuous_restrict]
    exact movb_cont_integral (hYk k) hT.le (hSkc k)
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc_right htT
  -- bounds
  obtain ⟨B, hB⟩ := (isCompact_univ (X := Set.Icc (0 : ℝ) T × Config d N)).exists_bound_of_continuousOn
    hSc.continuousOn
  have hSk_le : ∀ k, ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ X : Config d N,
      |movT_srcReg (b15e_withV D (Vk k)) N M ρ ρt r X - movT_srcReg D N M ρ ρt r X| ≤ C * ε k :=
    fun k r hr X => hCdiff (Vk k) (hVk2 k) (ε k) (hεpos k).le (hVg k) (hVl k) r hr X
  -- pointwise convergence of Fk to F
  have hconv : ∀ r ∈ Set.Icc (0 : ℝ) T, Tendsto (fun k => Fk k r) atTop (𝓝 (F r)) := by
    intro r hr
    have hSr : Continuous (movT_srcReg D N M ρ ρt r) :=
      movb_slice_of_joint (S := movT_srcReg D N M ρ ρt) hSc hr
    have hSkr : ∀ k, Continuous (movT_srcReg (b15e_withV D (Vk k)) N M ρ ρt r) :=
      fun k => movb_slice_of_joint (S := movT_srcReg (b15e_withV D (Vk k)) N M ρ ρt) (hSkc k) hr
    have h1 := hmarg r hr _ hSr
    have hdiff : ∀ k, |Fk k r - ∫ Z, movT_srcReg D N M ρ ρt r Z
        ∂(selectedLaw P (b15c_regProcess (Yk k)) r)| ≤ C * ε k := by
      intro k
      haveI := hprobYk k r
      have hint : ∀ f : Config d N → ℝ, Continuous f →
          Integrable f (selectedLaw P (b15c_regProcess (Yk k)) r) := fun f hf =>
        hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      rw [← integral_sub (hint _ (hSkr k)) (hint _ hSr)]
      have := norm_integral_le_of_norm_le_const (μ := selectedLaw P (b15c_regProcess (Yk k)) r)
        (f := fun Z => movT_srcReg (b15e_withV D (Vk k)) N M ρ ρt r Z - movT_srcReg D N M ρ ρt r Z)
        (C := C * ε k) (Eventually.of_forall fun X => by
          rw [Real.norm_eq_abs]; exact hSk_le k r hr X)
      simpa using this
    have h2 : Tendsto (fun k => Fk k r - ∫ Z, movT_srcReg D N M ρ ρt r Z
        ∂(selectedLaw P (b15c_regProcess (Yk k)) r)) atTop (𝓝 0) := by
      have hz : Tendsto (fun k => C * ε k) atTop (𝓝 0) := by simpa using hε0.const_mul C
      exact squeeze_zero_norm (fun k => by rw [Real.norm_eq_abs]; exact hdiff k) hz
    have := h1.add h2
    simp only [add_zero] at this
    refine this.congr fun k => ?_
    ring
  -- bound on Fk
  have hFkb : ∀ k, ∀ r ∈ Set.Icc (0 : ℝ) T, ‖Fk k r‖ ≤ max B 0 + C := by
    intro k r hr
    haveI := hprobYk k r
    have := norm_integral_le_of_norm_le_const (μ := selectedLaw P (b15c_regProcess (Yk k)) r)
      (f := fun Z => movT_srcReg (b15e_withV D (Vk k)) N M ρ ρt r Z) (C := max B 0 + C)
      (Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs]
        have h1 := hSk_le k r hr X
        have h2 := hB (⟨r, hr⟩, X) (Set.mem_univ _)
        rw [Real.norm_eq_abs] at h2
        have h3 : C * ε k ≤ C := by nlinarith [hεle k, hC0]
        have := abs_sub_abs_le_abs_sub (movT_srcReg (b15e_withV D (Vk k)) N M ρ ρt r X)
          (movT_srcReg D N M ρ ρt r X)
        linarith [le_max_left B 0])
    simpa using this
  -- convergence of the time integrals
  have hJ : Tendsto (fun k => ∫ r in Set.Icc 0 t, Fk k r) atTop (𝓝 (∫ r in Set.Icc 0 t, F r)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => max B 0 + C)
      (fun k => ((hFkc k).mono hsub).aestronglyMeasurable measurableSet_Icc)
      (integrable_const _) (fun k => ?_) ?_
    · exact (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr =>
        hFkb k r (hsub hr))
    · exact (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr =>
        hconv r (hsub hr))
  -- the entropy side
  have hQt := hQprob t ht
  haveI := hprobY t
  haveI := hprobYk
  have hlsc : relEntropy (selectedLaw P (b15c_regProcess Y) t) (movT_Q (b15c_gReg d D.s M) D N ρ t) ≤
      liminf (fun k => relEntropy (selectedLaw P (b15c_regProcess (Yk k)) t)
        (movT_Q (b15c_gReg d D.s M) D N ρ t)) atTop := by
    unfold relEntropy
    exact b15b_klDiv_liminf_le (fun φ hφ => hmarg t ht φ hφ) (fun φ _ => tendsto_const_nhds)
  set H0 := (relEntropy (selectedLaw P (b15c_regProcess Y) 0)
    (movT_Q (b15c_gReg d D.s M) D N ρ 0)).toReal with hH0
  set y : ℕ → ℝ := fun k => H0 + ∫ r in Set.Icc 0 t, Fk k r with hy
  have hyk : ∀ k, 0 ≤ y k := fun k =>
    (ENNReal.toReal_nonneg).trans (hlev k).2
  have hle : ∀ k, relEntropy (selectedLaw P (b15c_regProcess (Yk k)) t)
      (movT_Q (b15c_gReg d D.s M) D N ρ t) ≤ ENNReal.ofReal (y k) := fun k => by
    rw [← ENNReal.ofReal_toReal (hlev k).1]
    exact ENNReal.ofReal_le_ofReal (hlev k).2
  have hy0 : Tendsto y atTop (𝓝 (H0 + ∫ r in Set.Icc 0 t, F r)) := tendsto_const_nhds.add hJ
  have hyinf : 0 ≤ H0 + ∫ r in Set.Icc 0 t, F r := ge_of_tendsto' hy0 hyk
  have hlim : Tendsto (fun k => ENNReal.ofReal (y k)) atTop
      (𝓝 (ENNReal.ofReal (H0 + ∫ r in Set.Icc 0 t, F r))) := ENNReal.tendsto_ofReal hy0
  have hfinal : relEntropy (selectedLaw P (b15c_regProcess Y) t) (movT_Q (b15c_gReg d D.s M) D N ρ t) ≤
      ENNReal.ofReal (H0 + ∫ r in Set.Icc 0 t, F r) := by
    refine hlsc.trans ?_
    rw [← hlim.liminf_eq]
    exact liminf_le_liminf (Eventually.of_forall hle)
  have hne : relEntropy (selectedLaw P (b15c_regProcess Y) t) (movT_Q (b15c_gReg d D.s M) D N ρ t) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfinal
  refine ⟨hne, ?_⟩
  have := (ENNReal.toReal_le_toReal hne ENNReal.ofReal_ne_top).2 hfinal
  rwa [ENNReal.toReal_ofReal hyinf] at this

end HRS
