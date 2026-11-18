import HRS.MS.WsStatAux37
import HRS.MS.WsStatTie
import HRS.Main.Headline

/-!
# S21 packet K-5: `S21Main` from the initial-path input `S21Init`

`s21_main_of_init`: given `S21Init d s a beta T` (packets G, H: the initial path), the path estimates `S21Main` of S2.1 (i) hold for
every `C0 >=` a threshold, with a constant `C`.  This is the assembly of packets A-F, I, J, K:
the filtered modification (`s21f_filtered`), the centred remainder, the master comparison (`s21_master_Z`) with the scaled Gaussian
process `sqrt beta Z`, the rate algebra (packet B) and the `beta^{-1/2}` scaling back to `zeta = sqrt N (mu_N - m_N)`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MS.S21

open HRS.Whole HRS.MS.GenPath HRS.MP.RdRem HRS.GF HRS.Uniform HRS.Whole.AppendixA
open HRS (Euc)

variable {d : ℕ}

set_option maxHeartbeats 2000000 in
theorem s21_main_of_init (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) {T : ℝ} (hT : 0 < T) (hinit : S21Init d s a β T hT.le) :
    ∃ C₀thr : ℝ, ∀ C₀ : ℝ, C₀thr ≤ C₀ → ∃ C : ℝ, HRS.Whole.S21Main d s a β T C₀ C := by
  classical
  by_cases hex : ∃ ρ₁ : Euc d → ℝ, IsThermalEquilibrium d s a β ρ₁
  swap
  · exact ⟨0, fun C₀ _ => ⟨0, fun ρβ hρβ => absurd ⟨ρβ, hρβ⟩ hex⟩⟩
  obtain ⟨ρ₁, h₁⟩ := hex
  obtain ⟨θ, Λ, K, hθ, hvalid, C₀thr, hthr0, hS⟩ := s21_setup_family hd hs0 hsd ha hβ hT h₁
  obtain ⟨C₀t, hTrAll⟩ := s56_trace_moment' (s21Bounds d s a β T θ Λ K 0) hvalid
  refine ⟨max (max C₀thr C₀t) 1, fun C₀ hC₀ => ?_⟩
  have hC₀1 : 1 ≤ C₀ := (le_max_right _ _).trans hC₀
  have hC₀pos : 0 < C₀ := by linarith
  have hC₀thr : C₀thr ≤ C₀ := ((le_max_left _ _).trans (le_max_left _ _)).trans hC₀
  have hC₀t : C₀t ≤ C₀ := ((le_max_right _ _).trans (le_max_left _ _)).trans hC₀
  set b : WholeBounds d := s21Bounds d s a β T θ Λ K C₀ with hbdef
  obtain ⟨S, hρ', hinv', hκ', hCadj⟩ := hS C₀ hC₀thr
  have hbeq : b = { s21Bounds d s a β T θ Λ K 0 with C₀ := b.C₀ } := s21Bounds_eq s a β T θ Λ K C₀
  have hbv : b.Valid := s56_valid_of_eq hvalid hbeq
  have hT0 : 0 ≤ b.T := hbv.hT.le
  obtain ⟨Ctr', hCtr0, hTr⟩ := hTrAll b hbeq hC₀t
  obtain ⟨Ctr, Cmax, hOMall⟩ := HRS.MS.Star.general_orbits_maximal_proof b hbv
  obtain ⟨Cs, Cw1, Cw2, hCs0, hCw10, hCw20, hCmp⟩ := s56_compare' (d := d) b.m b.T hT0
  obtain ⟨Kε, hKε0, hKε⟩ := s21_energy_integral_stationary hd hs0 hsd ha hβ
  obtain ⟨M₂, hM₂0, hM₂ρ, hM₂mom⟩ := s21_second_moment_stationary hd hs0 hsd ha hβ
  obtain ⟨CT, hCT⟩ := s21_centered_remainder hd hs0 hsd ha hβ hT.le
  obtain ⟨CA, hCA⟩ := s21_var_hyp hd hs0 hsd ha hβ
  obtain ⟨Cg, hCg0, hCg⟩ := s21_glr_le_loc (s := s) (C₀ := C₀) (K₁ := 3 * Kε + 1) (M₂ := M₂)
    (by omega : 1 ≤ d) hs0 hsd hC₀pos (by positivity) hM₂0
  have hinit' : S21InitAt d s a β b.T b.m hT0 := hinit
  obtain ⟨Ci, hCi0, hInit⟩ := hinit'
  obtain ⟨bO, KO, G0, G1, G2, hOrb⟩ := s21_orbit_data hd hs0 hsd ha hβ hT.le h₁
  -- the constants
  set CT' : ℝ := max CT 0 with hCT'
  have hCT'0 : 0 ≤ CT' := le_max_right _ _
  have hc1 : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  set Csm : ℝ := max 1 β⁻¹ * (Cs * Ctr' * Cg + Real.sqrt β * CT' + max 1 β * Ci) with hCsm
  set Cw : ℝ := (Real.sqrt β)⁻¹ * (Cw1 * Real.sqrt (Ctr' * Cg) + Real.sqrt β * CT' + Real.sqrt β * Ci) with hCw
  refine ⟨max Csm Cw, ?_⟩
  intro ρβ hρβ N hN hInv Ω mΩ P hP X₀ W X hBr hInd hlaw0 hstrong Ω' mΩ' P' hP' Z hZ
  have hρeq : ρβ = ρ₁ := (HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρβ).trans
    (HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ h₁).symm
  rw [hρeq] at hZ
  have hd1 : 1 ≤ d := by omega
  have hm : (d : ℝ) < b.m := (s21_dm b hbv).2
  have hN1 : 1 ≤ N := by omega
  set Gibbs := HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β with hGibbs
  have hlawt : ∀ t : ℝ≥0, (t : ℝ) ≤ T → law P (X t) = Gibbs := hInv P T X₀ W X hBr hInd hlaw0 hstrong
  have hX0m : Measurable (X 0) := hstrong.adapted 0
  have hlaw00 : P.map (X 0) = Gibbs := hlawt 0 (by simpa using hT.le)
  haveI hGp : IsProbabilityMeasure Gibbs := by
    rw [← hlaw00]
    exact (Measure.isProbabilityMeasure_map_iff hX0m.aemeasurable).2 inferInstance
  -- the filtered modification
  have hdistinct : ∀ᵐ ζ ∂P, X 0 ζ ∉ eucCollisionSet d N := by
    filter_upwards [hstrong.no_collision] with ζ h
    exact h 0 (by simpa using hT.le)
  have hindep0 : IndepFun (X 0) (fun ζ t => W t ζ) P :=
    IndepFun.congr hInd (hstrong.init.mono fun ζ h => h.symm) Filter.EventuallyEq.rfl
  have hS0 : IsWholeStrongSolution P (quadraticGradientDyn d s a β) T (X 0) W X :=
    { hstrong with init := Filter.Eventually.of_forall fun _ => rfl }
  obtain ⟨X', ℱ, W', hmod, hX's, hF'⟩ := s21f_filtered hd1 s a β N hN T hT P (X 0) W X hX0m hdistinct hBr
    hindep0 hS0
  have hlawt' : ∀ t : ℝ≥0, (t : ℝ) ≤ T → law P (X' t) = Gibbs := fun t ht => by
    rw [← hlawt t ht]
    exact Measure.map_congr (hmod t ht)
  have hX'm : ∀ t, Measurable (X' t) := hX's.adapted
  have hNpos : 0 < N := by omega
  -- the setup facts
  have hσ := s21_sigma_eq b S hβ hinv' hN1 (hκ' N hN1)
  have hσ2 : S.σ N = Real.sqrt N * Real.sqrt β := by
    rw [hσ.1, Real.sqrt_mul (Nat.cast_nonneg N)]
  have hq1 : S.q N = 1 := hσ.2
  have hdyn : S.dyn N = quadraticGradientDyn d s a β := s21_dyn_setup S hinv' N
  have hX'sS : IsWholeStrongSolution P (S.dyn N) b.T (X 0) W X' := by rw [hdyn]; exact hX's
  have hC := hCadj N
  have hM1 : b.M = -1 := rfl
  have hcoeff : S.coeff N = (⟨s, -1, quadV (a • (1 : Matrix (Fin d) (Fin d) ℝ)) 0, β⁻¹⟩ : WholeDyn d).coeff
      (fun _ => ρ₁) := s21_coeff_setup S hρ' hinv' N
  have hcoeff2 : (quadraticGradientDyn d s a β).coeff (fun _ => ρ₁) = S.coeff N := by
    rw [hcoeff, s21_dyn_eq]
  have hstat : ∀ t ∈ Set.Icc (0 : ℝ) b.T, P.map (X' (Real.toNNReal t)) = P.map (X' 0) := fun t ht =>
    (hlawt' _ (by rw [Real.coe_toNNReal _ ht.1]; exact ht.2)).trans (hlawt' 0 (by simpa using hT.le)).symm
  haveI hP0 : IsProbabilityMeasure (P.map (X' 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hX'm 0).aemeasurable).2 inferInstance
  have hν1 : Integrable (fun x : Euc d => ‖x‖) (HRS.Whole.meanEmpirical (P.map (X' 0))) := by
    refine s21_meanEmp_norm_integrable hNpos P (X' 0) (hX'm 0) ?_
    exact lt_of_le_of_lt (hM₂mom N hN P (X' 0) (hX'm 0) (hlawt' 0 (by simpa using hT.le))) ENNReal.ofReal_lt_top
  -- the centred remainder and the Fubini identity
  obtain ⟨hint', hremc⟩ := hCT ρ₁ h₁ N hN P (X 0) W X' hBr hX's hlawt'
  have hρS : IsSchwartzDensity ρ₁ := by
    rw [HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ h₁]; exact s21_schwartz_thermal hd hs0 hsd ha hβ
  have hint : ∀ᵐ ζ ∂P, ∀ α : MultiIndex d, ∀ t ∈ Set.Icc (0 : ℝ) b.T,
      IntegrableOn (fun r => commForcing (S.coeff N) b.s b.m (HRS.Whole.withDensityReal ρ₁) X' α t r ζ)
        (Set.Icc 0 t) := by
    rw [hcoeff]
    exact hint'
  have hOrb' : HRS.MS.S53.S53Orbit (S.coeff N) b.m b.T KO bO G0 G1 G2 := by
    rw [hcoeff]; exact hOrb
  have hfub : ∀ α : MultiIndex d, ∀ t ∈ Set.Icc (0 : ℝ) b.T,
      IntegrableOn (fun r => ∫ ζ, commForcing (S.coeff N) b.s b.m (HRS.Whole.withDensityReal ρ₁) X' α t r ζ ∂P)
          (Set.Icc 0 t) ∧
        ∫ ζ, (∫ r in Set.Icc (0 : ℝ) t,
            commForcing (S.coeff N) b.s b.m (HRS.Whole.withDensityReal ρ₁) X' α t r ζ) ∂P =
          ∫ r in Set.Icc (0 : ℝ) t, ∫ ζ, commForcing (S.coeff N) b.s b.m (HRS.Whole.withDensityReal ρ₁) X' α t r ζ ∂P ∧
        Integrable (fun ζ => ∫ r in Set.Icc (0 : ℝ) t,
          commForcing (S.coeff N) b.s b.m (HRS.Whole.withDensityReal ρ₁) X' α t r ζ) P := by
    intro α t ht
    exact HRS.MS.S53.s21_fubini_comm hd hs0 hsd b.m b.T hT0 hρS (quadraticGradientDyn d s a β) (S.coeff N) hOrb' CA hN
      P (X 0) W X' hX's (fun t ht => (hlawt' _ (by rw [Real.coe_toNNReal _ ht.1]; exact ht.2)).trans
        (hlawt' 0 (by simpa using hT.le)).symm)
      (fun f hf => hCA N hN P (X' 0) (hX'm 0) (hlawt' 0 (by simpa using hT.le)) ρ₁ h₁ f hf) α ht
  -- second moments and the energy
  have hmom : ∀ t ∈ Set.Icc (0 : ℝ) b.T,
      ∫⁻ ζ, ENNReal.ofReal (HRS.Whole.pair (HRS.Whole.empirical (X' (Real.toNNReal t) ζ))
        (fun x => ‖x‖ ^ 2)) ∂P ≤ ENNReal.ofReal M₂ ∧
      ENNReal.ofReal (HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N t)) (fun x => ‖x‖ ^ 2)) ≤
        ENNReal.ofReal M₂ := by
    intro t ht
    refine ⟨hM₂mom N hN P (X' (Real.toNNReal t)) (hX'm _) (hlawt' _ (by rw [Real.coe_toNNReal _ ht.1]; exact ht.2)), ?_⟩
    rw [hρ' N t]
    exact ENNReal.ofReal_le_ofReal (hM₂ρ ρ₁ h₁)
  have hδ0 : 0 ≤ HRS.deltaN d s N := (s21_deltaN_pos hs0 hsd N hN1).le
  have hoN0 : 0 ≤ HRS.oN d s C₀ N := (s21_oN_pos hd1 hs0 hC₀pos N hN1).le
  have hEle : S.energyMomentE N 1 P X' ≤ ENNReal.ofReal (Kε * HRS.deltaN d s N + HRS.oN d s C₀ N) := by
    refine s21_energyMomentE_le S P X' (Kε := Kε * HRS.deltaN d s N) ?_ ?_ hoN0
    · intro t ht
      have := (hKε ρ₁ h₁ N hN P (X' (Real.toNNReal t)) (hX'm _)
        (hlawt' _ (by rw [Real.coe_toNNReal _ ht.1]; exact ht.2))).1
      rw [hρ' N t]
      exact this
    · intro t ht
      have := (hKε ρ₁ h₁ N hN P (X' (Real.toNNReal t)) (hX'm _)
        (hlawt' _ (by rw [Real.coe_toNNReal _ ht.1]; exact ht.2))).2
      rw [hρ' N t]
      exact this
  have hE1 : S.energyMomentE N 1 P X' ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hEle
  have hEreal : (S.energyMomentE N 1 P X').toReal ≤ (3 * Kε + 1) * HRS.oN d s C₀ N := by
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hEle
    rw [ENNReal.toReal_ofReal (by positivity)] at h1
    have h2 := s21_deltaN_le_oN hd1 hs0 hsd hC₀pos N hN1
    have h3 : 3 / C₀ ≤ 3 := by
      rw [div_le_iff₀ hC₀pos]; linarith
    have h4 : HRS.deltaN d s N ≤ 3 * HRS.oN d s C₀ N := by
      calc HRS.deltaN d s N ≤ 3 / C₀ * HRS.oN d s C₀ N := h2
        _ ≤ 3 * HRS.oN d s C₀ N := mul_le_mul_of_nonneg_right h3 hoN0
    calc _ ≤ Kε * HRS.deltaN d s N + HRS.oN d s C₀ N := h1
      _ ≤ Kε * (3 * HRS.oN d s C₀ N) + HRS.oN d s C₀ N := by
          have := mul_le_mul_of_nonneg_left h4 hKε0
          linarith
      _ = (3 * Kε + 1) * HRS.oN d s C₀ N := by ring
  have hglr : generalLocalizationRate d (S.energyMomentE N 1 P X').toReal M₂ N ≤
      Cg * localizationRate d s C₀ N :=
    hCg N hN _ ENNReal.toReal_nonneg hEreal
  -- the remainder bound in the scaled form
  set c1 : ℝ := Real.sqrt β with hc1def
  set vfun : Set.Icc (0 : ℝ) b.T → MultiIndex d → Ω → ℝ := fun t α ζ =>
    -(Real.sqrt N / 2) * ∫ r in Set.Icc (0 : ℝ) t,
      (commForcing (S.coeff N) b.s b.m (HRS.Whole.withDensityReal ρ₁) X' α t r ζ -
        ∫ ζ', commForcing (S.coeff N) b.s b.m (HRS.Whole.withDensityReal ρ₁) X' α t r ζ' ∂P) with hvfun
  have hremc' : (∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) b.T, l2NormE (fun α : MultiIndex d => vfun t α ζ)) ^ (2 : ℝ) ∂P) ^
      (1 / 2 : ℝ) ≤ ENNReal.ofReal (CT * Real.sqrt (HRS.deltaN d s N)) := by
    have e2 : ∀ x : ℝ≥0∞, x ^ (2 : ℝ) = x ^ (2 : ℕ) := fun x => by
      rw [← ENNReal.rpow_natCast]; norm_num
    simp_rw [e2]
    rw [← hcoeff] at hremc
    exact hremc
  have hrem : (∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) b.T, l2NormE (fun α : MultiIndex d =>
        s21Gfun b S ρ₁ P X' t α ζ)) ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (c1 * (CT' * Real.sqrt (HRS.deltaN d s N))) := by
    haveI : Nonempty (Set.Icc (0 : ℝ) b.T) := ⟨⟨0, le_rfl, hT0⟩⟩
    have e : ∀ (t : Set.Icc (0 : ℝ) b.T) α ζ, s21Gfun b S ρ₁ P X' t α ζ = c1 * vfun t α ζ := by
      intro t α ζ
      simp only [s21Gfun, hvfun]
      rw [hσ2]
      ring
    simp_rw [e]
    rw [s21_hrem_scale P c1 hc1.le vfun, ENNReal.ofReal_mul hc1.le]
    refine mul_le_mul' le_rfl (hremc'.trans (ENNReal.ofReal_le_ofReal ?_))
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
  -- the Gaussian side
  set Zh : ℝ → Ω' → OscDual d b.m := fun t ζ => c1 • Z t ζ with hZh
  have hZm : ∀ t, Measurable (Zh t) := fun t => (hZ.meas t).const_smul c1
  have hZc : ∀ᵐ ζ ∂P', ContinuousOn (fun t => Zh t ζ) (Set.Icc 0 b.T) := by
    filter_upwards [hZ.cont] with ζ h using h.const_smul c1
  set Cinit : ℝ → ℝ → MultiIndex d → MultiIndex d → ℝ := fun t t' α α' =>
    HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal ρ₁) β
      (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ₁)) 0 t (oscTestFun b.m α))
      (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ₁)) 0 t' (oscTestFun b.m α')) with hCinit
  obtain ⟨γ0, hγp, hγfdd, hγs, hγw⟩ := hInit ρ₁ h₁ N hN
  haveI : IsProbabilityMeasure γ0 := hγp
  set L : OscPath d b.m b.T →L[ℝ] OscPath d b.m b.T := c1 • ContinuousLinearMap.id ℝ (OscPath d b.m b.T) with hL
  haveI hγhp : IsProbabilityMeasure (γ0.map L) :=
    (Measure.isProbabilityMeasure_map_iff L.continuous.measurable.aemeasurable).2 hγp
  have hZfdd : ∀ (p : ℕ) (ts : Fin p → ℝ) (_ : ∀ a, ts a ∈ Set.Icc (0 : ℝ) b.T) (αs : Fin p → MultiIndex d),
      P'.map (fun ζ => (WithLp.toLp 2 fun a => OscDual.coord (Zh (ts a) ζ) (αs a) :
          EuclideanSpace ℝ (Fin p))) =
        multivariateGaussian 0 (Matrix.of fun a c => (fun t t' α α' => β * Cinit t t' α α') (ts a) (ts c) (αs a) (αs c) +
          noiseCovW (S.coeff N) (S.q N) (ts a) (ts c) (oscTestFun b.m (αs a)) (oscTestFun b.m (αs c))) := by
    intro p ts hts αs
    have := s21_Zh_fdd P' hβ hZ ts hts αs
    rw [hq1, ← hcoeff2]
    exact this
  have hγh : ∀ (p : ℕ) (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) b.T) (αs : Fin p → MultiIndex d),
      (Matrix.of fun a c => (fun t t' α α' => β * Cinit t t' α α') (ts a) (ts c) (αs a) (αs c)).PosSemidef ∧
      (γ0.map L).map (fun w : OscPath d b.m b.T => (WithLp.toLp 2 fun a =>
          OscDual.coord (OscPath.at' w ⟨ts a, hts a⟩) (αs a) : EuclideanSpace ℝ (Fin p))) =
        multivariateGaussian 0 (Matrix.of fun a c => (fun t t' α α' => β * Cinit t t' α α') (ts a) (ts c)
          (αs a) (αs c)) := fun p ts hts αs =>
    s21_gammahat_fdd hβ γ0 Cinit hγfdd p ts hts αs
  -- the initial path
  set νb : Measure (Euc d) := HRS.Whole.meanEmpirical (P.map (X' 0)) with hνb
  haveI hνbp : IsProbabilityMeasure νb := HRS.Whole.meanEmpirical_isProbabilityMeasure _ hN1
  have hlaw0' : P.map (X' 0) = Gibbs := hlawt' 0 (by simpa using hT.le)
  have hνbG : νb = HRS.Whole.meanEmpirical Gibbs := by rw [hνb, hlaw0']
  set IP := s21IP b.m b.T hT0 (S.coeff N) N νb with hIP
  have hIPm : Measurable IP := s21IP_meas b hbv S hN1 hC νb hν1
  haveI hGIp : IsProbabilityMeasure (Gibbs.map IP) :=
    (Measure.isProbabilityMeasure_map_iff hIPm.aemeasurable).2 hGp
  have hγs' : smoothDist 2 (Gibbs.map IP) γ0 ≤ Ci * Real.sqrt (HRS.deltaN d s N) := by
    have h := hγs
    rw [hcoeff2] at h
    rw [hIP, hνbG]
    exact h
  have hγw' : wassersteinE 1 (Gibbs.map IP) γ0 ≤ ENNReal.ofReal (Ci * HRS.deltaN d s N ^ ((3 : ℝ) / 20)) := by
    have h := hγw
    rw [hcoeff2] at h
    rw [hIP, hνbG]
    exact h
  have hLm : Measurable L := L.continuous.measurable
  have hpath : law P (s21Path0 hT0 S X' νb) = (Gibbs.map IP).map L := by
    have e : s21Path0 hT0 S X' νb = L ∘ (IP ∘ X' 0) := by
      funext ζ
      exact s21_path0_eq hT0 S X' νb hσ2 ζ
    unfold law
    rw [e, ← Measure.map_map hLm (hIPm.comp (hX'm 0)), ← Measure.map_map hIPm (hX'm 0), hlaw0']
  have hLn : ‖L‖ ≤ c1 := s21_smul_clm_norm c1 hc1.le
  have hsm0 : smoothDist 2 (law P (s21Path0 hT0 S X' νb)) (γ0.map L) ≤
      max 1 β * (Ci * Real.sqrt (HRS.deltaN d s N)) := by
    rw [hpath]
    refine (HRS.Main.smoothDist_map_clm_le L 2 (Gibbs.map IP) γ0).trans ?_
    have hmx : max 1 (‖L‖ ^ 2) ≤ max 1 β := max_le_max le_rfl (by
      calc ‖L‖ ^ 2 ≤ c1 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hLn 2
        _ = β := Real.sq_sqrt hβ.le)
    exact mul_le_mul hmx hγs' (smoothDist_nonneg _ _ _) (le_trans zero_le_one (le_max_left _ _))
  have hw0 : wassersteinE 1 (law P (s21Path0 hT0 S X' νb)) (γ0.map L) ≤
      ENNReal.ofReal (c1 * (Ci * HRS.deltaN d s N ^ ((3 : ℝ) / 20))) := by
    rw [hpath]
    refine (HRS.Main.wassersteinE_map_clm_le L 1 le_rfl (Gibbs.map IP) γ0).trans ?_
    rw [ENNReal.ofReal_mul hc1.le]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hLn) hγw'
  have hMZ := s21_master_Z b hbv S hN hC (hOMall S N) hCmp hCtr0 hTr M₂ hM₂0 hM1 (fun t => hρ' N t) P hX'sS ℱ W'
    hF' hstat hν1 hfub hint hmom hE1 hrem (γ0.map L) hsm0 hw0 P' Zh hZm hZc
    (fun t t' α α' => β * Cinit t t' α α') hZfdd hγh
  -- transfer back to `zeta`
  set L' : OscPath d b.m b.T →L[ℝ] OscPath d b.m b.T := c1⁻¹ • ContinuousLinearMap.id ℝ (OscPath d b.m b.T) with hL'
  have hc1inv : 0 ≤ c1⁻¹ := inv_nonneg.2 hc1.le
  have hL'n : ‖L'‖ ≤ c1⁻¹ := s21_smul_clm_norm c1⁻¹ hc1inv
  have hΞm : AEMeasurable (s21XiPath S X' νb) P := by
    have h := gfb4_aemeasurable_windowPath P hT0 (s21Xi S X' νb)
      (fun t _ => s21_Xi_meas b hbv S hNpos X' hX'm νb t)
      (by
        filter_upwards [hX's.cont] with ζ hζ
        exact (s21_Xi_cont b hbv S hNpos X' νb ζ hζ).continuousOn)
    rw [← s56_wpo_eq_windowPath] at h
    exact h
  have hZaem : AEMeasurable (processWindow b.m b.T 0 Zh) P' := by
    have h := gfb4_aemeasurable_windowPath P' hT0 Zh (fun t _ => hZm t) hZc
    rw [← s56_wpo_eq_windowPath] at h
    exact h
  haveI hlΞp : IsProbabilityMeasure (law P (s21XiPath S X' νb)) :=
    (Measure.isProbabilityMeasure_map_iff hΞm).2 inferInstance
  haveI hlZp : IsProbabilityMeasure (law P' (processWindow b.m b.T 0 Zh)) :=
    (Measure.isProbabilityMeasure_map_iff hZaem).2 inferInstance
  have hX_ae := s21_X_eq_ae P T hT.le X X' hmod hstrong.cont hX's.cont
  have hzeta_ae : zetaPathW b.m b.T 0 P X =ᵐ[P] zetaPathW b.m b.T 0 P X' := by
    filter_upwards [hX_ae] with ζ h
    unfold zetaPathW
    refine s56_wpo_congr fun t ht => ?_
    have htle : ((Real.toNNReal t : ℝ≥0) : ℝ) ≤ T := by rw [Real.coe_toNNReal _ ht.1]; exact ht.2
    have hmapeq : P.map (X (Real.toNNReal t)) = P.map (X' (Real.toNNReal t)) :=
      Measure.map_congr (hmod _ htle).symm
    rw [hmapeq, h _ htle]
  have hlawzeta : law P (zetaPathW b.m b.T 0 P X) = (law P (s21XiPath S X' νb)).map L' := by
    unfold law
    rw [Measure.map_congr hzeta_ae]
    have e : zetaPathW b.m b.T 0 P X' = L' ∘ s21XiPath S X' νb := funext fun ζ =>
      s21_zeta_eq b S P X' hβ hσ2 hstat hNpos ζ
    rw [e, ← AEMeasurable.map_map_of_aemeasurable L'.continuous.measurable.aemeasurable hΞm]
  have hZlaw : law P' (processWindow b.m b.T 0 Z) = (law P' (processWindow b.m b.T 0 Zh)).map L' := by
    unfold law
    have e : processWindow b.m b.T 0 Z = L' ∘ processWindow b.m b.T 0 Zh := by
      funext ζ
      show windowPathOf b.m b.T 0 (fun t => Z t ζ) = c1⁻¹ • windowPathOf b.m b.T 0 (fun t => Zh t ζ)
      rw [← s21_wpo_smul c1⁻¹ (inv_ne_zero hc1.ne')]
      congr 1
      funext t
      show Z t ζ = c1⁻¹ • c1 • Z t ζ
      rw [smul_smul, inv_mul_cancel₀ hc1.ne', one_smul]
    rw [e, ← AEMeasurable.map_map_of_aemeasurable L'.continuous.measurable.aemeasurable hZaem]
  -- the conclusion
  have hm' : (d : ℝ) < ((wholeSpaceIndex d : ℕ) : ℝ) := hm
  -- the real-number bookkeeping
  have hδs0 : 0 ≤ Real.sqrt (HRS.deltaN d s N) := Real.sqrt_nonneg _
  have hglr0 : 0 ≤ generalLocalizationRate d (S.energyMomentE N 1 P X').toReal M₂ N :=
    s56_w_nonneg d _ M₂ N hM₂0
  have hloc0 : 0 ≤ localizationRate d s C₀ N := by unfold localizationRate; positivity
  have hCi : 0 ≤ Ci := hCi0
  set glr := generalLocalizationRate d (S.energyMomentE N 1 P X').toReal M₂ N with hglrdef
  set loc := localizationRate d s C₀ N with hlocdef
  set δs := Real.sqrt (HRS.deltaN d s N) with hδsdef
  have hM1β : 0 ≤ max 1 β := le_trans zero_le_one (le_max_left _ _)
  have hSnn : 0 ≤ Cs * (Ctr' * 1 * glr) + c1 * (CT' * δs) + max 1 β * (Ci * δs) :=
    add_nonneg (add_nonneg (mul_nonneg hCs0 (mul_nonneg (mul_nonneg hCtr0 zero_le_one) hglr0))
      (mul_nonneg hc1.le (mul_nonneg hCT'0 hδs0))) (mul_nonneg hM1β (mul_nonneg hCi hδs0))
  have hA : smoothDist 2 (law P (s21XiPath S X' νb)) (law P' (processWindow b.m b.T 0 Zh)) ≤
      Cs * (Ctr' * 1 * glr) + c1 * (CT' * δs) + max 1 β * (Ci * δs) := by
    have h := hMZ.1
    rw [hq1] at h
    have e : ENNReal.ofReal Cs * ENNReal.ofReal (Ctr' * 1 * glr) + ENNReal.ofReal (c1 * (CT' * δs)) +
        ENNReal.ofReal (max 1 β * (Ci * δs)) =
        ENNReal.ofReal (Cs * (Ctr' * 1 * glr) + c1 * (CT' * δs) + max 1 β * (Ci * δs)) := by
      rw [← ENNReal.ofReal_mul hCs0,
        ← ENNReal.ofReal_add (mul_nonneg hCs0 (mul_nonneg (mul_nonneg hCtr0 zero_le_one) hglr0))
          (mul_nonneg hc1.le (mul_nonneg hCT'0 hδs0)),
        ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hCs0 (mul_nonneg (mul_nonneg hCtr0 zero_le_one) hglr0))
          (mul_nonneg hc1.le (mul_nonneg hCT'0 hδs0))) (mul_nonneg hM1β (mul_nonneg hCi hδs0))]
    exact (ENNReal.ofReal_le_ofReal_iff hSnn).1 (h.trans (le_of_eq e))
  have hP1 : 0 ≤ Cs * Ctr' * Cg := mul_nonneg (mul_nonneg hCs0 hCtr0) hCg0
  have hP2 : 0 ≤ c1 * CT' + max 1 β * Ci := add_nonneg (mul_nonneg hc1.le hCT'0) (mul_nonneg hM1β hCi)
  have hSle : Cs * (Ctr' * 1 * glr) + c1 * (CT' * δs) + max 1 β * (Ci * δs) ≤
      (Cs * Ctr' * Cg + (c1 * CT' + max 1 β * Ci)) * (δs + loc) := by
    have h1 : Cs * (Ctr' * 1 * glr) ≤ Cs * Ctr' * Cg * loc := by
      calc Cs * (Ctr' * 1 * glr) = Cs * Ctr' * glr := by ring
        _ ≤ Cs * Ctr' * (Cg * loc) := mul_le_mul_of_nonneg_left hglr (mul_nonneg hCs0 hCtr0)
        _ = Cs * Ctr' * Cg * loc := by ring
    have e1 : c1 * (CT' * δs) + max 1 β * (Ci * δs) = (c1 * CT' + max 1 β * Ci) * δs := by ring
    have e2 : (Cs * Ctr' * Cg + (c1 * CT' + max 1 β * Ci)) * (δs + loc) =
        Cs * Ctr' * Cg * δs + Cs * Ctr' * Cg * loc + (c1 * CT' + max 1 β * Ci) * δs +
          (c1 * CT' + max 1 β * Ci) * loc := by ring
    have h3 := mul_nonneg hP1 hδs0
    have h4 := mul_nonneg hP2 hloc0
    linarith
  have hmaxL : max 1 (‖L'‖ ^ 2) ≤ max 1 β⁻¹ := max_le_max le_rfl (by
    calc ‖L'‖ ^ 2 ≤ (c1⁻¹) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hL'n 2
      _ = β⁻¹ := by rw [inv_pow, hc1def, Real.sq_sqrt hβ.le])
  have hMβ0 : 0 ≤ max 1 β⁻¹ := le_trans zero_le_one (le_max_left _ _)
  have hsmall : smoothDist 2 (law P (zetaPathW b.m b.T 0 P X)) (law P' (processWindow b.m b.T 0 Z)) ≤
      max Csm Cw * (δs + loc) := by
    rw [hlawzeta, hZlaw]
    refine (HRS.Main.smoothDist_map_clm_le L' 2 _ _).trans ?_
    have hCsm' : Csm = max 1 β⁻¹ * (Cs * Ctr' * Cg + (c1 * CT' + max 1 β * Ci)) := by
      rw [hCsm]; ring
    calc max 1 (‖L'‖ ^ 2) * smoothDist 2 (law P (s21XiPath S X' νb)) (law P' (processWindow b.m b.T 0 Zh))
        ≤ max 1 β⁻¹ * ((Cs * Ctr' * Cg + (c1 * CT' + max 1 β * Ci)) * (δs + loc)) :=
          mul_le_mul hmaxL (hA.trans hSle) (smoothDist_nonneg _ _ _) hMβ0
      _ = Csm * (δs + loc) := by rw [hCsm']; ring
      _ ≤ max Csm Cw * (δs + loc) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (add_nonneg hδs0 hloc0)
  have hδle1 : HRS.deltaN d s N ≤ 1 := s21_deltaN_le_one hs0 hsd N hN1
  have hδ34 : δs ≤ HRS.deltaN d s N ^ ((3 : ℝ) / 20) := s21_sqrt_le_rpow hδ0 hδle1
  have hrp0 : 0 ≤ HRS.deltaN d s N ^ ((3 : ℝ) / 20) := Real.rpow_nonneg hδ0 _
  have hsq0 : 0 ≤ Real.sqrt loc := Real.sqrt_nonneg _
  have hQnn : 0 ≤ Ctr' * 1 * glr := mul_nonneg (mul_nonneg hCtr0 zero_le_one) hglr0
  have hsqQ : Real.sqrt (Ctr' * 1 * glr) ≤ Real.sqrt (Ctr' * Cg) * Real.sqrt loc := by
    rw [← Real.sqrt_mul (mul_nonneg hCtr0 hCg0)]
    refine Real.sqrt_le_sqrt ?_
    calc Ctr' * 1 * glr = Ctr' * glr := by ring
      _ ≤ Ctr' * (Cg * loc) := mul_le_mul_of_nonneg_left hglr hCtr0
      _ = Ctr' * Cg * loc := by ring
  have hWB : c1⁻¹ * (Cw1 * Real.sqrt (Ctr' * 1 * glr) + c1 * (CT' * δs) +
      c1 * (Ci * HRS.deltaN d s N ^ ((3 : ℝ) / 20))) ≤
      Cw * (HRS.deltaN d s N ^ ((3 : ℝ) / 20) + Real.sqrt loc) := by
    have hCwdef : Cw = c1⁻¹ * (Cw1 * Real.sqrt (Ctr' * Cg) + c1 * CT' + c1 * Ci) := rfl
    have hr := Real.sqrt_nonneg (Ctr' * Cg)
    have hX1 : Cw1 * Real.sqrt (Ctr' * 1 * glr) ≤ Cw1 * (Real.sqrt (Ctr' * Cg) * Real.sqrt loc) :=
      mul_le_mul_of_nonneg_left hsqQ hCw10
    have hX2 : c1 * (CT' * δs) ≤ c1 * (CT' * HRS.deltaN d s N ^ ((3 : ℝ) / 20)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hδ34 hCT'0) hc1.le
    have hXY : Cw1 * Real.sqrt (Ctr' * 1 * glr) + c1 * (CT' * δs) +
        c1 * (Ci * HRS.deltaN d s N ^ ((3 : ℝ) / 20)) ≤
        (Cw1 * Real.sqrt (Ctr' * Cg) + c1 * CT' + c1 * Ci) *
          (HRS.deltaN d s N ^ ((3 : ℝ) / 20) + Real.sqrt loc) := by
      set r := HRS.deltaN d s N ^ ((3 : ℝ) / 20) with hr_def
      set q := Real.sqrt loc with hq_def
      set u := Real.sqrt (Ctr' * Cg) with hu_def
      have e2 : (Cw1 * u + c1 * CT' + c1 * Ci) * (r + q) =
          Cw1 * (u * q) + c1 * (CT' * r) + c1 * (Ci * r) + (Cw1 * u * r + (c1 * CT' + c1 * Ci) * q) := by ring
      have h3 : 0 ≤ Cw1 * u * r := mul_nonneg (mul_nonneg hCw10 hr) hrp0
      have h4 : 0 ≤ (c1 * CT' + c1 * Ci) * q := mul_nonneg (add_nonneg (mul_nonneg hc1.le hCT'0) (mul_nonneg hc1.le hCi)) hsq0
      linarith
    rw [hCwdef, mul_assoc c1⁻¹ (Cw1 * Real.sqrt (Ctr' * Cg) + c1 * CT' + c1 * Ci)]
    exact mul_le_mul_of_nonneg_left hXY hc1inv
  have hwass : wassersteinE 1 (law P (zetaPathW b.m b.T 0 P X)) (law P' (processWindow b.m b.T 0 Z)) ≤
      ENNReal.ofReal (max Csm Cw * (HRS.deltaN d s N ^ ((3 : ℝ) / 20) + Real.sqrt loc)) := by
    rw [hlawzeta, hZlaw]
    refine (HRS.Main.wassersteinE_map_clm_le L' 1 le_rfl _ _).trans ?_
    have h := hMZ.2
    rw [hq1] at h
    calc ENNReal.ofReal ‖L'‖ * wassersteinE 1 (law P (s21XiPath S X' νb)) (law P' (processWindow b.m b.T 0 Zh))
        ≤ ENNReal.ofReal c1⁻¹ * (ENNReal.ofReal Cw1 * (ENNReal.ofReal (Ctr' * 1 * glr)) ^ (1 / 2 : ℝ) +
            ENNReal.ofReal (c1 * (CT' * δs)) +
            ENNReal.ofReal (c1 * (Ci * HRS.deltaN d s N ^ ((3 : ℝ) / 20)))) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal hL'n) h
      _ = ENNReal.ofReal (c1⁻¹ * (Cw1 * Real.sqrt (Ctr' * 1 * glr) + c1 * (CT' * δs) +
            c1 * (Ci * HRS.deltaN d s N ^ ((3 : ℝ) / 20)))) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hQnn (by norm_num), ← Real.sqrt_eq_rpow,
            ← ENNReal.ofReal_mul hCw10,
            ← ENNReal.ofReal_add (mul_nonneg hCw10 (Real.sqrt_nonneg _)) (mul_nonneg hc1.le (mul_nonneg hCT'0 hδs0)),
            ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hCw10 (Real.sqrt_nonneg _))
              (mul_nonneg hc1.le (mul_nonneg hCT'0 hδs0))) (mul_nonneg hc1.le (mul_nonneg hCi hrp0)),
            ← ENNReal.ofReal_mul hc1inv]
      _ ≤ ENNReal.ofReal (max Csm Cw * (HRS.deltaN d s N ^ ((3 : ℝ) / 20) + Real.sqrt loc)) :=
          ENNReal.ofReal_le_ofReal (hWB.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
            (add_nonneg hrp0 hsq0)))
  exact ⟨s21_zeta_aemeas hd hN1 hm' hT.le P hstrong Gibbs (fun t ht => hlawt t ht),
    s21_Z_aemeas P' hZ hT.le, hsmall, hwass⟩

end HRS.MS.S21
