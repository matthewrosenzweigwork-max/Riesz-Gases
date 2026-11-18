import HRS.Sections.AdjKGlueAux3

/-!
# ADJK-GLUE, part 4: `moving_integrated_forcing` (Lemma 5.8, third assertion), assembled
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.AdjK

open HRS.Uniform

variable {d : ℕ}

theorem adjkg_moving_integrated_forcing (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ}
    {ρ : ℝ → Torus d → ℝ} (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (p₀ : ℝ) (hp₀ : 1 < p₀)
    (m : ℝ) (hm : (d : ℝ) / 2 + 2 < m) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        (∀ T' : ℝ, 0 ≤ T' → IsParticleSystem P htr.dyn T' X₀ W X) →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
          IsFilteredSolution P ℱ W' W X) →
        P.map X₀ ≪ modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0)) →
        eLpNorm ((P.map X₀).rnDeriv (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))))
          (ENNReal.ofReal p₀) (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) < ⊤ →
        (∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ k : NonzeroLattice d,
          IntervalIntegrable (fun r =>
            Real.sqrt N * modulatedEnergy
              (commKernel (periodicRieszGrad d htr.dyn.s) (Torus.grad (propagator htr.dyn ρ r t (Torus.realMode k))))
              (X r.toNNReal ω) (withDensityReal (ρ r))) volume 0 t) ∧
        ∀ a : ℝ, 0 ≤ a →
          ∫⁻ ω, ⨆ t ∈ {t : ℝ | t ∈ Set.Icc a (a + T) ∧ ∃ q : ℚ, (q : ℝ) = t}, ∑' k : NonzeroLattice d,
              ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * m) *
                evolvingForcingCoord htr.dyn ρ X k t ω ^ 2) ∂P ≤
            ENNReal.ofReal ((C * logMomentScale d s N p₀ (P.map X₀)
              (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) / Real.sqrt N) ^ 2) := by
  classical
  have hd1 : 1 ≤ d := by omega
  obtain ⟨cstar, A, hA, hw, hw0, hdom⟩ := movsx_hdom hd1 htr.hs0 htr.hsd
  obtain ⟨C₂, hC₂0, hC₂⟩ := moving_pair_moments_proof' hd htr p₀ hp₀ cstar hw 2 (by norm_num)
  obtain ⟨CV, cV, hCVpos, hcVpos, Vev, hdual, hplain, hdec, -⟩ := adjk_evolution_along_trajectory hd htr m
  obtain ⟨CV₂, cV₂, hCV₂pos, hcV₂pos, Vev₂, hdual₂, -, hdec₂, -⟩ :=
    adjk_evolution_along_trajectory hd htr ((d : ℝ) + 3)
  have hCV₂' : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev₂ t u‖ ≤ CV₂ := by
    intro u t hu hut
    refine (hdec₂ u t hu hut).trans ?_
    have : Real.exp (-cV₂ * (t - u)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    nlinarith [hCV₂pos]
  have hCV' : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ CV := by
    intro u t hu hut
    refine (hdec u t hu hut).trans ?_
    have : Real.exp (-cV * (t - u)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    nlinarith [hCVpos]
  obtain ⟨C₀, hC₀⟩ := Torus.cbNorm_realMode_le (d := d) 2
  set C₀' : ℝ := max C₀ 0 with hC₀'
  have hC₀'0 : 0 ≤ C₀' := le_max_right _ _
  set S : ℝ := ∑' j : NonzeroLattice d, Lattice.jp j.1 ^ (-(2 * (m - 2))) with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun j => Real.rpow_nonneg (Torus.jp_pos _).le _
  set c₁ : ℝ := C₂ * (A * ((d : ℝ) * C₀')) with hc₁
  have hc₁0 : 0 ≤ c₁ := by positivity
  set CC : ℝ := CV * (1 / cV + T) * (c₁ * Real.sqrt S) with hCC
  have hCC0 : 0 ≤ CC := by positivity
  refine ⟨CC, hCC0, ?_⟩
  intro N hN Ω _ P _ X₀ W X hPall hfilt hac hLp
  obtain ⟨ℱ, W', hF⟩ := hfilt
  set J : ℝ := logMomentScale d s N p₀ (P.map X₀)
    (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) with hJ
  set Jp : ℝ := max J 0 with hJp
  have hJp0 : 0 ≤ Jp := le_max_right _ _
  have hNpos : 0 < N := by omega
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hNpos)
  set K : ℝ := c₁ * Jp / Real.sqrt N with hK
  have hK0 : 0 ≤ K := by positivity
  have hmeasY : ∀ j : NonzeroLattice d, Measurable (fun p : ℝ × Ω => adjkgY s ρ X j p.1 p.2) :=
    fun j => adjkg_Y_measurable hd htr hF.progressive j
  have hmeasYr : ∀ (j : NonzeroLattice d) (r : ℝ), Measurable (fun ω => adjkgY s ρ X j r ω) :=
    fun j r => (hmeasY j).comp (measurable_const.prodMk measurable_id)
  -- per-mode second moments
  have hL2 : ∀ (r : ℝ), 0 ≤ r → ∀ j : NonzeroLattice d, ∫⁻ ω, ‖adjkgY s ρ X j r ω‖ₑ ^ 2 ∂P ≤
      ENNReal.ofReal ((K * Lattice.jp j.1 ^ 2) ^ 2) := by
    intro r hr j
    have hek : Torus.IsCk 2 (Torus.realMode j) := adjkd_isCk_of_smooth 2 (adjkd_isSmooth_realMode j)
    have hlip := dyncmp_lip_grad hek
    have hL0 : 0 ≤ (d : ℝ) * Torus.cbNorm 2 (Torus.realMode j) :=
      mul_nonneg (Nat.cast_nonneg d) (adjkd_cbNorm_nonneg 2 _)
    have hvc : Continuous (Torus.grad (Torus.realMode j)) :=
      Commutator.IsLipschitzVF.continuous hL0 hlip
    have hmeasK := dyncmp_commKernel_measurable
      (KernelGrad.measurable_periodicRieszGrad (by exact_mod_cast htr.hsd)) hvc.measurable
    have hsym : ∀ x y, commKernel (periodicRieszGrad d s) (Torus.grad (Torus.realMode j)) x y =
        commKernel (periodicRieszGrad d s) (Torus.grad (Torus.realMode j)) y x :=
      fun x y => dyncmp_commKernel_symm_gen htr.hsd _ x y
    have hDj0 : 0 ≤ A * ((d : ℝ) * Torus.cbNorm 2 (Torus.realMode j)) := mul_nonneg hA hL0
    have hpm := hC₂ N hN P X₀ W X hPall ⟨ℱ, W', hF⟩ hac hLp
      (A * ((d : ℝ) * Torus.cbNorm 2 (Torus.realMode j))) hDj0
      (commKernel (periodicRieszGrad d s) (Torus.grad (Torus.realMode j))) hmeasK hsym
      (fun x y _ => hdom _ _ hL0 hlip x y) r hr
    have hcb : Torus.cbNorm 2 (Torus.realMode j) ≤ C₀' * Lattice.jp j.1 ^ 2 :=
      (hC₀ j).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    set a : ℝ := C₂ * (A * ((d : ℝ) * Torus.cbNorm 2 (Torus.realMode j))) * Jp with ha
    have ha0 : 0 ≤ a := by positivity
    have hpm' : eLpNorm (fun ω => (N : ℝ) * modulatedEnergy
        (commKernel (periodicRieszGrad d s) (Torus.grad (Torus.realMode j))) (X r.toNNReal ω)
        (withDensityReal (ρ r))) (ENNReal.ofReal 2) P ≤ ENNReal.ofReal a := by
      refine hpm.trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
    have h1 := adjkg_Y_L2 (ρ := ρ) P hNpos X j hr (hmeasYr j r) ha0 hpm'
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    have hle : a / Real.sqrt N ≤ K * Lattice.jp j.1 ^ 2 := by
      rw [div_le_iff₀ hsq]
      have e : K * Lattice.jp j.1 ^ 2 * Real.sqrt N = c₁ * (Lattice.jp j.1 ^ 2) * Jp := by
        rw [hK]
        field_simp
      rw [e]
      have : a ≤ c₁ * (Lattice.jp j.1 ^ 2) * Jp := by
        rw [ha, hc₁]
        have : A * ((d : ℝ) * Torus.cbNorm 2 (Torus.realMode j)) ≤
            A * ((d : ℝ) * (C₀' * Lattice.jp j.1 ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcb (Nat.cast_nonneg d)) hA
        calc C₂ * (A * ((d : ℝ) * Torus.cbNorm 2 (Torus.realMode j))) * Jp
            ≤ C₂ * (A * ((d : ℝ) * (C₀' * Lattice.jp j.1 ^ 2))) * Jp :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hC₂0) hJp0
          _ = _ := by ring
      exact this
    have ha' : 0 ≤ a / Real.sqrt N := by positivity
    exact pow_le_pow_left₀ ha' hle 2
  -- the second moment of `R_r`
  set b : ℝ := K * Real.sqrt S with hb
  have hb0 : 0 ≤ b := by positivity
  have hb2 : b ^ 2 = K ^ 2 * S := by rw [hb, mul_pow, Real.sq_sqrt hS0]
  have hRb : ∀ r : ℝ, 0 ≤ r → ∫⁻ ω, ‖adjkgR m s ρ X r ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal (b ^ 2) := by
    intro r hr
    rw [hb2]
    exact adjkg_R_moment hd htr hm P X r hK0 (hmeasYr · r) (hL2 r hr)
  have hRmeas := adjkg_R_measurable hd htr hm hF.progressive
  -- a.s. integrability
  have hint := adjkg_conv_integrable Vev hplain hCV' P (adjkgR m s ρ X) hRmeas hRb
  -- conjunct 1
  have hC2 : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ k : NonzeroLattice d,
      IntervalIntegrable (fun r =>
        Real.sqrt N * modulatedEnergy
          (commKernel (periodicRieszGrad d htr.dyn.s) (Torus.grad (propagator htr.dyn ρ r t (Torus.realMode k))))
          (X r.toNNReal ω) (withDensityReal (ρ r))) volume 0 t := by
    have h : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) n, ∀ k : NonzeroLattice d,
        IntervalIntegrable (fun r =>
          Real.sqrt N * modulatedEnergy
            (commKernel (periodicRieszGrad d htr.dyn.s) (Torus.grad (propagator htr.dyn ρ r t (Torus.realMode k))))
            (X r.toNNReal ω) (withDensityReal (ρ r))) volume 0 t := fun n =>
      (adjk_forcing_intervalIntegrable_proof hd htr hN P X₀ W X (n : ℝ) (Nat.cast_nonneg n)
        (hPall n (Nat.cast_nonneg n)) ⟨ℱ, W', hF⟩).1
    filter_upwards [ae_all_iff.2 h] with ω hω t ht k
    obtain ⟨n, hn⟩ := exists_nat_ge t
    exact hω n t ⟨ht, hn⟩ k
  refine ⟨hC2, ?_⟩
  intro a ha
  have hC3 := adjk_det_convolution_L2_proof m T CV cV hT hCVpos.le hcVpos Vev hdec Ω P
    (adjkgR m s ρ X) hRmeas b hb0 hRb a ha
  refine le_trans ?_ (hC3.trans ?_)
  · refine lintegral_mono_ae ?_
    filter_upwards [hint] with ω hω
    refine iSup₂_le fun t ht => ?_
    have ht0 : 0 ≤ t := ha.trans ht.1.1
    have e : ∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * m) *
        evolvingForcingCoord htr.dyn ρ X k t ω ^ 2) =
        ‖∫ r in (0 : ℝ)..t, Vev t r (adjkgR m s ρ X r ω)‖ₑ ^ 2 := by
      rw [adjkg_enorm_sq_eq]
      refine tsum_congr fun k => ?_
      rw [adjkg_coord_integral hd htr hm hdual hdual₂ hCV₂' X ω ht0 (hω t ht0) k]
    rw [e]
    exact pow_le_pow_left' (le_iSup₂ (f := fun t (_ : t ∈ ratIcc a (a + T)) =>
      ‖∫ r in (0 : ℝ)..t, Vev t r (adjkgR m s ρ X r ω)‖ₑ) t ht) 2
  · refine ENNReal.ofReal_le_ofReal ?_
    have hbd : CV * (1 / cV + T) * b = CC * Jp / Real.sqrt N := by
      rw [hb, hK, hCC]
      field_simp
    rw [hbd]
    have hCCJ : CC * Jp / Real.sqrt N ≤ |CC * J / Real.sqrt N| := by
      rw [abs_div, abs_of_pos hsq, abs_mul, abs_of_nonneg hCC0]
      refine div_le_div_of_nonneg_right ?_ hsq.le
      exact mul_le_mul_of_nonneg_left (by rcases le_total J 0 with h | h
                                          · simp [hJp, max_eq_right h]
                                          · simp [hJp, max_eq_left h, abs_of_nonneg h]) hCC0
    calc (CC * Jp / Real.sqrt N) ^ 2 ≤ |CC * J / Real.sqrt N| ^ 2 :=
          pow_le_pow_left₀ (by positivity) hCCJ 2
      _ = (CC * J / Real.sqrt N) ^ 2 := sq_abs _

end HRS.AdjK
