import HRS.PDE.TorusFPLpGlue1
import HRS.PDE.TorusFPLpGlue2

/-!
# D3PHI glue, part 3: `V ∈ C²` (limit `k → ∞`) and `movT_lp_reg_bound_of_d3phi`

`movT_lp_reg_bound_pos_of_d3phi`: the `ε`-level `L^p` bound for `V ∈ C²`, `0 < T`, a general admissible exponent path, from
the smooth-`V` bridge (`TorusFPLpGlue2`) by `V_k → V` in `C²`, the stability of the SDE (`movb_exists_approx_solutions`), the
`C ε_k` perturbation of the source (`movb_srcReg_withV_diff`, which changes the constant `Cs` by `c C ε_k/ℓ`) and the joint narrow
lower semicontinuity of the `L^p` norm (`movT_lp_lsc`, constant reference `Q^M_t`).  Modelled on `movb_reg_ineq_pos`.
`movT_lp_reg_bound_of_d3phi`: the frozen statement `movT_lp_reg_bound`, with `p = movT_pPath` (`d3phi_movT_path`) and
`movT_lpGain` (`d3phi_movT_gain`); `t = 0` is trivial, `t > 0` forces `T > 0`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

/-- The gain is affine in `Cs` (the constant of the exponential bound). -/
theorem d3phi_gain_eq (c Cs : ℝ) (L p : ℝ → ℝ) (t : ℝ) :
    d3phi_gain c Cs L p t = (Cs / c) * ∫ r in (0 : ℝ)..t, L r * ((p r - 1) / p r) := by
  unfold d3phi_gain
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun r _ => ?_
  simp only [mul_assoc]


theorem movT_lp_reg_bound_pos_of_d3phi (hN0 : 0 < N) (hNd : 1 ≤ N * d) {Ω : Type*}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    (D : DynData d) (hM : D.M = -(1 : Matrix (Fin d) (Fin d) ℝ)) (hκ : 0 < D.invβ)
    (hV2 : Torus.IsCk 2 D.V) {T : ℝ} (hT : 0 < T) {ρ ρt : ℝ → Torus d → ℝ}
    (hρt : IsC12Test T ρ ρt) (hdens : ∀ r ∈ Set.Icc (0 : ℝ) T, IsProbDensity (ρ r))
    (hpos : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, 0 < ρ r x) (M : ℝ) {Y₀ : Ω → Fin N → Euc d}
    (hY₀ : ∀ t : ℝ, Measurable[ℱ t] Y₀) {Y : ℝ → Ω → (Fin N → Euc d)}
    (hY : IsAdditiveSDESolution P ℱ W' (fun _ => b15c_liftedDriftReg D M) (liftedNoise D) Y₀
      (fun _ => ⊤) Y)
    {c Cs ℓ : ℝ} (hc : 0 < c) (hℓ : 0 < ℓ) {L : ℝ → ℝ} (hL : ∀ r ∈ Set.Icc 0 T, ℓ ≤ L r)
    (hLi : IntegrableOn L (Set.Icc 0 T))
    (hexp : ∀ r ∈ Set.Icc 0 T, ∫⁻ X : Config d N,
      ENNReal.ofReal (Real.exp (c * |movT_srcReg D N M ρ ρt r X| / L r))
        ∂(movT_Q (b15c_gReg d D.s M) D N ρ r) ≤ ENNReal.ofReal (Real.exp Cs))
    {p : ℝ → ℝ} (hp : D3phiPath c L p T)
    (hac : selectedLaw P (b15c_regProcess Y) 0 ≪ movT_Q (b15c_gReg d D.s M) D N ρ 0)
    (hfin : eLpNorm ((selectedLaw P (b15c_regProcess Y) 0).rnDeriv
        (movT_Q (b15c_gReg d D.s M) D N ρ 0)) (ENNReal.ofReal (p 0))
        (movT_Q (b15c_gReg d D.s M) D N ρ 0) < ⊤) :
    ∀ t ∈ Set.Icc 0 T,
      selectedLaw P (b15c_regProcess Y) t ≪ movT_Q (b15c_gReg d D.s M) D N ρ t ∧
      eLpNorm ((selectedLaw P (b15c_regProcess Y) t).rnDeriv (movT_Q (b15c_gReg d D.s M) D N ρ t))
          (ENNReal.ofReal (p t)) (movT_Q (b15c_gReg d D.s M) D N ρ t) ≤
        eLpNorm ((selectedLaw P (b15c_regProcess Y) 0).rnDeriv (movT_Q (b15c_gReg d D.s M) D N ρ 0))
            (ENNReal.ofReal (p 0)) (movT_Q (b15c_gReg d D.s M) D N ρ 0) *
          ENNReal.ofReal (Real.exp (d3phi_gain c Cs L p t)) := by
  intro t ht
  obtain ⟨Vk, hVs, hVg, hVl⟩ := movb_smooth_approx hV2
  have hVk2 : ∀ k, Torus.IsCk 2 (Vk k) := fun k => movb_isCk_of_smooth' (hVs k)
  obtain ⟨Yk, hYk, hmarg⟩ := movb_exists_approx_solutions hW' D hV2 M hT.le hY₀ hY Vk hVk2 hVg
  obtain ⟨C, hC0, hCdiff⟩ := movb_srcReg_withV_diff hN0 D hM hκ hV2 M hρt hpos
  set ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hεdef
  have hεpos : ∀ k, 0 < ε k := fun k => by positivity
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set Csk : ℕ → ℝ := fun k => Cs + c * C * ε k / ℓ with hCsk
  have hCsk0 : Tendsto Csk atTop (𝓝 Cs) := by
    have : Tendsto (fun k => Cs + c * C * ε k / ℓ) atTop (𝓝 (Cs + c * C * 0 / ℓ)) :=
      tendsto_const_nhds.add ((hε0.const_mul (c * C)).div_const ℓ)
    simpa using this
  -- probability facts
  have hprobYk : ∀ k r, IsProbabilityMeasure (selectedLaw P (b15c_regProcess (Yk k)) r) := fun k r =>
    b15b_selectedLaw_isProb (fun s => b15c_regProcess_measurable (hYk k) s) r
  have hprobY : ∀ r : ℝ, IsProbabilityMeasure (selectedLaw P (b15c_regProcess Y) r) := fun r =>
    b15b_selectedLaw_isProb (fun s => b15c_regProcess_measurable hY s) r
  have hQprob : ∀ r ∈ Set.Icc (0 : ℝ) T,
      IsProbabilityMeasure (movT_Q (b15c_gReg d D.s M) D N ρ r) := fun r hr => by
    haveI : IsProbabilityMeasure (withDensityReal (ρ r)) := isProb_withDensityReal (hdens r hr)
    have hg : Continuous (b15c_gReg d D.s M) :=
      b15c_isSmooth_continuous (b15c_gReg_isSmooth (b15_one_le_d D) D.hs0 D.hsd M)
    exact modulatedGibbs_prob_of_continuous hg _ _
  have hP0 : ∀ k, selectedLaw P (b15c_regProcess (Yk k)) 0 = selectedLaw P (b15c_regProcess Y) 0 :=
    fun k => by rw [b15e_selectedLaw_zero_of_init (hYk k), b15e_selectedLaw_zero_of_init hY]
  -- the level-k exponential bounds
  have hexpk : ∀ k, ∀ r ∈ Set.Icc 0 T, ∫⁻ X : Config d N,
      ENNReal.ofReal (Real.exp (c * |movT_srcReg (b15e_withV D (Vk k)) N M ρ ρt r X| / L r))
        ∂(movT_Q (b15c_gReg d (b15e_withV D (Vk k)).s M) (b15e_withV D (Vk k)) N ρ r) ≤
          ENNReal.ofReal (Real.exp (Csk k)) := by
    intro k r hr
    have hLr : ℓ ≤ L r := hL r hr
    have hLpos : 0 < L r := hℓ.trans_le hLr
    have hpt : ∀ X : Config d N,
        ENNReal.ofReal (Real.exp (c * |movT_srcReg (b15e_withV D (Vk k)) N M ρ ρt r X| / L r)) ≤
          ENNReal.ofReal (Real.exp (c * |movT_srcReg D N M ρ ρt r X| / L r)) *
            ENNReal.ofReal (Real.exp (c * C * ε k / ℓ)) := by
      intro X
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
      have h1 := hCdiff (Vk k) (hVk2 k) (ε k) (hεpos k).le (hVg k) (hVl k) r hr X
      have h2 : |movT_srcReg (b15e_withV D (Vk k)) N M ρ ρt r X| ≤
          |movT_srcReg D N M ρ ρt r X| + C * ε k := by
        have := abs_sub_abs_le_abs_sub (movT_srcReg (b15e_withV D (Vk k)) N M ρ ρt r X)
          (movT_srcReg D N M ρ ρt r X)
        linarith
      have h3 : c * |movT_srcReg (b15e_withV D (Vk k)) N M ρ ρt r X| / L r ≤
          c * |movT_srcReg D N M ρ ρt r X| / L r + c * (C * ε k) / L r := by
        rw [← add_div, ← mul_add]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hc.le) hLpos.le
      have h4 : c * (C * ε k) / L r ≤ c * C * ε k / ℓ := by
        rw [← mul_assoc]
        exact div_le_div_of_nonneg_left (by have := hεpos k; positivity) hℓ hLr
      linarith
    calc _ ≤ ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (c * |movT_srcReg D N M ρ ρt r X| / L r)) *
            ENNReal.ofReal (Real.exp (c * C * ε k / ℓ))
          ∂(movT_Q (b15c_gReg d D.s M) D N ρ r) := lintegral_mono hpt
      _ = (∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (c * |movT_srcReg D N M ρ ρt r X| / L r))
          ∂(movT_Q (b15c_gReg d D.s M) D N ρ r)) * ENNReal.ofReal (Real.exp (c * C * ε k / ℓ)) :=
          lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (Real.exp Cs) * ENNReal.ofReal (Real.exp (c * C * ε k / ℓ)) :=
          mul_le_mul' (hexp r hr) le_rfl
      _ = ENNReal.ofReal (Real.exp (Csk k)) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  -- the level-k bounds
  have hlev : ∀ k, ∀ t ∈ Set.Icc 0 T,
      selectedLaw P (b15c_regProcess (Yk k)) t ≪ movT_Q (b15c_gReg d D.s M) D N ρ t ∧
      eLpNorm ((selectedLaw P (b15c_regProcess (Yk k)) t).rnDeriv
          (movT_Q (b15c_gReg d D.s M) D N ρ t)) (ENNReal.ofReal (p t))
          (movT_Q (b15c_gReg d D.s M) D N ρ t) ≤
        eLpNorm ((selectedLaw P (b15c_regProcess Y) 0).rnDeriv (movT_Q (b15c_gReg d D.s M) D N ρ 0))
            (ENNReal.ofReal (p 0)) (movT_Q (b15c_gReg d D.s M) D N ρ 0) *
          ENNReal.ofReal (Real.exp (d3phi_gain c (Csk k) L p t)) := by
    intro k t' ht'
    have := movT_lp_reg_bound_smooth_of_d3phi hNd hN0 hW' (b15e_withV D (Vk k)) hM hκ (hVs k) hT hρt
      hdens hpos M hY₀ (hYk k) hc hℓ hL hLi (hexpk k) hp (by rw [hP0 k]; exact hac)
      (by rw [hP0 k]; exact hfin) t' ht'
    rw [hP0 k] at this
    exact this
  -- the limit
  haveI := hQprob t ht
  haveI := hprobY t
  haveI := hprobYk
  set a := eLpNorm ((selectedLaw P (b15c_regProcess Y) 0).rnDeriv (movT_Q (b15c_gReg d D.s M) D N ρ 0))
    (ENNReal.ofReal (p 0)) (movT_Q (b15c_gReg d D.s M) D N ρ 0) with ha
  set J : ℝ := ∫ r in (0 : ℝ)..t, L r * ((p r - 1) / p r) with hJ
  have hgain : Tendsto (fun k => ENNReal.ofReal (Real.exp (d3phi_gain c (Csk k) L p t))) atTop
      (𝓝 (ENNReal.ofReal (Real.exp (d3phi_gain c Cs L p t)))) := by
    have h1 : Tendsto (fun k => d3phi_gain c (Csk k) L p t) atTop (𝓝 (d3phi_gain c Cs L p t)) := by
      simp only [d3phi_gain_eq]
      exact (hCsk0.div_const c).mul_const J
    exact ENNReal.tendsto_ofReal (Real.continuous_exp.continuousAt.tendsto.comp h1)
  have hliminf : liminf (fun k => eLpNorm ((selectedLaw P (b15c_regProcess (Yk k)) t).rnDeriv
          (movT_Q (b15c_gReg d D.s M) D N ρ t)) (ENNReal.ofReal (p t))
          (movT_Q (b15c_gReg d D.s M) D N ρ t)) atTop ≤
      a * ENNReal.ofReal (Real.exp (d3phi_gain c Cs L p t)) := by
    calc _ ≤ liminf (fun k => a * ENNReal.ofReal (Real.exp (d3phi_gain c (Csk k) L p t))) atTop :=
          liminf_le_liminf (Eventually.of_forall fun k => (hlev k t ht).2)
      _ = _ := (ENNReal.Tendsto.const_mul hgain (Or.inr hfin.ne)).liminf_eq
  have hlt : liminf (fun k => eLpNorm ((selectedLaw P (b15c_regProcess (Yk k)) t).rnDeriv
          (movT_Q (b15c_gReg d D.s M) D N ρ t)) (ENNReal.ofReal (p t))
          (movT_Q (b15c_gReg d D.s M) D N ρ t)) atTop < ⊤ :=
    lt_of_le_of_lt hliminf (ENNReal.mul_lt_top hfin ENNReal.ofReal_lt_top)
  have hp1 : 1 < p t := hp.gt_one t ht
  obtain ⟨hacT, hle⟩ := movT_lp_lsc (ν := selectedLaw P (b15c_regProcess Y) t)
    (νn := fun k => selectedLaw P (b15c_regProcess (Yk k)) t)
    (Qn := fun _ => movT_Q (b15c_gReg d D.s M) D N ρ t)
    (hν := fun φ hφ => hmarg t ht φ hφ) (hQ := fun φ _ => tendsto_const_nhds)
    (Eventually.of_forall fun k => (hlev k t ht).1) hp1 hlt
  exact ⟨hacT, hle.trans hliminf⟩


theorem d3phi_movT_pPath_zero (c p₀ : ℝ) (L : ℝ → ℝ) (hp₀ : 1 < p₀) : movT_pPath c p₀ L 0 = p₀ := by
  have hp0 : p₀ ≠ 0 := by intro h; rw [h] at hp₀; linarith
  simp only [movT_pPath, intervalIntegral.integral_same, mul_zero, Real.exp_zero, mul_one, sub_sub_cancel,
    one_div_one_div]

theorem d3phi_movT_lpGain_zero (c Cs p₀ : ℝ) (L : ℝ → ℝ) : movT_lpGain c Cs p₀ L 0 = 0 := by
  simp [movT_lpGain]

/-- **`movT_lp_reg_bound`, conditional on the D3PHI packets** (`d3phi_lp_bound`, hence `d3phi_identity_classical`):
the statement of `HRS.movT_lp_reg_bound` (`MovSpec2.lean:176`) verbatim. -/
theorem movT_lp_reg_bound_of_d3phi {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (hN : 2 ≤ N) {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hW' : IsBrownianFiltration P ℱ W') {D : DynData d} {T : ℝ} {ρ ρt : ℝ → Torus d → ℝ}
    (htr : MovTraj D T ρ) (hρt : IsC12Test T ρ ρt) (M : ℝ) (hM : 0 ≤ M) {Y₀ : Ω → Fin N → Euc d}
    (hY₀ : ∀ t : ℝ, Measurable[ℱ t] Y₀) {Y : ℝ → Ω → (Fin N → Euc d)}
    (hY : IsAdditiveSDESolution P ℱ W' (fun _ => b15c_liftedDriftReg D M) (liftedNoise D) Y₀
      (fun _ => ⊤) Y)
    {c Cs ℓ : ℝ} (hc : 0 < c) (hℓ : 0 < ℓ) {L : ℝ → ℝ} (hL : ∀ r ∈ Set.Icc 0 T, ℓ ≤ L r)
    (hLi : IntegrableOn L (Set.Icc 0 T))
    (hexp : ∀ r ∈ Set.Icc 0 T, ∫⁻ X : Config d N,
      ENNReal.ofReal (Real.exp (c * |movT_srcReg D N M ρ ρt r X| / L r))
        ∂(movT_Q (b15c_gReg d D.s M) D N ρ r) ≤ ENNReal.ofReal (Real.exp Cs))
    {p₀ : ℝ} (hp₀ : 1 < p₀)
    (hac : selectedLaw P (b15c_regProcess Y) 0 ≪ movT_Q (b15c_gReg d D.s M) D N ρ 0)
    (hfin : eLpNorm ((selectedLaw P (b15c_regProcess Y) 0).rnDeriv (movT_Q (b15c_gReg d D.s M) D N ρ 0))
      (ENNReal.ofReal p₀) (movT_Q (b15c_gReg d D.s M) D N ρ 0) < ⊤) :
    ∀ t ∈ Set.Icc 0 T,
      selectedLaw P (b15c_regProcess Y) t ≪ movT_Q (b15c_gReg d D.s M) D N ρ t ∧
      eLpNorm ((selectedLaw P (b15c_regProcess Y) t).rnDeriv (movT_Q (b15c_gReg d D.s M) D N ρ t))
          (ENNReal.ofReal (movT_pPath c p₀ L t)) (movT_Q (b15c_gReg d D.s M) D N ρ t) ≤
        eLpNorm ((selectedLaw P (b15c_regProcess Y) 0).rnDeriv (movT_Q (b15c_gReg d D.s M) D N ρ 0))
            (ENNReal.ofReal p₀) (movT_Q (b15c_gReg d D.s M) D N ρ 0) *
          ENNReal.ofReal (Real.exp (movT_lpGain c Cs p₀ L t)) := by
  intro t ht
  have hT0 : 0 ≤ T := ht.1.trans ht.2
  rcases ht.1.eq_or_lt with h0 | hpos0
  · subst h0
    refine ⟨hac, ?_⟩
    rw [d3phi_movT_pPath_zero c p₀ L hp₀, d3phi_movT_lpGain_zero]
    simp
  · have hTpos : 0 < T := hpos0.trans_le ht.2
    have hN0 : 0 < N := by omega
    have hNd : 1 ≤ N * d := Nat.mul_pos hN0 (b15_one_le_d D)
    have hdens : ∀ r ∈ Set.Icc (0 : ℝ) T, IsProbDensity (ρ r) := fun r hr => htr.mf.density r hr
    have hL0 : ∀ r ∈ Set.Icc 0 T, 0 ≤ L r := fun r hr => hℓ.le.trans (hL r hr)
    have hpath := d3phi_movT_path hc hp₀ hL0 hLi hT0
    have hp00 := d3phi_movT_pPath_zero c p₀ L hp₀
    have key := movT_lp_reg_bound_pos_of_d3phi hN0 hNd hW' D htr.gradient htr.pos_temp htr.V_reg hTpos hρt
      hdens htr.pos M hY₀ hY hc hℓ hL hLi hexp hpath hac (by rw [hp00]; exact hfin) t ht
    rw [hp00, d3phi_movT_gain hc hp₀ hL0 hLi ht] at key
    exact key

example := (@movT_lp_reg_bound_of_d3phi : type_of% @HRS.movT_lp_reg_bound)

end HRS
