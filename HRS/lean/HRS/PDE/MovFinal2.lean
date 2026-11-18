import HRS.PDE.MovFinal1

/-!
# MOV-FINAL (part 2): the `L^p` glue re-run with the relocated packet proofs

Verbatim copies of `mov_lp_ineq`, `mov_lp_bound` (`HRS/PDE/MovSpec2.lean`) with frozen packets replaced by `_proof`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

/-- **`mov_lp_ineq_proof` (variable-exponent `L^p` bound along the moving reference).**  For the particle system `MovHyp`
and any `(c, Cs, ℓ, L)` such that the regularised sources satisfy the scaled exponential bound `MovSrcScaled`
(`P:eq:source-exp`, M L6670), with `‖h_0‖_{L^{p₀}(Q_0)} < ∞`, `h_0 = df_N^0/dQ_N^0`: for all `t ∈ [0,T]`,
`f_N^t ≪ Q_N^t` and `‖h_N^t‖_{L^{p(t)}(Q_N^t)} ≤ ‖h_N^0‖_{L^{p₀}(Q_N^0)} exp(movT_lpGain)`, `movT_lpGain = (Cs/c)∫_0^t L(p-1)/p dr`, with the exponent path
`p = movT_pPath c p₀ L` (`P:eq:p-ode`).  This is `P:eq:lognorm-derivative` (M L6692-6695), integrated and exponentiated,
for the *unregularised* particle system; `f_N^t ≪ Q_N^t` is part of the conclusion so that `h_N^t` is the genuine density.
Proof: `movT_regSeq_exists_proof`, `movT_lp_reg_bound_proof` for each level, `movT_lp_init_limsup_proof`, `movT_lp_lsc_proof` along
`b15c_marginal_tendsto`, `movT_Q_tendsto_weak_proof`. -/
theorem mov_lp_ineq_proof (hN : 2 ≤ N) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {D : DynData d} {T : ℝ} {ρ ρt : ℝ → Torus d → ℝ} {X₀ : Ω → Config d N}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (h : MovHyp P D N T ρ X₀ W X) (hρt : IsC12Test T ρ ρt)
    {c Cs ℓ : ℝ} (hc : 0 < c) (hℓ : 0 < ℓ) {L : ℝ → ℝ} (hL : ∀ r ∈ Set.Icc 0 T, ℓ ≤ L r)
    (hLi : IntegrableOn L (Set.Icc 0 T)) (hexp : MovSrcScaled D N ρ ρt T c Cs L)
    {p₀ : ℝ} (hp₀ : 1 < p₀)
    (hac : P.map X₀ ≪ movT_Q (periodicRiesz d D.s) D N ρ 0)
    (hfin : eLpNorm ((P.map X₀).rnDeriv (movT_Q (periodicRiesz d D.s) D N ρ 0)) (ENNReal.ofReal p₀)
      (movT_Q (periodicRiesz d D.s) D N ρ 0) < ⊤) :
    ∀ t ∈ Set.Icc 0 T,
      P.map (X t.toNNReal) ≪ movT_Q (periodicRiesz d D.s) D N ρ t ∧
      eLpNorm ((P.map (X t.toNNReal)).rnDeriv (movT_Q (periodicRiesz d D.s) D N ρ t))
          (ENNReal.ofReal (movT_pPath c p₀ L t)) (movT_Q (periodicRiesz d D.s) D N ρ t) ≤
        eLpNorm ((P.map X₀).rnDeriv (movT_Q (periodicRiesz d D.s) D N ρ 0)) (ENNReal.ofReal p₀)
            (movT_Q (periodicRiesz d D.s) D N ρ 0) *
          ENNReal.ofReal (Real.exp (movT_lpGain c Cs p₀ L t)) := by
  intro t ht
  have hS := h.sol
  obtain ⟨ℱ, W', M, Y₀, Y, seq⟩ := movT_regSeq_exists_proof h
  haveI : IsProbabilityMeasure (P.map X₀) := inferInstance
  obtain ⟨hac_n, hlim0⟩ := movT_lp_init_limsup_proof hN (ht.1.trans ht.2) h.traj seq.levels seq.levels_nonneg hp₀ hac hfin
  obtain ⟨M₀, hM₀⟩ := hexp
  have hMev : ∀ᶠ n in atTop, M₀ ≤ M n := seq.levels.eventually_ge_atTop M₀
  have hL0 : ∀ r ∈ Set.Icc 0 T, 0 ≤ L r := fun r hr => hℓ.le.trans (hL r hr)
  set a := eLpNorm ((P.map X₀).rnDeriv (movT_Q (periodicRiesz d D.s) D N ρ 0)) (ENNReal.ofReal p₀)
    (movT_Q (periodicRiesz d D.s) D N ρ 0) with ha
  set E := ENNReal.ofReal (Real.exp (movT_lpGain c Cs p₀ L t)) with hE
  have hfinev : ∀ᶠ n in atTop,
      eLpNorm ((P.map X₀).rnDeriv (movT_Q (b15c_gReg d D.s (M n)) D N ρ 0)) (ENNReal.ofReal p₀)
        (movT_Q (b15c_gReg d D.s (M n)) D N ρ 0) < ⊤ :=
    hlim0.eventually (gt_mem_nhds hfin)
  have hbound : ∀ᶠ n in atTop, selectedLaw P (b15c_regProcess (Y n)) t ≪
      movT_Q (b15c_gReg d D.s (M n)) D N ρ t ∧
      eLpNorm ((selectedLaw P (b15c_regProcess (Y n)) t).rnDeriv
          (movT_Q (b15c_gReg d D.s (M n)) D N ρ t)) (ENNReal.ofReal (movT_pPath c p₀ L t))
        (movT_Q (b15c_gReg d D.s (M n)) D N ρ t) ≤
      eLpNorm ((P.map X₀).rnDeriv (movT_Q (b15c_gReg d D.s (M n)) D N ρ 0)) (ENNReal.ofReal p₀)
        (movT_Q (b15c_gReg d D.s (M n)) D N ρ 0) * E := by
    filter_upwards [hMev, hfinev] with n hn hnf
    have key := movT_lp_reg_bound_proof hN seq.brownian h.traj hρt (M n) (seq.levels_nonneg n)
      seq.init_adapted (seq.sol n) hc hℓ hL hLi (fun r hr => hM₀ (M n) hn r hr) hp₀
      (by rw [movT_reg_init_law seq n]; exact hac_n n)
      (by rw [movT_reg_init_law seq n]; exact hnf) t ht
    rw [movT_reg_init_law seq n] at key
    exact key
  haveI : ∀ n, IsProbabilityMeasure (selectedLaw P (b15c_regProcess (Y n)) t) := fun n =>
    b15b_selectedLaw_isProb (fun s => b15c_regProcess_measurable (seq.sol n) s) t
  haveI : ∀ n, IsProbabilityMeasure (movT_Q (b15c_gReg d D.s (M n)) D N ρ t) := fun n =>
    movT_QReg_isProb D h.traj (M n) ht
  haveI : IsProbabilityMeasure (P.map (X t.toNNReal)) :=
    inferInstance
  haveI : IsProbabilityMeasure (movT_Q (periodicRiesz d D.s) D N ρ t) := movfin_movT_Q_isProb hN h.traj ht
  have hliminf : liminf (fun n => eLpNorm ((selectedLaw P (b15c_regProcess (Y n)) t).rnDeriv
          (movT_Q (b15c_gReg d D.s (M n)) D N ρ t)) (ENNReal.ofReal (movT_pPath c p₀ L t))
        (movT_Q (b15c_gReg d D.s (M n)) D N ρ t)) atTop ≤ a * E := by
    calc _ ≤ liminf (fun n => eLpNorm ((P.map X₀).rnDeriv (movT_Q (b15c_gReg d D.s (M n)) D N ρ 0))
              (ENNReal.ofReal p₀) (movT_Q (b15c_gReg d D.s (M n)) D N ρ 0) * E) atTop :=
          liminf_le_liminf (hbound.mono fun n hn => hn.2)
      _ = a * E := (ENNReal.Tendsto.mul_const hlim0 (Or.inr ENNReal.ofReal_ne_top)).liminf_eq
  have hlt : liminf (fun n => eLpNorm ((selectedLaw P (b15c_regProcess (Y n)) t).rnDeriv
          (movT_Q (b15c_gReg d D.s (M n)) D N ρ t)) (ENNReal.ofReal (movT_pPath c p₀ L t))
        (movT_Q (b15c_gReg d D.s (M n)) D N ρ t)) atTop < ⊤ :=
    lt_of_le_of_lt hliminf (ENNReal.mul_lt_top hfin ENNReal.ofReal_lt_top)
  have hp := (movT_pPath_bounds hc hp₀ hL0 ht).1
  obtain ⟨hacT, hle⟩ := movT_lp_lsc_proof (ν := P.map (X t.toNNReal))
    (hν := fun φ hφ => b15c_marginal_tendsto hS seq.sol seq.eventually_eq ht.1 ht.2 hφ)
    (hQ := fun φ hφ => movT_Q_tendsto_weak_proof hN h.traj seq.levels seq.levels_nonneg ht hφ)
    (hbound.mono fun n hn => hn.1) hp hlt
  exact ⟨hacT, hle.trans hliminf⟩

/-- **`mov_lp_bound_proof`: Lemma 5.8, first assertion `P:eq:log-moment` (M L6642-6646) and Lemma 7.8 item 1 in the
`MovHyp` setting.**  Given the exponent `p₀ > 1`, the data of the pressure estimate (`s`, `β ∈ [βm,βp]`, `inf ρ ≥ c₀`,
`‖ρ^r‖_{C²} ≤ Λ₂`) and a bound `Λ₁` of `∫_0^T L` (`L(t) = ‖∇u^t‖_∞`, M L6660-6661, "the relaxation input gives
`∫_0^∞L < ∞`"), there are `p_∞ > 1` and `C` such that for every `N ≥ 2`, every system and every horizon `T`, if
`h_N^0 = df_N^0/dQ_N^0 ∈ L^{p₀}(Q_N^0)` then for all `t ∈ [0,T]` `f_N^t ≪ Q_N^t` and
`‖h_N^t‖_{L^{p_∞}(Q_N^t)} ≤ exp(C J_N)`, `J_N = 1 + Nδ_N + log‖h_N^0‖_{L^{p₀}(Q_N^0)}` (`logMomentScale`).
`L` is any positive-lower-bounded Lipschitz bound of `u^r` (consumers apply it to `L + η(T)`, `η(T) T ≤ 1`).
Constants independent of `T`, `N`, `L`, the system.  Discharges the "variable-exponent identity" and the
exponential-source steps of `moving_log_moment` (`Sec5.lean:357`) and `alltime_Lp` item 1 (`Sec7Fields.lean:70`). -/
theorem mov_lp_bound_proof (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ) (hβm : 0 < βm)
    (c₀ : ℝ) (hc₀ : 0 < c₀) (Λ₂ : ℝ) (p₀ : ℝ) (hp₀ : 1 < p₀) (Λ₁ : ℝ) (hΛ₁ : 0 ≤ Λ₁) :
    ∃ pInf C : ℝ, 1 < pInf ∧ 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ {Ω : Type*} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] {D : DynData d} {T : ℝ} {ρ ρt : ℝ → Torus d → ℝ}
      (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
      MovHyp P D N T ρ X₀ W X → IsC12Test T ρ ρt → D.s = s → D.invβ⁻¹ ∈ Set.Icc βm βp →
      (∀ r ∈ Set.Icc 0 T, ∀ x, c₀ ≤ ρ r x) →
      (∀ r ∈ Set.Icc 0 T, Torus.cbNorm 2 (ρ r) ≤ Λ₂) →
      ∀ L : ℝ → ℝ, (∃ ℓ : ℝ, 0 < ℓ ∧ ∀ r ∈ Set.Icc 0 T, ℓ ≤ L r) → IntegrableOn L (Set.Icc 0 T) →
      (∀ r ∈ Set.Icc 0 T, IsLipschitzVF (L r) (mfeTransport D (ρ r))) →
      ∫ r in Set.Icc 0 T, L r ≤ Λ₁ →
      P.map X₀ ≪ movT_Q (periodicRiesz d s) D N ρ 0 →
      eLpNorm ((P.map X₀).rnDeriv (movT_Q (periodicRiesz d s) D N ρ 0)) (ENNReal.ofReal p₀)
        (movT_Q (periodicRiesz d s) D N ρ 0) < ⊤ →
      ∀ t ∈ Set.Icc 0 T,
        P.map (X t.toNNReal) ≪ movT_Q (periodicRiesz d s) D N ρ t ∧
        eLpNorm ((P.map (X t.toNNReal)).rnDeriv (movT_Q (periodicRiesz d s) D N ρ t))
            (ENNReal.ofReal pInf) (movT_Q (periodicRiesz d s) D N ρ t) ≤
          ENNReal.ofReal (Real.exp (C * (1 + N * deltaN d s N + Real.log
            (eLpNorm ((P.map X₀).rnDeriv (movT_Q (periodicRiesz d s) D N ρ 0)) (ENNReal.ofReal p₀)
              (movT_Q (periodicRiesz d s) D N ρ 0)).toReal))) := by
  obtain ⟨c, C₂, hc, hscal⟩ := movT_source_exp_scaled_uniform_proof hd hs0 hsd βm βp hβm c₀ hc₀ Λ₂
  set Cp : ℝ := max C₂ 0 with hCp
  set q : ℝ := 1 - 1 / p₀ with hq
  have hp0 : 0 < p₀ := by linarith
  have hq0 : 0 < q := by rw [hq]; have : 1 / p₀ < 1 := (div_lt_one hp0).2 hp₀; linarith
  have hq1 : q < 1 := by
    have h : 0 < 1 / p₀ := by positivity
    rw [hq]; linarith
  set e₁ : ℝ := Real.exp (-(1 / c) * Λ₁) with he₁
  have he0 : 0 < e₁ := Real.exp_pos _
  have he1 : e₁ ≤ 1 := by
    rw [he₁]; apply Real.exp_le_one_iff.2
    have : 0 < 1 / c := by positivity
    nlinarith
  set pInf : ℝ := 1 / (1 - q * e₁) with hpInf
  have hden0 : 0 < 1 - q * e₁ := by nlinarith
  have hpInf1 : 1 < pInf := by
    rw [hpInf, lt_div_iff₀ hden0]; nlinarith [mul_pos hq0 he0]
  refine ⟨pInf, max 1 Cp, hpInf1, le_trans zero_le_one (le_max_left _ _), ?_⟩
  intro N hN Ω _ P _ D T ρ ρt X₀ W X hH hρt hDs hβ hc0 hΛ L hLℓ hLi hLip hint hac hfin t ht
  obtain ⟨ℓ, hℓ, hLℓ⟩ := hLℓ
  subst hDs
  haveI : IsProbabilityMeasure (P.map X₀) := inferInstance
  haveI : IsProbabilityMeasure (movT_Q (periodicRiesz d D.s) D N ρ 0) :=
    movfin_movT_Q_isProb hN hH.traj ⟨le_rfl, ht.1.trans ht.2⟩
  set a := eLpNorm ((P.map X₀).rnDeriv (movT_Q (periodicRiesz d D.s) D N ρ 0)) (ENNReal.ofReal p₀)
    (movT_Q (periodicRiesz d D.s) D N ρ 0) with ha
  have ha1 : 1 ≤ a := movspec_one_le_eLpNorm_rnDeriv _ _ hac hp₀.le
  have haTop : a ≠ ⊤ := hfin.ne
  have hat1 : 1 ≤ a.toReal := by
    have := ENNReal.toReal_mono haTop ha1
    simpa using this
  have hlog : 0 ≤ Real.log a.toReal := Real.log_nonneg hat1
  have hNδ : 0 ≤ (N : ℝ) * deltaN d D.s N := by
    have : 1 ≤ (N : ℝ) * deltaN d D.s N := one_le_mul_deltaN hs0 N (by omega)
    linarith
  have hapos : 0 < a.toReal := by linarith
  -- the degenerate case `T = 0` (`movT_source_exp_scaled_uniform_proof` needs `0 < T`): `t = 0`, `X 0 = X₀` a.s.
  rcases (ht.1.trans ht.2).eq_or_lt with hT0 | hTpos
  · have ht0 : t = 0 := le_antisymm (by have h2 := ht.2; rwa [← hT0] at h2) ht.1
    subst ht0
    have hXe : P.map (X (0 : ℝ).toNNReal) = P.map X₀ := by
      rw [Real.toNNReal_zero]
      exact Measure.map_congr (by filter_upwards [hH.sol.init] with ω hω; exact hω)
    rw [hXe]
    refine ⟨hac, ?_⟩
    have hpIle : pInf ≤ p₀ := by
      rw [hpInf, div_le_iff₀ hden0]
      have h1 : p₀ * q = p₀ - 1 := by rw [hq]; field_simp
      nlinarith [mul_nonneg (sub_nonneg.2 hp₀.le) (sub_nonneg.2 he1)]
    refine (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpIle)).trans ?_
    show a ≤ _
    calc a = ENNReal.ofReal a.toReal := (ENNReal.ofReal_toReal haTop).symm
      _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc a.toReal = Real.exp (Real.log a.toReal) := (Real.exp_log hapos).symm
          _ ≤ _ := by
            refine Real.exp_le_exp.2 ?_
            have hM1 : (1 : ℝ) ≤ max 1 Cp := le_max_left _ _
            nlinarith [mul_le_mul_of_nonneg_right hM1 (by linarith : 0 ≤ 1 + N * deltaN d D.s N + Real.log a.toReal)]
  have hsc := hscal hH.traj hρt hTpos rfl hβ hc0 hΛ L hℓ (fun r hr => ⟨hLℓ r hr, hLip r hr⟩) N hN
  obtain ⟨hacT, hle⟩ := mov_lp_ineq_proof hN P hH hρt hc hℓ hLℓ hLi hsc hp₀ hac hfin t ht
  refine ⟨hacT, ?_⟩
  have hL0 : ∀ r ∈ Set.Icc 0 T, 0 ≤ L r := fun r hr => hℓ.le.trans (hLℓ r hr)
  haveI : IsProbabilityMeasure (movT_Q (periodicRiesz d D.s) D N ρ t) := movfin_movT_Q_isProb hN hH.traj ht
  have hp_ge : pInf ≤ movT_pPath c p₀ L t := movT_pPath_ge hc hp₀ hL0 hLi ht hint
  have hm : AEStronglyMeasurable ((P.map (X t.toNNReal)).rnDeriv
      (movT_Q (periodicRiesz d D.s) D N ρ t)) (movT_Q (periodicRiesz d D.s) D N ρ t) :=
    (Measure.measurable_rnDeriv _ _).aestronglyMeasurable
  have h1 : eLpNorm ((P.map (X t.toNNReal)).rnDeriv (movT_Q (periodicRiesz d D.s) D N ρ t))
      (ENNReal.ofReal pInf) (movT_Q (periodicRiesz d D.s) D N ρ t) ≤
      eLpNorm ((P.map (X t.toNNReal)).rnDeriv (movT_Q (periodicRiesz d D.s) D N ρ t))
      (ENNReal.ofReal (movT_pPath c p₀ L t)) (movT_Q (periodicRiesz d D.s) D N ρ t) :=
    eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hp_ge)
  refine h1.trans (hle.trans ?_)
  -- the gain
  have hgain : movT_lpGain c (C₂ * N * deltaN d D.s N) p₀ L t ≤ Cp * (N * deltaN d D.s N) := by
    unfold movT_lpGain
    have hA : 0 ≤ (1 / c) * ∫ r in (0 : ℝ)..t, L r :=
      mul_nonneg (by positivity) (movT_intL_nonneg hL0 ht)
    have hE0 : 0 < Real.exp (-(1 / c) * ∫ r in (0 : ℝ)..t, L r) := Real.exp_pos _
    have hE1 : Real.exp (-(1 / c) * ∫ r in (0 : ℝ)..t, L r) ≤ 1 := by
      apply Real.exp_le_one_iff.2; nlinarith
    set κ : ℝ := (1 - 1 / p₀) * (1 - Real.exp (-(1 / c) * ∫ r in (0 : ℝ)..t, L r)) with hκ
    have hκ0 : 0 ≤ κ := mul_nonneg hq0.le (by linarith)
    have hκ1 : κ ≤ 1 := by
      rw [hκ]
      have : (1 - 1 / p₀) ≤ 1 := hq1.le
      nlinarith
    have hCs : C₂ * N * deltaN d D.s N ≤ Cp * (N * deltaN d D.s N) := by
      have : C₂ ≤ Cp := le_max_left _ _
      nlinarith
    have : C₂ * N * deltaN d D.s N * (1 - 1 / p₀) * (1 - Real.exp (-(1 / c) * ∫ r in (0 : ℝ)..t, L r)) =
        (C₂ * N * deltaN d D.s N) * κ := by rw [hκ]; ring
    rw [this]
    have hCp0 : 0 ≤ Cp * (N * deltaN d D.s N) := mul_nonneg (le_max_right _ _) hNδ
    rcases le_total 0 (C₂ * N * deltaN d D.s N) with hc2 | hc2
    · calc (C₂ * N * deltaN d D.s N) * κ ≤ (C₂ * N * deltaN d D.s N) * 1 :=
            mul_le_mul_of_nonneg_left hκ1 hc2
        _ ≤ _ := by linarith
    · have : (C₂ * N * deltaN d D.s N) * κ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc2 hκ0
      linarith
  -- assemble: a * exp(gain) ≤ exp(C J)
  have hfinal : a * ENNReal.ofReal (Real.exp (movT_lpGain c (C₂ * N * deltaN d D.s N) p₀ L t)) ≤
      ENNReal.ofReal (Real.exp (max 1 Cp * (1 + N * deltaN d D.s N + Real.log a.toReal))) := by
    rw [← ENNReal.ofReal_toReal haTop, ← ENNReal.ofReal_mul hapos.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have hx : a.toReal = Real.exp (Real.log a.toReal) := (Real.exp_log hapos).symm
    have hmul : a.toReal * Real.exp (movT_lpGain c (C₂ * N * deltaN d D.s N) p₀ L t) =
        Real.exp (Real.log a.toReal + movT_lpGain c (C₂ * N * deltaN d D.s N) p₀ L t) := by
      rw [Real.exp_add, ← hx]
    rw [hmul]
    refine Real.exp_le_exp.2 ?_
    have h3 : movT_lpGain c (C₂ * N * deltaN d D.s N) p₀ L t ≤ max 1 Cp * (N * deltaN d D.s N) :=
      hgain.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hNδ)
    have h4 : Real.log a.toReal ≤ max 1 Cp * Real.log a.toReal :=
      le_mul_of_one_le_left hlog (le_max_left _ _)
    have hM1 : 0 ≤ max 1 Cp := le_trans zero_le_one (le_max_left _ _)
    have hexpand : max 1 Cp * (1 + N * deltaN d D.s N + Real.log a.toReal) =
        max 1 Cp + max 1 Cp * (N * deltaN d D.s N) + max 1 Cp * Real.log a.toReal := by ring
    rw [ENNReal.toReal_ofReal hapos.le, hexpand]
    linarith
  exact hfinal

example := (@mov_lp_ineq_proof : type_of% @HRS.mov_lp_ineq)
example := (@mov_lp_bound_proof : type_of% @HRS.mov_lp_bound)

end HRS

end
