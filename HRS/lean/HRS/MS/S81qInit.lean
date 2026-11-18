import HRS.MS.S81pAssemble
import HRS.MS.WsStatAux32
import HRS.MS.WsInitGAux11
import HRS.MS.GenPathAux53
import HRS.MS.S88BDTie
import HRS.MS.S88BDF01
import HRS.MS.QsfStat1
import HRS.MS.FinNoiseAux5
import HRS.MS.S88BDP01
import HRS.MS.S81qLinear

/-!
# S8.1 (worker S81Q): the physical initial term `I^u` and its decay

Namespace `HRS.Whole.S81Q`, prefix `s81q_`.

For the critical thermal density `ρ`, a canonical law `P_{N,β}` of the initial configuration `X₀` and `u ≥ 1`, the **physical initial term**
of the Duhamel decomposition of the window `ζ_N^{u+·}` is the `B_m`-valued process

`I^u(t)_α = √N ( μ_N(X₀)(U_{u+t} φ_α) - ∫ U_{u+t} φ_α d m_N )`,  `φ_α = oscTestFun m α`, `m_N = firstMarginal (law X₀)`,

with the classical adjoint orbit `U_{s} φ = propagatorW (critCoeff d a β ρ) 0 s φ`.
A *continuous* `B_m`-valued version is the evaluation of the continuous `K`-space vector `s56k0 … (√N) (μ_N(X₀)) (E μ_N)` along the horizon
`u+T` (`s56EvalPath`), extended by the clamp `s56Ext` beyond `[0,u+T]`.

* `s81q_k0_coord`: the coordinates of `s56k0` (any `m`, any orbit family with `MemCb 2`);
* `s81q_initial_term`: the process `Ip`, defined for every time, continuous for every `ω`, measurable, with the coordinate formula
  (`= s88Particle`) for `t ∈ [0,T]` and the decay `‖processWindow m T 0 Ip‖_{L²(P)} ≤ K e^{-c u}` (from `s88_particle_decay`);
* `s81q_proc_comp`, `s81q_L2_comp`: transport of such a process along a measure preserving enlargement `π : Ω'' → Ω`.
-/

set_option autoImplicit false
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff
open HRS HRS.Whole HRS.MS.GenPath HRS.MS.S88Breakdown HRS.Whole.S81P

namespace HRS.Whole.S81Q

variable {d : ℕ}

/-- The adjoint input `OscAdjointInput` of the critical coefficients at every `m ≥ wholeSpaceIndex d` and every horizon. -/
theorem s81q_adj (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρ) {m : ℝ}
    (hm : (wholeSpaceIndex d : ℝ) ≤ m) (T : ℝ) (hT : 0 ≤ T) :
    OscAdjointInput (critCoeff d a β ρ) m T := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hsd : (d : ℝ) / 2 < d := by linarith
  have hρeq : ρ = thermalDensity d ((d : ℝ) / 2) a β :=
    HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ
  have hSch : IsSchwartzDensity ρ := by
    rw [hρeq]; exact HRS.MS.S21.s21_schwartz_thermal hd hs0 hsd ha hβ
  have hQ : (a • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm := by
    unfold Matrix.IsSymm; simp
  rw [HRS.MS.S85.s85_crit_eq, HRS.MS.S85.s85_coeff_fv _ hQ]
  refine HRS.MS.S21.s21_oscAdjointInput hd hs0 hsd (inv_pos.2 hβ) _ hQ hSch T hT m ?_
  have h1 : ((24 * d + 240 : ℕ) : ℝ) = 24 * (d : ℝ) + 240 := by push_cast; ring
  have h2 : (wholeSpaceIndex d : ℝ) = 24 * (d : ℝ) + 240 := h1
  linarith

/-- The coordinates of `s56k0` along the orbit family (any `m`). -/
theorem s81q_k0_coord {C : WholeCoeff d} {m T : ℝ} (hC : OscAdjointInput C m T) (σ : ℝ)
    (hmeas : ∀ a : Fin d, Measurable fun z : Euc d => gradFeature C m T a 0 z)
    {Bf : ℝ} (hBf : 0 ≤ Bf) (hbd : ∀ (a : Fin d) (z : Euc d), ‖gradFeature C m T a 0 z‖ ≤ Bf)
    (hcb : ∀ α : MultiIndex d, ∀ t ∈ Set.Icc (0 : ℝ) T, MemCb 2 (propagatorW C 0 t (oscTestFun m α)))
    (ν μ' : Measure (Euc d)) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ']
    (hν : Integrable (fun x : Euc d => ‖x‖) ν) (hμ : Integrable (fun x : Euc d => ‖x‖) μ')
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (α : MultiIndex d) :
    OscDual.coord ((s56k0 C m T σ ν μ').evalA t) α =
      σ * (HRS.Whole.pair ν (propagatorW C 0 t (oscTestFun m α)) -
        HRS.Whole.pair μ' (propagatorW C 0 t (oscTestFun m α))) := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  obtain ⟨hcd, hbdd⟩ := hcb α t ht
  obtain ⟨B, hB⟩ := hbdd 0 (Nat.zero_le _)
  have hh : ContDiff ℝ 1 (propagatorW C 0 t (oscTestFun m α)) := hcd.of_le (by norm_num)
  rw [HRS.MS.S52.s52_coord_evalA ht.1 ht.2]
  rw [s56_k0_inner C m T σ Bf hBf hmeas hbd ν μ' hν hμ (HRS.MS.S52.s52y1 m T t α)
    (propagatorW C 0 t (oscTestFun m α)) hh B
    (fun z => by
      have h1 : ‖iteratedFDeriv ℝ 0 (propagatorW C 0 t (oscTestFun m α)) z‖ ≤ B := hB ⟨z, rfl⟩
      rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h1)
    (fun a z => by
      rw [HRS.MS.S52.s52_pair_grad_y1 hC ht.2 a h0 z α]
      simp [ht.1])]
  rfl

/-- The sup-norm of a continuous window is bounded by the supremum of the pointwise norms. -/
theorem s81q_enorm_window_le {m T : ℝ} {Ω : Type*} (Y : ℝ → Ω → OscDual d m) (ζ : Ω)
    (hc : Continuous fun t => Y t ζ) :
    ‖processWindow m T 0 Y ζ‖ₑ ≤ ⨆ t : Set.Icc (0 : ℝ) T, ‖Y t ζ‖ₑ := by
  set R : ℝ≥0∞ := ⨆ t : Set.Icc (0 : ℝ) T, ‖Y t ζ‖ₑ with hR
  rcases eq_or_ne R ⊤ with h | h
  · rw [h]; exact le_top
  have hcw : Continuous fun t : Set.Icc (0 : ℝ) T => Y (0 + (t : ℝ)) ζ := by
    simp only [zero_add]
    exact hc.comp continuous_subtype_val
  have hw : processWindow m T 0 Y ζ =
      (⟨fun t : Set.Icc (0 : ℝ) T => Y (0 + (t : ℝ)) ζ, hcw⟩ : C(Set.Icc (0 : ℝ) T, OscDual d m)) := by
    unfold processWindow windowPathOf
    exact dif_pos hcw
  have hnorm : ‖processWindow m T 0 Y ζ‖ ≤ R.toReal := by
    rw [hw]
    refine (ContinuousMap.norm_le _ ENNReal.toReal_nonneg).2 fun t => ?_
    have : ‖Y (0 + (t : ℝ)) ζ‖ₑ ≤ R := by
      simpa using le_iSup (fun t : Set.Icc (0 : ℝ) T => ‖Y t ζ‖ₑ) t
    have h2 := ENNReal.toReal_mono h this
    simpa [toReal_enorm] using h2
  calc ‖processWindow m T 0 Y ζ‖ₑ = ENNReal.ofReal ‖processWindow m T 0 Y ζ‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal R.toReal := ENNReal.ofReal_le_ofReal hnorm
    _ = R := ENNReal.ofReal_toReal h

/-- **The physical initial term and its decay.**  For every `u ≥ 1` the process `Ip t ζ = (J ζ)(u+t)` (`J = s56EvalPath (s56k0 …)` clamped
outside `[0,u+T]`) is measurable, continuous in `t` for every `ζ`, has the coordinates
`√N (μ_N(X₀ ζ)(U_{u+t}φ_α) - ∫ U_{u+t}φ_α d m_N)` for `t ∈ [0,T]`, and `‖Ip‖_{L²(P; 𝒳_T)} ≤ K e^{-cu}` (`K, c` before `ρ, N, P, u`). -/
theorem s81q_initial_term (hd : 2 ≤ d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) (m : ℝ)
    (hm : (wholeSpaceIndex d : ℝ) ≤ m) (T : ℝ) (hT : 0 < T) :
    ∃ K c : ℝ, 0 < c ∧ ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ →
      ∀ N : ℕ, 2 ≤ N → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → EucConfig d N), Measurable X₀ →
        law P X₀ = HRS.Whole.canonicalGibbs (rieszKernel d ((d : ℝ) / 2)) (confinement a) N β →
        ∀ u : ℝ, 1 ≤ u →
          ∃ Ip : ℝ → Ω → OscDual d m,
            S81PProc P T Ip ∧ (∀ ζ, Continuous fun t => Ip t ζ) ∧
            (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (α : MultiIndex d) (ζ : Ω),
              OscDual.coord (Ip t ζ) α =
                Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical (X₀ ζ))
                    (propagatorW (critCoeff d a β ρβ) 0 (u + t) (oscTestFun m α)) -
                  ∫ x, propagatorW (critCoeff d a β ρβ) 0 (u + t) (oscTestFun m α) x
                    ∂(HRS.Whole.firstMarginal (law P X₀)))) ∧
            s81p_L2 P (processWindow m T 0 Ip) ≤ ENNReal.ofReal (K * Real.exp (-c * u)) := by
  classical
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hsd : (d : ℝ) / 2 < d := by linarith
  obtain ⟨Cs, hCs0, hLin⟩ := s81q_linear_input hd ha hβ
  obtain ⟨cc, bb, hc, hb, hsum, hall⟩ := s88_orbit_envelopes hd a β ha hβ m hm
  refine ⟨s88Constant T Cs bb, cc, hc, fun ρβ hρβ N hN Ω _ P _ X₀ hX₀ hlaw u hu => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hN0 : 0 < N := by omega
  obtain ⟨hreg, henv⟩ := hall ρβ hρβ
  obtain ⟨Cs', hCs0', hStat⟩ := S45.s45_static_all hd hs0 hsd ha hβ
  have hSN := hStat N hN
  set Pc : Measure (EucConfig d N) :=
    HRS.Whole.canonicalGibbs (rieszKernel d ((d : ℝ) / 2)) (confinement a) N β with hPc
  haveI hPcp : IsProbabilityMeasure Pc := hSN.prob
  have hvar := (hLin ρβ hρβ N hN P X₀ hX₀ hlaw).2
  have hdecay := s88_particle_decay hd a β ha hβ m ρβ hρβ cc bb hb hsum hreg henv T Cs u hT hu N hN P X₀
    hlaw hvar
  set C := critCoeff d a β ρβ with hC
  have hT' : 0 < u + T := by linarith
  obtain ⟨B, hB0, hfd⟩ := HRS.MS.FinNoise.s86_feat_data hd a β ha hβ m hm (u + T) hT'
  obtain ⟨hfeat, hbound⟩ := hfd ρβ hρβ
  have hmeasG : ∀ i : Fin d, Measurable fun z : Euc d => gradFeature C m (u + T) i 0 z := fun i =>
    (hfeat.cont i 0 ⟨le_rfl, hT'.le⟩).measurable
  have hbdG : ∀ (i : Fin d) (z : Euc d), ‖gradFeature C m (u + T) i 0 z‖ ≤ B := fun i z => by
    have := hbound i 0 z
    simpa using this
  have hCadj := s81q_adj hd ha hβ hρβ hm (u + T) hT'.le
  have hcb : ∀ α : MultiIndex d, ∀ t ∈ Set.Icc (0 : ℝ) (u + T),
      MemCb 2 (propagatorW C 0 t (oscTestFun m α)) := fun α t ht => hreg.memCb α t ht.1
  -- integrability of the mean empirical measure
  obtain ⟨M₂, hM₂0, -, hM₂mom⟩ := HRS.MS.S21.s21_second_moment_stationary hd hs0 hsd ha hβ
  have hνint : Integrable (fun z : Euc d => ‖z‖) (HRS.Whole.meanEmpirical Pc) := by
    have h := HRS.MS.S21.s21g_meanEmp_norm_integrable (d := d) (N := N) hN0 Pc
      (id : EucConfig d N → EucConfig d N) measurable_id
      (lt_of_le_of_lt (hM₂mom N hN Pc id measurable_id (by simp [HRS.law, hPc])) ENNReal.ofReal_lt_top)
    simpa using h
  haveI : IsProbabilityMeasure (HRS.Whole.meanEmpirical Pc) :=
    HRS.Whole.meanEmpirical_isProbabilityMeasure Pc hN1
  have hmean : HRS.Whole.meanEmpirical Pc = HRS.Whole.firstMarginal (law P X₀) := by
    rw [hlaw]; exact HRS.Whole.meanEmpirical_eq_firstMarginal Pc hSN.exch hN1
  set J : EucConfig d N → OscPath d m (u + T) := fun x =>
    s56EvalPath hT'.le (s56k0 C m (u + T) (Real.sqrt N) (HRS.Whole.empirical x)
      (HRS.Whole.meanEmpirical Pc)) with hJ
  have hJm : Measurable J :=
    (s56EvalPath hT'.le).continuous.measurable.comp
      (s56_k0_meas C m (u + T) (Real.sqrt N) B hB0 hmeasG hbdG hN0 (HRS.Whole.meanEmpirical Pc) hνint)
  set Ip : ℝ → Ω → OscDual d m := fun t ζ => s56Ext hT'.le (J (X₀ ζ)) (u + t) with hIp
  have hcont : ∀ ζ, Continuous fun t => Ip t ζ := fun ζ =>
    (s56Ext_cont hT'.le (J (X₀ ζ))).comp (continuous_const.add continuous_id)
  have hcoord : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (α : MultiIndex d) (ζ : Ω),
      OscDual.coord (Ip t ζ) α = s88Particle P X₀ (s88Orbit C m (u + t) α) ζ := by
    intro t ht α ζ
    have ht' : u + t ∈ Set.Icc (0 : ℝ) (u + T) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    haveI := HRS.Whole.empirical_isProbabilityMeasure hN0 (X₀ ζ)
    have hνi : Integrable (fun z : Euc d => ‖z‖) (HRS.Whole.empirical (X₀ ζ)) :=
      HRS.Whole.Q09A.integrable_empirical hN1 (X₀ ζ) _
    have h1 : Ip t ζ = (s56k0 C m (u + T) (Real.sqrt N) (HRS.Whole.empirical (X₀ ζ))
        (HRS.Whole.meanEmpirical Pc)).evalA (u + t) := by
      simp only [hIp, hJ]
      rw [s56Ext_of_mem hT'.le _ ht']
      rfl
    rw [h1, s81q_k0_coord hCadj (Real.sqrt N) hmeasG hB0 hbdG hcb _ _ hνi hνint ht' α, hmean]
    rfl
  refine ⟨Ip, ⟨fun t => s56Ext_meas hT'.le (fun ζ => J (X₀ ζ)) (hJm.comp hX₀) (u + t),
    Filter.Eventually.of_forall fun ζ => (hcont ζ).continuousOn⟩, hcont, ?_, ?_⟩
  · intro t ht α ζ
    rw [hcoord t ht α ζ]
    rfl
  · rw [s81p_L2_eq]
    refine le_trans ?_ hdecay
    refine ENNReal.rpow_le_rpow (lintegral_mono fun ζ => ?_) (by norm_num)
    have h1 := s81q_enorm_window_le (m := m) (T := T) Ip ζ (hcont ζ)
    have h2 : (⨆ t : Set.Icc (0 : ℝ) T, ‖Ip t ζ‖ₑ) = ⨆ t : Set.Icc (0 : ℝ) T,
        HRS.Whole.l2NormE (fun α : MultiIndex d =>
          s88Particle P X₀ (s88Orbit (critCoeff d a β ρβ) m (u + t.1) α) ζ) := by
      refine iSup_congr fun t => ?_
      rw [s56_enorm_eq_l2NormE]
      congr 1
      funext α
      exact hcoord t.1 t.2 α ζ
    rw [h2] at h1
    calc ‖processWindow m T 0 Ip ζ‖ₑ ^ (2 : ℝ) ≤ (⨆ t : Set.Icc (0 : ℝ) T,
        HRS.Whole.l2NormE (fun α : MultiIndex d =>
          s88Particle P X₀ (s88Orbit (critCoeff d a β ρβ) m (u + t.1) α) ζ)) ^ (2 : ℝ) :=
          ENNReal.rpow_le_rpow h1 (by norm_num)
      _ = _ := by rw [ENNReal.rpow_two]

/-- Transport of a continuous measurable process along a measure preserving map. -/
theorem s81q_proc_comp {Ω Ω'' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω''] {P : Measure Ω}
    {Q : Measure Ω''} {π : Ω'' → Ω} (hπ : MeasurePreserving π Q P) {m T : ℝ}
    {Y : ℝ → Ω → OscDual d m} (hY : S81PProc P T Y) : S81PProc Q T (fun t ζ => Y t (π ζ)) :=
  ⟨fun t => (hY.1 t).comp hπ.measurable, hπ.quasiMeasurePreserving.ae hY.2⟩

/-- The `L²` size of the window is invariant under measure preserving transport. -/
theorem s81q_L2_comp {Ω Ω'' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω''] {P : Measure Ω}
    {Q : Measure Ω''} {π : Ω'' → Ω} (hπ : MeasurePreserving π Q P) {m T : ℝ} (hT : 0 ≤ T)
    {Y : ℝ → Ω → OscDual d m} (hY : S81PProc P T Y) :
    s81p_L2 Q (processWindow m T 0 (fun t ζ => Y t (π ζ))) = s81p_L2 P (processWindow m T 0 Y) := by
  unfold s81p_L2
  congr 1
  have hae : AEMeasurable (fun ζ => ENNReal.ofReal (‖processWindow m T 0 Y ζ‖ ^ (2 : ℝ))) P :=
    ENNReal.measurable_ofReal.comp_aemeasurable (((hY.aemeasurable hT).norm).pow_const (2 : ℝ))
  have hae' : AEMeasurable (fun ζ => ENNReal.ofReal (‖processWindow m T 0 Y ζ‖ ^ (2 : ℝ)))
      (Measure.map π Q) := by rw [hπ.map_eq]; exact hae
  have := lintegral_map' hae' (hπ.aemeasurable)
  rw [hπ.map_eq] at this
  exact this.symm

end HRS.Whole.S81Q
