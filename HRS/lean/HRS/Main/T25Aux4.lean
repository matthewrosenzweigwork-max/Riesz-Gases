import HRS.Main.T25Aux3
import HRS.Sections.DynCmpAux3

/-!
# T25-IN, part 4 (ENT-IN): `P:eq:pair-input` and `P:eq:linear-input`

TeX M L6546-6557.  For the actual particle law `f_N^t` of a system on a horizon `T`, uniformly in `t ∈ [0,T]`, `T`, `N ≥ 2`, the
system and the initial law (the entropy input being the horizon-uniform `t25_entropy_uniform`):

* `t25_pair_input` (`P:eq:pair-input`): for symmetric measurable `h` with `|h| ≤ D w` (`w = g + c_*`, off the diagonal):
  `E[N |F_N^h(X_N^t, μ^t)|] ≤ C D B_N` (and integrability).  Step 1 is the single-time `t25_pair_entropy`:
  `E_ν[N|F^h|] ≤ C D (H(ν|Q^t) + Nδ_N)` for every law `ν` of finite entropy (`movlog_expmoment` + the entropy inequality
  `movspec_int_le`; the kernel `h` is repaired on the diagonal and divided by `D` exactly as in `movfin_movlog_pair_core`).
* `t25_linear_input` (`P:eq:linear-input`): for measurable `|b| ≤ K`: `E|μ_N^t(b) - μ^t(b)| ≤ C K √(B_N/N)`
  (Hoeffding + Donsker-Varadhan `dyncmp_linear_entropy` with `H(f^t|(μ^t)^{⊗N}) ≤ C B_N`).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace T25

variable {d : ℕ}

/-- `P:eq:pair-input`, single-time entropy form: for every probability law `ν` on `Config d N` with
`H(ν | Q_N^t) < ∞`, symmetric measurable `h` with `|h(x,y)| ≤ D (g(x-y) + c_*)` for `x ≠ y`:
`N F_N^h(·, μ^t)` is `ν`-integrable and `E_ν[N|F_N^h|] ≤ C D (H(ν|Q_N^t) + Nδ_N)`, `C = C(trajectory, c_*)`. -/
theorem t25_pair_entropy (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (cstar : ℝ)
    (hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + cstar) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ t : ℝ, 0 ≤ t →
      ∀ ν : Measure (Config d N), IsProbabilityMeasure ν →
        relEntropy ν (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ t))) ≠ ⊤ →
        ∀ D : ℝ, 0 ≤ D → ∀ h : Torus d → Torus d → ℝ, Measurable (Function.uncurry h) →
          (∀ x y, h x y = h y x) →
          (∀ x y, x ≠ y → |h x y| ≤ D * (periodicRiesz d s (x - y) + cstar)) →
          Integrable (fun X : Config d N => (N : ℝ) * modulatedEnergy h X (withDensityReal (ρ t))) ν ∧
          ∫ X, |(N : ℝ) * modulatedEnergy h X (withDensityReal (ρ t))| ∂ν ≤
            C * D * ((relEntropy ν (modulatedGibbs (periodicRiesz d s) N β
              (withDensityReal (ρ t)))).toReal + N * deltaN d s N) := by
  have hd1 : 1 ≤ d := by omega
  have hs0 := htr.hs0
  have hsd := htr.hsd
  set cs : ℝ := max cstar (1 - periodicRiesz d s 0) with hcs
  have hcsc : cstar ≤ cs := le_max_left _ _
  have hw1 : ∀ z : Torus d, 1 ≤ periodicRiesz d s z + cs := fun z => by
    by_cases hz : z = 0
    · subst hz
      have : 1 - periodicRiesz d s 0 ≤ cs := le_max_right _ _
      linarith
    · have := hw z hz; linarith
  obtain ⟨c, C0, hc, hC0, Hexp⟩ := MovLog.movlog_expmoment hd htr cs hw1
  refine ⟨(1 + C0) / c, by positivity, fun N hN t ht ν hν hfinν D hD h hm hsym hdom => ?_⟩
  have hN0 : 0 < N := by omega
  have hQ : ∀ r : ℝ, movT_Q (periodicRiesz d s) htr.dyn N ρ r =
      modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ r)) :=
    fun r => movT_Q_eq_beta (D := htr.dyn) (β := β) (by simp [IsSmoothPositiveTrajectory.dyn, PDE.mfData]) N ρ r
  set μt : Measure (Torus d) := withDensityReal (ρ t) with hμt
  set Q : Measure (Config d N) := modulatedGibbs (periodicRiesz d s) N β μt with hQdef
  have hNδ1 : 1 ≤ (N : ℝ) * deltaN d s N := one_le_mul_deltaN hs0 N (by omega)
  have hρd := (MovLog.movlog_traj htr t).mf.density t ⟨ht, le_rfl⟩
  have hcont : Continuous (ρ t) :=
    mova_continuous_of_isCk ((MovLog.movlog_traj htr t).ck t ⟨ht, le_rfl⟩)
  haveI := isProb_withDensityReal hρd
  haveI : IsProbabilityMeasure Q := by
    rw [hQdef, ← hQ t]; exact movfin_movT_Q_isProb hN (MovLog.movlog_traj htr t) ⟨ht, le_rfl⟩
  have hνQ : ν ≪ Q := (klDiv_ne_top_iff.1 hfinν).1
  have hQπ : Q ≪ Measure.pi (fun _ : Fin N => μt) := by
    rw [hQdef, movf_modGibbs_eq_tilted hd1 hs0 hsd hρd hcont hN0 htr.hβ.le]
    exact tilted_absolutelyContinuous _ _
  have hinj : ∀ᵐ Y ∂ν, ∀ i j, i ≠ j → Y i ≠ Y j :=
    hνQ.ae_le (hQπ.ae_le (ae_injective_pi (withDensityReal_singleton hd1 (ρ t))))
  set H : ℝ := (relEntropy ν Q).toReal with hH
  have hH0 : 0 ≤ H := ENNReal.toReal_nonneg
  rcases hD.eq_or_lt with h0 | hpos
  · -- D = 0: the kernel vanishes off the diagonal, so the energy vanishes ν-a.e.
    subst h0
    have hz : (fun X : Config d N => (N : ℝ) * modulatedEnergy h X μt) =ᵐ[ν] fun _ => 0 := by
      filter_upwards [hinj] with X hX
      have e1 : modulatedEnergy h X μt = modulatedEnergy (fun _ _ => (0 : ℝ)) X μt :=
        modulatedEnergy_congr_offdiag (withDensityReal_singleton hd1 (ρ t))
          (fun x y hxy => by
            have := hdom x y hxy
            rw [zero_mul] at this
            simpa using abs_nonpos_iff.1 this) X hX
      rw [e1]
      simp [modulatedEnergy]
    refine ⟨(integrable_zero _ _ _).congr hz.symm, ?_⟩
    have : ∫ X, |(N : ℝ) * modulatedEnergy h X μt| ∂ν = 0 := by
      rw [integral_congr_ae (g := fun _ => (0 : ℝ)) (by filter_upwards [hz] with X hX; simp [hX])]
      simp
    rw [this]
    simp
  · -- D > 0: repaired kernel, exponential moment, entropy inequality
    set hk : Torus d → Torus d → ℝ := fun x y => if x = y then 0 else D⁻¹ * h x y with hhk
    have hkm : Measurable (Function.uncurry hk) := by
      have : Function.uncurry hk = fun p : Torus d × Torus d =>
          if p.1 = p.2 then 0 else D⁻¹ * Function.uncurry h p := by
        funext p; rfl
      rw [this]
      exact Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const
        (measurable_const.mul hm)
    have hks : ∀ x y, hk x y = hk y x := fun x y => by
      by_cases hxy : x = y
      · subst hxy; rfl
      · simp only [hhk, if_neg hxy, if_neg (Ne.symm hxy)]; rw [hsym x y]
    have hkd : ∀ x y, |hk x y| ≤ 1 * (periodicRiesz d s (x - y) + cs) := fun x y => by
      by_cases hxy : x = y
      · simp only [hhk, if_pos hxy, abs_zero]
        have := hw1 (x - y); linarith
      · simp only [hhk, if_neg hxy]
        have h1 := hdom x y hxy
        rw [abs_mul, abs_of_pos (inv_pos.2 hpos)]
        calc D⁻¹ * |h x y| ≤ D⁻¹ * (D * (periodicRiesz d s (x - y) + cstar)) :=
              mul_le_mul_of_nonneg_left h1 (inv_pos.2 hpos).le
          _ = periodicRiesz d s (x - y) + cstar := by field_simp
          _ ≤ 1 * (periodicRiesz d s (x - y) + cs) := by linarith
    obtain ⟨hEm, hEx⟩ := Hexp N hN t ht hk hkm hks hkd
    set Z : Config d N → ℝ := fun Y => (N : ℝ) * modulatedEnergy hk Y μt with hZ
    have hZm : Measurable Z := measurable_const.mul hEm
    have hEx' : ∫⁻ Y, ENNReal.ofReal (Real.exp (c * |Z Y|)) ∂Q ≤
        ENNReal.ofReal (Real.exp (C0 * ((N : ℝ) * deltaN d s N))) := by
      refine le_trans (le_of_eq ?_) hEx
      refine lintegral_congr fun Y => ?_
      have e : c * |Z Y| = c * N * |modulatedEnergy hk Y μt| := by
        simp only [hZ, abs_mul, abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]; ring
      rw [e]
    have hfinν' : klDiv ν Q ≠ ⊤ := hfinν
    obtain ⟨hZi, hZb⟩ := movspec_int_le ν Q hZm.aemeasurable hZm.aemeasurable hc hEx' hfinν'
    have hcongr : (fun X : Config d N => (N : ℝ) * modulatedEnergy h X μt) =ᵐ[ν]
        fun X => D • Z X := by
      filter_upwards [hinj] with X hX
      have e1 : modulatedEnergy hk X μt =
          modulatedEnergy (fun x y => D⁻¹ * h x y) X μt :=
        modulatedEnergy_congr_offdiag (withDensityReal_singleton hd1 (ρ t))
          (fun x y hxy => by simp only [hhk, if_neg hxy]) _ hX
      rw [MovLog.movlog_modEnergy_smul] at e1
      simp only [hZ, smul_eq_mul, e1]
      field_simp
    refine ⟨(hZi.smul D).congr hcongr.symm, ?_⟩
    have e2 : ∫ X, |(N : ℝ) * modulatedEnergy h X μt| ∂ν = D * ∫ X, |Z X| ∂ν := by
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [hcongr] with X hX
      rw [hX, smul_eq_mul, abs_mul, abs_of_pos hpos]
    rw [e2]
    have hb : ∫ X, |Z X| ∂ν ≤ (1 + C0) / c * (H + (N : ℝ) * deltaN d s N) := by
      have hZb' : ∫ X, |Z X| ∂ν ≤ (H + C0 * ((N : ℝ) * deltaN d s N)) / c := hZb
      refine hZb'.trans ?_
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hc]
      nlinarith [mul_nonneg hC0 hH0, mul_nonneg hC0 (by linarith : 0 ≤ (N : ℝ) * deltaN d s N)]
    calc D * ∫ X, |Z X| ∂ν ≤ D * ((1 + C0) / c * (H + (N : ℝ) * deltaN d s N)) :=
          mul_le_mul_of_nonneg_left hb hD
      _ = _ := by ring

/-- Bound for the centred linear statistic. -/
theorem t25_lin_bound {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {b : Torus d → ℝ} {K : ℝ}
    (hbK : ∀ x, |b x| ≤ K) {N : ℕ} (hN : 0 < N) (X : Config d N) :
    |(1 / (N : ℝ)) * ∑ i, b (X i) - ∫ x, b x ∂μ| ≤ 2 * K := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hm : |∫ x, b x ∂μ| ≤ K := by
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := b) (C := K)
      (Filter.Eventually.of_forall fun x => by simpa using hbK x)
    simpa using this
  have h1 : |(1 / (N : ℝ)) * ∑ i, b (X i)| ≤ K := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / N)]
    calc 1 / (N : ℝ) * |∑ i, b (X i)| ≤ 1 / (N : ℝ) * ∑ i, |b (X i)| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
      _ ≤ 1 / (N : ℝ) * ∑ i : Fin N, K :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hbK _) (by positivity)
      _ = K := by simp; field_simp
  calc _ ≤ |(1 / (N : ℝ)) * ∑ i, b (X i)| + |∫ x, b x ∂μ| := abs_sub _ _
    _ ≤ 2 * K := by linarith

/-- `P:eq:pair-input` for the actual particle law (TeX M L6551-6553): uniformly in the horizon `T`, `t ∈ [0,T]`, `N ≥ 2`, the
system, the initial law and `h` with `|h| ≤ D w`:  `E[N|F_N^h(X_N^t, μ^t)|] ≤ C D B_N`. -/
theorem t25_pair_input (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (cstar : ℝ)
    (hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + cstar) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ T : ℝ, 0 ≤ T →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsParticleSystem P htr.dyn T X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        relEntropy (P.map X₀)
          (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) ≠ ⊤ →
        ∀ D : ℝ, 0 ≤ D → ∀ h : Torus d → Torus d → ℝ, Measurable (Function.uncurry h) →
          (∀ x y, h x y = h y x) →
          (∀ x y, x ≠ y → |h x y| ≤ D * (periodicRiesz d s (x - y) + cstar)) →
          ∀ t ∈ Set.Icc (0 : ℝ) T,
            Integrable (fun ω => (N : ℝ) *
              modulatedEnergy h (X t.toNNReal ω) (withDensityReal (ρ t))) P ∧
            ∫ ω, |(N : ℝ) * modulatedEnergy h (X t.toNNReal ω) (withDensityReal (ρ t))| ∂P ≤
              C * D * entropyScale d s N (P.map X₀)
                (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := t25_pair_entropy hd htr cstar hw
  obtain ⟨C₂, hC₂0, hC₂⟩ := t25_entropy_uniform hd htr
  refine ⟨C₁ * (C₂ + 1), by positivity, ?_⟩
  intro N hN T hT Ω _ P _ X₀ W X hP hfilt hfin D hD h hm hsym hdom t ht
  have hXm : Measurable (X t.toNNReal) := hP.sol.adapted _
  haveI : IsProbabilityMeasure (P.map (X t.toNNReal)) :=
    (Measure.isProbabilityMeasure_map_iff hXm.aemeasurable).2 inferInstance
  have hsum := hC₂ N hN T hT P X₀ W X hP hfilt hfin t ht
  set B : ℝ := entropyScale d s N (P.map X₀)
    (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) with hB
  have hδ : 1 ≤ (N : ℝ) * deltaN d s N := one_le_mul_deltaN htr.hs0 N (by omega)
  have hH0 : 0 ≤ (relEntropy (P.map X₀)
      (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0)))).toReal :=
    ENNReal.toReal_nonneg
  have hBge : (N : ℝ) * deltaN d s N ≤ B := by rw [hB]; unfold entropyScale; linarith
  have hB1 : 1 ≤ B := by rw [hB]; unfold entropyScale; linarith
  have hle1 : relEntropy (P.map (X t.toNNReal))
      (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ t))) ≤ ENNReal.ofReal (C₂ * B) :=
    le_trans le_self_add hsum
  have hfinν : relEntropy (P.map (X t.toNNReal))
      (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ t))) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle1
  have hHle : (relEntropy (P.map (X t.toNNReal))
      (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ t)))).toReal ≤ C₂ * B := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle1
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  obtain ⟨hint, hbd⟩ := hC₁ N hN t ht.1 (P.map (X t.toNNReal)) inferInstance hfinν D hD h hm hsym hdom
  refine ⟨(integrable_map_measure hint.aestronglyMeasurable hXm.aemeasurable).1 hint, ?_⟩
  have hI := integral_map hXm.aemeasurable hint.abs.aestronglyMeasurable
  have e : ∫ ω, |(N : ℝ) * modulatedEnergy h (X t.toNNReal ω) (withDensityReal (ρ t))| ∂P =
      ∫ Y, |(N : ℝ) * modulatedEnergy h Y (withDensityReal (ρ t))| ∂(P.map (X t.toNNReal)) := by
    rw [integral_map hXm.aemeasurable (f := fun Y => |(N : ℝ) * modulatedEnergy h Y (withDensityReal (ρ t))|)
      hint.abs.aestronglyMeasurable]
  rw [e]
  refine hbd.trans ?_
  have : C₁ * D * ((relEntropy (P.map (X t.toNNReal))
      (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ t)))).toReal + N * deltaN d s N) ≤
      C₁ * D * (C₂ * B + B) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC₁0 hD)
  refine this.trans (le_of_eq ?_)
  ring

/-- `P:eq:linear-input` for the actual particle law (TeX M L6554-6557): for measurable `|b| ≤ K`,
`E|μ_N^t(b) - μ^t(b)| ≤ C K √(B_N/N)`, uniformly in the horizon, `t ∈ [0,T]`, `N ≥ 2`, the system and the initial law. -/
theorem t25_linear_input (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ T : ℝ, 0 ≤ T →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsParticleSystem P htr.dyn T X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        relEntropy (P.map X₀)
          (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) ≠ ⊤ →
        ∀ b : Torus d → ℝ, Measurable b → ∀ K : ℝ, 0 ≤ K → (∀ x, |b x| ≤ K) →
          ∀ t ∈ Set.Icc (0 : ℝ) T,
            Integrable (fun ω => |(1 / (N : ℝ)) * ∑ i, b (X t.toNNReal ω i) -
              ∫ x, b x ∂(withDensityReal (ρ t))|) P ∧
            ∫ ω, |(1 / (N : ℝ)) * ∑ i, b (X t.toNNReal ω i) - ∫ x, b x ∂(withDensityReal (ρ t))| ∂P ≤
              C * K * Real.sqrt (entropyScale d s N (P.map X₀)
                (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) / N) := by
  obtain ⟨C₂, hC₂0, hC₂⟩ := t25_entropy_uniform hd htr
  refine ⟨Real.sqrt (2 * C₂ + 2), Real.sqrt_nonneg _, ?_⟩
  intro N hN T hT Ω _ P _ X₀ W X hP hfilt hfin b hb K hK hbK t ht
  have hN0 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hXm : Measurable (X t.toNNReal) := hP.sol.adapted _
  haveI : IsProbabilityMeasure (P.map (X t.toNNReal)) :=
    (Measure.isProbabilityMeasure_map_iff hXm.aemeasurable).2 inferInstance
  have hρd := (MovLog.movlog_traj htr T).mf.density t ht
  haveI := isProb_withDensityReal hρd
  have hsum := hC₂ N hN T hT P X₀ W X hP hfilt hfin t ht
  set B : ℝ := entropyScale d s N (P.map X₀)
    (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) with hB
  have hδ : 1 ≤ (N : ℝ) * deltaN d s N := one_le_mul_deltaN htr.hs0 N (by omega)
  have hH0 : 0 ≤ (relEntropy (P.map X₀)
      (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0)))).toReal :=
    ENNReal.toReal_nonneg
  have hB1 : 1 ≤ B := by rw [hB]; unfold entropyScale; linarith
  have hle1 : relEntropy (P.map (X t.toNNReal)) (Measure.pi fun _ : Fin N => withDensityReal (ρ t)) ≤
      ENNReal.ofReal (C₂ * B) := le_trans le_add_self hsum
  have hfinν : relEntropy (P.map (X t.toNNReal)) (Measure.pi fun _ : Fin N => withDensityReal (ρ t)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle1
  have hHle : (relEntropy (P.map (X t.toNNReal))
      (Measure.pi fun _ : Fin N => withDensityReal (ρ t))).toReal ≤ C₂ * B := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle1
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  have hlin := dyncmp_linear_entropy (μ := withDensityReal (ρ t)) hb hK hbK hN0
    (ν := P.map (X t.toNNReal)) hfinν
  have hSm : Measurable (fun Y : Config d N => |(1 / (N : ℝ)) * ∑ i, b (Y i) -
      ∫ x, b x ∂(withDensityReal (ρ t))|) :=
    ((measurable_const.mul (Finset.measurable_sum _ fun i _ => hb.comp (measurable_pi_apply i))).sub
      measurable_const).abs
  have hint : Integrable (fun ω => |(1 / (N : ℝ)) * ∑ i, b (X t.toNNReal ω i) -
      ∫ x, b x ∂(withDensityReal (ρ t))|) P := by
    refine Integrable.of_bound ((hSm.comp hXm).aestronglyMeasurable) (2 * K)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_abs]
    exact t25_lin_bound hbK hN0 _
  refine ⟨hint, ?_⟩
  have e : ∫ ω, |(1 / (N : ℝ)) * ∑ i, b (X t.toNNReal ω i) - ∫ x, b x ∂(withDensityReal (ρ t))| ∂P =
      ∫ Y, |(1 / (N : ℝ)) * ∑ i, b (Y i) - ∫ x, b x ∂(withDensityReal (ρ t))|
        ∂(P.map (X t.toNNReal)) := by
    rw [integral_map hXm.aemeasurable (f := fun Y : Config d N => |(1 / (N : ℝ)) * ∑ i, b (Y i) -
      ∫ x, b x ∂(withDensityReal (ρ t))|) hSm.aestronglyMeasurable]
  rw [e]
  refine hlin.trans ?_
  have hlog : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9; linarith
  have h1 : 2 * ((relEntropy (P.map (X t.toNNReal))
      (Measure.pi fun _ : Fin N => withDensityReal (ρ t))).toReal + Real.log 2) / N ≤
      (2 * C₂ + 2) * (B / N) := by
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hNr]
    nlinarith
  have h2 : Real.sqrt (2 * ((relEntropy (P.map (X t.toNNReal))
      (Measure.pi fun _ : Fin N => withDensityReal (ρ t))).toReal + Real.log 2) / N) ≤
      Real.sqrt (2 * C₂ + 2) * Real.sqrt (B / N) := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt h1
  calc K * Real.sqrt (2 * ((relEntropy (P.map (X t.toNNReal))
        (Measure.pi fun _ : Fin N => withDensityReal (ρ t))).toReal + Real.log 2) / N)
      ≤ K * (Real.sqrt (2 * C₂ + 2) * Real.sqrt (B / N)) := mul_le_mul_of_nonneg_left h2 hK
    _ = _ := by ring

end T25

end HRS

end
