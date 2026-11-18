import HRS.Main.T25PAux32

/-!
# T25P, part 33: clause 3 of Theorem 2.5 (`C_T d₂^{E_m}(η_N^0, η°)` in place of the initial term)

Apply the core estimate with the identity coupling `η' = η_N^0` (initial term `0`) against the window law `Λ̄` of the re-based
linear solution started at `ν_N = law η_N^0`; compare `Λ̄` with the window law of `Y` (re-based at `ν`) through the common
Gaussian part `γ` (`t25_smoothDist_affine_le`), and conclude with the triangle inequality.
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory Complex
open scoped ENNReal NNReal BigOperators Matrix RealInnerProductSpace

namespace HRS.T25P

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.Main HRS.T25

variable {d : ℕ}

theorem t25p_comb2 {p2 q2 p3 q3 : ℝ} (h2 : 0 ≤ p2) (g2 : 0 ≤ q2) (h3 : 0 ≤ p3) (g3 : 0 ≤ q3) :
    ENNReal.ofReal p2 * ENNReal.ofReal q2 + ENNReal.ofReal p3 * ENNReal.ofReal q3 =
    ENNReal.ofReal (p2 * q2 + p3 * q3) := by
  rw [← ENNReal.ofReal_mul h2, ← ENNReal.ofReal_mul h3,
    ← ENNReal.ofReal_add (mul_nonneg h2 g2) (mul_nonneg h3 g3)]

theorem t25p_clause3 (S : PreparedData d) (m : ℝ) (hm : (d : ℝ) + 2 < m) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧
      ∀ a : ℝ, 0 ≤ a → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        SelectedFlow P S.dyn (a + T) X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        relEntropy (law P X₀) (S.refMeasure N 0) < ⊤ →
      ∀ (ν : Measure (NegSobolev d m)) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
        [IsProbabilityMeasure P'] (Y₀ : Ω' → NegSobolev d m) (Y : ℝ → Ω' → NegSobolev d m),
        IsPreparedLinear S m (a + T) ν P' Y₀ Y →
        smoothDist 2 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
          C * (smoothDist 2 (law P (fun ω => etaE m (X₀ ω) S.μ0)) ν +
            S.B N (law P X₀) / Real.sqrt N + Real.sqrt (S.B N (law P X₀) / N)) := by
  classical
  have hd : 2 ≤ d := S.hd
  have htr := t25_traj S
  have hm1 : (d : ℝ) / 2 + 2 < m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hm0 : (d : ℝ) / 2 < m := by linarith
  obtain ⟨Cr, cr, hCr, hcr, Vev, hdual, hpkg⟩ := t25p_ev_pkg hd htr m
  obtain ⟨Cmax, hCmax0, hEv⟩ := hpkg T hT
  obtain ⟨CΨ, hCΨ0, hΨ⟩ := t25p_Psi_L1 hd htr hm hcr hT
  obtain ⟨Ct, hCt0, hTr⟩ := t25p_trace_int hd htr hm hcr hT
  refine ⟨1 + Cr ^ 2 + Cr * CΨ + Cr ^ 2 / 2 * Ct, by positivity, ?_⟩
  intro a ha N hN Ω _ P _ X₀ W X hSel hfilt hrel ν Ω' _ P' _ Y₀ Y hY
  have hT' : 0 < a + T := by linarith
  have hplain : IsPlainEvolution Vev (a + T) := hEv.plain _ hT'.le
  have hKb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ a + T → ‖Vev t r‖ ≤ Cr := by
    intro r t hr hrt _
    refine (hEv.decay r t hr hrt).trans ?_
    have : Real.exp (-cr * (t - r)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    nlinarith
  have hb : ∀ t : ℝ, 0 ≤ t → t ≤ a + T → ‖Vev t 0‖ ≤ Cr := fun t ht0 htT => hKb 0 t le_rfl ht0 htT
  set B := S.B N (law P X₀) with hB
  have hB0 : 0 ≤ B := t25p_B_nonneg S hN (law P X₀)
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < N))
  have hXs := t25_isParticleSystem S hSel
  obtain ⟨ℱ, W', hF⟩ := hfilt
  have hX₀ae : AEMeasurable X₀ P := (hXs.sol.adapted 0).aemeasurable.congr hXs.sol.init
  have hent : relEntropy (P.map X₀)
      (modulatedGibbs (periodicRiesz d S.s) N S.β (withDensityReal (S.ρ 0))) ≠ ⊤ := hrel.ne
  have hgm := t25p_etaE_measurable S m hm0 N
  set νN : Measure (NegSobolev d m) := law P (fun ω => etaE m (X₀ ω) S.μ0) with hνN
  have hlin := t25_linear_of_prepared S hY
  have hY0 : Measurable Y₀ := hY.meas
  -- the Gaussian part and the re-based solutions
  obtain ⟨γ, hγ, hγlaw⟩ := t25p_rebase_law (Vev := Vev) hT ha hplain hCr.le hb P' Y₀ hY0 Y hlin.meas hlin.cont
  haveI := hγ
  have hprobνN : IsProbabilityMeasure νN := by
    rw [hνN]; infer_instance
  haveI : IsProbabilityMeasure ν := by rw [← hY.law_init]; infer_instance
  have hsolκ := fun (κ : Measure (NegSobolev d m)) (_ : IsProbabilityMeasure κ) =>
    t25p_rebase hd htr hT' hdual hplain hCr.le hKb P' Y₀ hY0 Y hlin κ
  set ΛY : Measure (PathSp T (NegSobolev d m)) := law P' (windowPath m T a Y) with hΛYdef
  set Λb : Measure (PathSp T (NegSobolev d m)) := law (P'.prod νN) (windowPath m T a
        (fun t (w : Ω' × NegSobolev d m) => Y t w.1 - Vev t 0 (Y₀ w.1) + Vev t 0 w.2)) with hΛbdef
  set Eη : Measure (PathSp T (NegSobolev d m)) := S.etaLaw m T a P X with hEη
  have hpΛY : IsProbabilityMeasure ΛY := by
    have h : IsProbabilityMeasure (P'.map (fun ω => (windowPath m T a Y ω : PathSp T (NegSobolev d m)))) :=
      inferInstance
    exact h
  have hpΛb : IsProbabilityMeasure Λb := by
    have h : IsProbabilityMeasure ((P'.prod νN).map (fun w => (windowPath m T a
        (fun t (w : Ω' × NegSobolev d m) => Y t w.1 - Vev t 0 (Y₀ w.1) + Vev t 0 w.2) w :
          PathSp T (NegSobolev d m)))) := inferInstance
    exact h
  have hpEη : IsProbabilityMeasure Eη := by
    have h : IsProbabilityMeasure (P.map (fun ω => (windowFluc m T a (Real.sqrt N) X S.ρ ω :
        PathSp T (NegSobolev d m)))) := inferInstance
    exact h
  haveI := hpΛY
  haveI := hpΛb
  haveI := hpEη
  -- (A) the window law of `Y`
  have hΛY : ΛY =
      (ν.prod γ).map (fun q : NegSobolev d m × PathSp T (NegSobolev d m) =>
        t25p_L ha Vev hplain.2.2 hCr.le hb q.1 + q.2) := by
    have h1 := t25p_lin_unique hd htr hT ha hdual hCr.le hKb P' (P'.prod ν) Y₀ hY0 Y hlin
      (fun w : Ω' × NegSobolev d m => w.2) measurable_snd
      (fun t w => Y t w.1 - Vev t 0 (Y₀ w.1) + Vev t 0 w.2) (hsolκ ν inferInstance)
      (by rw [Measure.map_snd_prod, measure_univ, one_smul]; exact hY.law_init)
    rw [hΛYdef]
    refine h1.trans ?_
    rw [← hγlaw ν]
    unfold law
    congr 1
  -- (B) the window law of the re-based solution started at `ν_N`
  have hΛb : Λb =
      (νN.prod γ).map (fun q : NegSobolev d m × PathSp T (NegSobolev d m) =>
        t25p_L ha Vev hplain.2.2 hCr.le hb q.1 + q.2) := by
    rw [hΛbdef, ← hγlaw νN]
    unfold law
    congr 1
  -- (C) comparison of the two window laws
  haveI : SecondCountableTopology (PathSp T (NegSobolev d m)) :=
    inferInstanceAs (SecondCountableTopology C(Set.Icc (0 : ℝ) T, NegSobolev d m))
  have hcmp := HRS.T25.t25_smoothDist_affine_le (t25p_L ha Vev hplain.2.2 hCr.le hb) νN ν γ
  have hLn : ‖t25p_L ha Vev hplain.2.2 hCr.le hb‖ ≤ Cr := t25p_norm_L_le ha Vev hplain.2.2 hCr.le hb
  have hmax : max 1 (‖t25p_L ha Vev hplain.2.2 hCr.le hb‖ ^ 2) ≤ 1 + Cr ^ 2 := by
    refine max_le (by nlinarith [sq_nonneg Cr]) ?_
    have := norm_nonneg (t25p_L ha Vev hplain.2.2 hCr.le hb)
    nlinarith
  -- (D) the core estimate with the identity coupling `η' = η_N^0`
  have hX0ℱ : Measurable[ℱ 0] (X (Real.toNNReal 0)) := by
    rw [Real.toNNReal_zero]
    have h := hF.adapted 0
    rwa [NNReal.coe_zero] at h
  have hflm0 : Measurable[ℱ 0] (fun ω => flucProc m (Real.sqrt N) X S.ρ 0 ω) :=
    ((gf_measurable_ofMeasureDiff_proof m hm0 (withDensityReal (S.ρ 0))).const_smul (Real.sqrt N)).comp hX0ℱ
  have hflu0 : ∀ᵐ ω ∂P, flucProc m (Real.sqrt N) X S.ρ 0 ω = etaE m (X₀ ω) S.μ0 := by
    filter_upwards [hXs.sol.init] with ω hω
    simp only [flucProc, Real.toNNReal_zero, hω, etaE, flucE, PreparedData.μ0, S.hρ_init]
  have hη'law : P.map (fun ω => flucProc m (Real.sqrt N) X S.ρ 0 ω) = νN := Measure.map_congr hflu0
  have hν₀ : (P'.prod νN).map (fun w : Ω' × NegSobolev d m => w.2) =
      P.map (fun ω => flucProc m (Real.sqrt N) X S.ρ 0 ω) := by
    rw [Measure.map_snd_prod, measure_univ, one_smul, hη'law]
  have hid := t25p_hid hd htr hm1 hT ha hCr hcr hdual hEv (P'.prod νN)
    (fun w : Ω' × NegSobolev d m => w.2) measurable_snd
    (fun t (w : Ω' × NegSobolev d m) => Y t w.1 - Vev t 0 (Y₀ w.1) + Vev t 0 w.2)
    (hsolκ νN hprobνN) (P.map (fun ω => flucProc m (Real.sqrt N) X S.ρ 0 ω)) hν₀
    (law (P'.prod νN) (windowPath m T a
      (fun t (w : Ω' × NegSobolev d m) => Y t w.1 - Vev t 0 (Y₀ w.1) + Vev t 0 w.2))) rfl
  have core := t25p_core_gen hd htr hm hT hCr hcr hdual hEv hN ha P X₀ W X hXs ℱ W' hF
    (fun ω => flucProc m (Real.sqrt N) X S.ρ 0 ω) hflm0 _ hid
  obtain ⟨c1, -⟩ := core
  have hz : ∫⁻ ω, ‖flucProc m (Real.sqrt N) X S.ρ 0 ω - flucProc m (Real.sqrt N) X S.ρ 0 ω‖ₑ ∂P = 0 := by
    simp
  rw [hz, mul_zero, zero_add] at c1
  have hPsi := hΨ N hN a ha P X₀ W X hXs ⟨ℱ, W', hF⟩ hent
  have hBe : entropyScale d S.s N (law P X₀)
      (modulatedGibbs (periodicRiesz d S.s) N S.β (withDensityReal (S.ρ 0))) = B := rfl
  rw [hBe] at hPsi
  obtain ⟨Mart, Z, hM, -⟩ := t25p_stage1 hd htr hm hT hCr hcr hdual hEv hN ha P X₀ W X hXs ℱ W' hF
  have hTr' := hTr N hN a ha P X₀ W X hXs ⟨ℱ, W', hF⟩ hent ℱ Mart hM
  rw [hBe] at hTr'
  have hPsi' : ∫⁻ ω, ENNReal.ofReal Cr * t25p_Psi d S.s S.ρ m cr a T X ω ∂P ≤
      ENNReal.ofReal Cr * ENNReal.ofReal (CΨ * B / Real.sqrt N) := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact mul_le_mul' le_rfl hPsi
  have c2 := c1.trans (add_le_add hPsi' (mul_le_mul' le_rfl hTr'))
  rw [t25p_comb2 hCr.le (by positivity) (by positivity) (by positivity)] at c2
  have hd1 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 c2
  -- (E) identification of the left-hand law
  have hLe : law P (Uniform.windowPath a T (flucProc m (Real.sqrt N) X S.ρ)) = Eη := by
    rw [hEη]
    unfold PreparedData.etaLaw
    refine congrArg (fun f => P.map f) ?_
    funext ω
    exact (t25_windowFluc_eq m T a (Real.sqrt N) ha X S.ρ ω).symm
  rw [hLe] at hd1
  -- (F) the triangle inequality
  have htri : smoothDist 2 Eη ΛY ≤ smoothDist 2 Eη Λb + smoothDist 2 Λb ΛY :=
    smoothDist_triangle 2 Eη Λb ΛY
  have h2 : smoothDist 2 Λb ΛY ≤ (1 + Cr ^ 2) * smoothDist 2 νN ν := by
    rw [hΛb, hΛY]
    exact hcmp.trans (mul_le_mul_of_nonneg_right hmax (smoothDist_nonneg 2 νN ν))
  have hsd0 : 0 ≤ smoothDist 2 νN ν := smoothDist_nonneg 2 νN ν
  have hf0 : 0 ≤ B / Real.sqrt N := by positivity
  have hg0 : 0 ≤ Real.sqrt (B / N) := Real.sqrt_nonneg _
  have hcg : CΨ * B / Real.sqrt N = CΨ * (B / Real.sqrt N) := mul_div_assoc _ _ _
  rw [hcg] at hd1
  have k2 : Cr * (CΨ * (B / Real.sqrt N)) ≤ (1 + Cr ^ 2 + Cr * CΨ + Cr ^ 2 / 2 * Ct) * (B / Real.sqrt N) := by
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ hf0
    have : 0 ≤ Cr ^ 2 / 2 * Ct := by positivity
    nlinarith [sq_nonneg Cr]
  have k3 : Cr ^ 2 / 2 * (Ct * Real.sqrt (B / N)) ≤ (1 + Cr ^ 2 + Cr * CΨ + Cr ^ 2 / 2 * Ct) * Real.sqrt (B / N) := by
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ hg0
    have : 0 ≤ Cr * CΨ := by positivity
    nlinarith [sq_nonneg Cr]
  have k1 : (1 + Cr ^ 2) * smoothDist 2 νN ν ≤ (1 + Cr ^ 2 + Cr * CΨ + Cr ^ 2 / 2 * Ct) * smoothDist 2 νN ν := by
    refine mul_le_mul_of_nonneg_right ?_ hsd0
    have : 0 ≤ Cr * CΨ := by positivity
    have : 0 ≤ Cr ^ 2 / 2 * Ct := by positivity
    linarith
  have hfinal : smoothDist 2 Eη ΛY ≤ (1 + Cr ^ 2 + Cr * CΨ + Cr ^ 2 / 2 * Ct) *
      (smoothDist 2 νN ν + B / Real.sqrt N + Real.sqrt (B / N)) := by
    calc smoothDist 2 Eη ΛY ≤ smoothDist 2 Eη Λb + smoothDist 2 Λb ΛY := htri
      _ ≤ (Cr * (CΨ * (B / Real.sqrt N)) + Cr ^ 2 / 2 * (Ct * Real.sqrt (B / N))) +
          (1 + Cr ^ 2) * smoothDist 2 νN ν := add_le_add hd1 h2
      _ ≤ (1 + Cr ^ 2 + Cr * CΨ + Cr ^ 2 / 2 * Ct) * (B / Real.sqrt N) +
          (1 + Cr ^ 2 + Cr * CΨ + Cr ^ 2 / 2 * Ct) * Real.sqrt (B / N) +
          (1 + Cr ^ 2 + Cr * CΨ + Cr ^ 2 / 2 * Ct) * smoothDist 2 νN ν := by
          have := add_le_add (add_le_add k2 k3) k1
          linarith
      _ = _ := by ring
  exact hfinal

end HRS.T25P
