import HRS.Main.T25PAux24
import HRS.Main.T25Aux6

/-!
# T25P, part 25: the enlarged comparison for the prepared data (statement `t25p_prep`)

Given an arbitrary coupling `π₀` of `(law η_N^0, ν)` and a prepared linear solution `(Y₀, Y)` with initial law `ν`: enlarge the
filtered solution so that `η' ~ ν` is `ℱ_0`-measurable with `(η_N^0, η')` of law `π₀`, and apply `t25p_core_gen` with the target
`Λ = law (Y^{a+·})`.  The conclusion keeps the `Ψ_a`- and trace-integrals on the enlarged space (bounded afterwards by
`t25p_Psi_L1`, `t25p_Psi_L2`, `t25p_trace_int`, which apply to the pulled-back particle system).
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory Complex
open scoped ENNReal NNReal BigOperators Matrix RealInnerProductSpace

namespace HRS.T25P

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.Main HRS.T25

variable {d : ℕ}

theorem t25p_prep (S : PreparedData d) {m : ℝ} (hm : (d : ℝ) + 2 < m) {T : ℝ} (hT : 0 < T)
    {Cr cr Cmax : ℝ} (hCr : 0 < Cr) (hcr : 0 < cr)
    {Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m}
    (hdual : IsDualEvolution (t25_traj S).dyn S.ρ m Vev) (hEv : T25Ev m Cr cr T Cmax Vev)
    {a : ℝ} (ha : 0 ≤ a) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hSel : SelectedFlow P S.dyn (a + T) X₀ W X)
    (hfilt : ∃ (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
      IsFilteredSolution P ℱ W' W X)
    {ν : Measure (NegSobolev d m)} {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y₀ : Ω' → NegSobolev d m) (Y : ℝ → Ω' → NegSobolev d m)
    (hY : IsPreparedLinear S m (a + T) ν P' Y₀ Y)
    (π₀ : Measure (NegSobolev d m × NegSobolev d m))
    (hπ₀ : IsCoupling π₀ (law P (fun ω => etaE m (X₀ ω) S.μ0)) ν) :
    ∃ (Ω'' : Type) (mΩ'' : MeasurableSpace Ω'') (P'' : Measure Ω'') (_ : IsProbabilityMeasure P'')
      (π : Ω'' → Ω) (_ : MeasurePreserving π P'' P),
      IsParticleSystem P'' (t25_traj S).dyn (a + T) (fun ω => X₀ (π ω)) (fun t ω => W t (π ω))
        (fun t ω => X t (π ω)) ∧
      (∃ (ℱ'' : Filtration ℝ mΩ'') (W'' : ℝ≥0 → Ω'' → (Fin N × Fin d) → ℝ),
        IsFilteredSolution P'' ℱ'' W'' (fun t ω => W t (π ω)) (fun t ω => X t (π ω))) ∧
      ENNReal.ofReal (smoothDist 2 (S.etaLaw m T a P X) (law P' (windowPath m T a Y))) ≤
        ENNReal.ofReal (Cr * Real.exp (-cr * a)) * ∫⁻ z, ‖z.1 - z.2‖ₑ ∂π₀ +
        ∫⁻ ω, ENNReal.ofReal Cr * t25p_Psi d S.s S.ρ m cr a T (fun t ω => X t (π ω)) ω ∂P'' +
        ENNReal.ofReal (Cr ^ 2 / 2) * ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) (a + T),
          ENNReal.ofReal (Real.exp (-cr * max (a - r) 0) ^ 2 * traceNormForm
            (covForm m S.β⁻¹ (empirical (X r.toNNReal (π ω))) - covDensT m S.β⁻¹ (a + T) S.ρ r))) ∂P'' ∧
      (∀ p : ℝ, (p = 1 ∨ p = 2) →
        wassersteinE p (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
          ENNReal.ofReal ((2 * (Cr ^ 2 + Real.sqrt Cmax) + Cr + 1) * Real.exp (-cr * a)) *
              (∫⁻ z, ‖z.1 - z.2‖ₑ ^ p ∂π₀) ^ (1 / p) +
            (∫⁻ ω, (ENNReal.ofReal Cr * t25p_Psi d S.s S.ρ m cr a T (fun t ω => X t (π ω)) ω) ^ p ∂P'') ^ (1 / p) +
            ENNReal.ofReal (2 * (Cr ^ 2 + Real.sqrt Cmax) + Cr + 1) *
              (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) (a + T),
                ENNReal.ofReal (Real.exp (-cr * max (a - r) 0) ^ 2 * traceNormForm
                  (covForm m S.β⁻¹ (empirical (X r.toNNReal (π ω))) -
                    covDensT m S.β⁻¹ (a + T) S.ρ r))) ∂P'') ^ (1 / 2 : ℝ)) := by
  classical
  have hd : 2 ≤ d := S.hd
  have htr := t25_traj S
  have hm0 : (d : ℝ) / 2 < m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨ℱ, W', hF⟩ := hfilt
  have hX : IsParticleSystem P (t25_traj S).dyn (a + T) X₀ W X := t25_isParticleSystem S hSel
  have hX0 : ∀ᵐ ω ∂P, X 0 ω = X₀ ω := hX.sol.init
  have hgm := t25p_etaE_measurable S m hm0 N
  obtain ⟨Ω'', mΩ'', P'', hP'', π, hπ, ℱ'', η', hsol, hη'0, hηlaw, hpair⟩ :=
    t25p_enlarge_coupled m N P X₀ W X ℱ W' hF hX0 (fun x => etaE m x S.μ0) hgm ν π₀ hπ₀
  have hX'' := t25p_isParticleSystem_comp hπ hX
  refine ⟨Ω'', mΩ'', P'', hP'', π, hπ, hX'', ⟨ℱ'', _, hsol⟩, ?_⟩
  have hm1 : (d : ℝ) / 2 + 2 < m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  -- the window law of the particle fluctuation process
  have hcont := t25p_fluc_cont hd htr hm hT hCr hcr hdual hEv hN ha P X₀ W X hX ℱ W' hF
  have hflm : ∀ t, Measurable (fun ω => flucProc m (Real.sqrt N) X S.ρ t ω) := fun t =>
    ((gf_measurable_ofMeasureDiff_proof m hm0 (withDensityReal (S.ρ t))).const_smul (Real.sqrt N)).comp
      (hX.sol.adapted _)
  have hFwae : AEMeasurable (Uniform.windowPath a T (flucProc m (Real.sqrt N) X S.ρ)) P :=
    HRS.Uniform.Comp28.aem_wp_a P ha hT.le _ (fun t _ => hflm t) hcont
  have hlawFw := t25p_law_pullback hπ hFwae
  have hL : law P'' (Uniform.windowPath a T (flucProc m (Real.sqrt N) (fun t ω => X t (π ω)) S.ρ)) =
      (S.etaLaw m T a P X : Measure (PathSp T (NegSobolev d m))) := by
    have e1 : S.etaLaw m T a P X = P.map (Uniform.windowPath a T (flucProc m (Real.sqrt N) X S.ρ)) := by
      unfold PreparedData.etaLaw
      refine congrArg (fun f => P.map f) ?_
      funext ω
      exact t25_windowFluc_eq m T a (Real.sqrt N) ha X S.ρ ω
    rw [e1]
    exact hlawFw
  -- the target
  have hν₀ : P'.map Y₀ = P''.map η' := hY.law_init.trans hηlaw.symm
  have hid := t25p_hid hd htr hm1 hT ha hCr hcr hdual hEv P' Y₀ hY.meas Y (t25_linear_of_prepared S hY)
    (P''.map η') hν₀ (law P' (windowPath m T a Y)) rfl
  have core := t25p_core_gen hd htr hm hT hCr hcr hdual hEv hN ha P'' (fun ω => X₀ (π ω))
    (fun t ω => W t (π ω)) (fun t ω => X t (π ω)) hX'' ℱ'' _ hsol η' hη'0
    (law P' (windowPath m T a Y)) hid
  -- the cost
  have hX₀ae : AEMeasurable X₀ P := (hX.sol.adapted 0).aemeasurable.congr hX.sol.init
  have hX₀π : AEMeasurable (fun ω => X₀ (π ω)) P'' :=
    hX₀ae.comp_quasiMeasurePreserving hπ.quasiMeasurePreserving
  have hηm : Measurable η' := hη'0.mono (ℱ''.le 0) le_rfl
  have hpairae : AEMeasurable (fun ω => (etaE m (X₀ (π ω)) S.μ0, η' ω)) P'' :=
    (hgm.comp_aemeasurable hX₀π).prodMk hηm.aemeasurable
  have hflu0 : ∀ᵐ ω ∂P'', flucProc m (Real.sqrt N) (fun t ω => X t (π ω)) S.ρ 0 ω =
      etaE m (X₀ (π ω)) S.μ0 := by
    filter_upwards [hπ.quasiMeasurePreserving.ae hX0] with ω hω
    simp only [flucProc, Real.toNNReal_zero, hω, etaE, flucE, PreparedData.μ0, S.hρ_init]
  have hcost : ∀ Φ : NegSobolev d m × NegSobolev d m → ℝ≥0∞, Measurable Φ →
      ∫⁻ ω, Φ (flucProc m (Real.sqrt N) (fun t ω => X t (π ω)) S.ρ 0 ω, η' ω) ∂P'' =
        ∫⁻ z, Φ z ∂π₀ := by
    intro Φ hΦ
    rw [← hpair, lintegral_map' hΦ.aemeasurable hpairae]
    refine lintegral_congr_ae ?_
    filter_upwards [hflu0] with ω hω
    rw [hω]
  have hc1 : ∫⁻ ω, ‖flucProc m (Real.sqrt N) (fun t ω => X t (π ω)) S.ρ 0 ω - η' ω‖ₑ ∂P'' =
      ∫⁻ z, ‖z.1 - z.2‖ₑ ∂π₀ :=
    hcost (fun z => ‖z.1 - z.2‖ₑ) (measurable_fst.sub measurable_snd).enorm
  have hcp : ∀ p : ℝ, ∫⁻ ω, ‖flucProc m (Real.sqrt N) (fun t ω => X t (π ω)) S.ρ 0 ω - η' ω‖ₑ ^ p ∂P'' =
      ∫⁻ z, ‖z.1 - z.2‖ₑ ^ p ∂π₀ := fun p =>
    hcost (fun z => ‖z.1 - z.2‖ₑ ^ p) ((measurable_fst.sub measurable_snd).enorm.pow_const p)
  rw [hL] at core
  obtain ⟨c1, c2⟩ := core
  refine ⟨?_, fun p hp => ?_⟩
  · rw [hc1] at c1
    exact c1
  · have := c2 p hp
    rw [hcp p] at this
    exact this

end HRS.T25P
