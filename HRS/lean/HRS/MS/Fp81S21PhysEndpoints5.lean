import HRS.MS.Fp81S21PhysEndpoints4
import HRS.MS.Fp81S21InitialWindow2

/-! Positive-coupling initial endpoint for the full-horizon prediction. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.CovMeas

private theorem fp81s21_physical_initial_mean_moment
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ) {N : ℕ}
    (hN : 2 ≤ N) (E : InitialSteinEnv R) :
    Integrable (fun x : Euc p.d => jbracket x ^ (wholeSpaceIndex p.d : ℝ))
      (HRS.Whole.meanEmpirical (r26t3_Q R N)) := by
  let μ : Measure (Euc p.d) := r26t3_mu R 0
  let P : Measure (EucConfig p.d N) := r26t3_Q R N
  let f : Euc p.d → ℝ := fun x => jbracket x ^ (wholeSpaceIndex p.d : ℝ)
  let S := E.static N hN
  haveI hμ : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu E.reference.prob
  have hρupper : ∀ x : Euc p.d,
      R.ρ 0 x ≤ E.C * Real.exp (-E.c * ‖x‖ ^ 2) := by
    intro x
    exact (le_abs_self _).trans (E.reference.h0 x)
  have hgauss : HasR2GaussianUpper E.C E.c (R.ρ 0) :=
    ⟨E.reference.hc, hρupper⟩
  obtain ⟨CM, hCM⟩ := HRS.MS.R2Chaos.s94_moment_rpow
    E.reference.prob hgauss (a := (wholeSpaceIndex p.d : ℝ)) (by positivity)
  have hfmeas : Measurable f := by
    dsimp [f]
    exact (((by
      unfold jbracket
      fun_prop : Continuous fun x : Euc p.d => jbracket x).rpow_const
        (fun x => Or.inl (zero_lt_one.trans_le (HRS.MS.R2Poly.s95_one_le_jb x)).ne')).measurable)
  have hfnonneg : ∀ x, 0 ≤ f x := by
    intro x
    exact Real.rpow_nonneg (by
      have := HRS.MS.R2Poly.s95_one_le_jb x
      positivity) _
  have hfμ : Integrable f μ := by
    refine ⟨hfmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hfnonneg)]
    exact lt_of_le_of_lt hCM ENNReal.ofReal_lt_top
  obtain ⟨φ, hφm, hνeq, hφb, -, -⟩ := S.marg
  have hφnonneg : ∀ x, 0 ≤ φ x := fun x => (hφb x).1
  have hφμ : Integrable (fun x => φ x * f x) μ := by
    refine Integrable.mono' (hfμ.mul_const E.Cs)
      ((hφm.mul hfmeas).aestronglyMeasurable) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hφnonneg x) (hfnonneg x))]
    calc φ x * f x = f x * φ x := by ring
      _ ≤ f x * E.Cs := mul_le_mul_of_nonneg_left (hφb x).2 (hfnonneg x)
  have hνint : Integrable f
      (μ.withDensity (fun x => ENNReal.ofReal (φ x))) := by
    rw [integrable_withDensity_iff_integrable_smul' hφm.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    convert hφμ using 1
    funext x
    simp [smul_eq_mul, ENNReal.toReal_ofReal (hφnonneg x)]
  letI : IsProbabilityMeasure P := by
    change IsProbabilityMeasure (r26t3_Q R N)
    rw [← E.law_eq N]
    exact S.prob
  have hmean : HRS.Whole.meanEmpirical P =
      μ.withDensity (fun x => ENNReal.ofReal (φ x)) := by
    have hExch : HRS.Whole.IsExchangeable P := by
      change HRS.Whole.IsExchangeable (r26t3_Q R N)
      rw [← E.law_eq N]
      exact S.exch
    have hfirst : HRS.Whole.meanEmpirical P = HRS.Whole.firstMarginal P :=
      HRS.Whole.meanEmpirical_eq_firstMarginal P hExch (by omega)
    have hνP : S47.s47_nu p.d p.s (R.ρ 0) p.γ N = HRS.Whole.firstMarginal P := by
      change S47.s47_nu p.d p.s (R.ρ 0) p.γ N =
        HRS.Whole.firstMarginal (r26t3_Q R N)
      rw [← E.law_eq N]
    calc HRS.Whole.meanEmpirical P = HRS.Whole.firstMarginal P := hfirst
      _ = S47.s47_nu p.d p.s (R.ρ 0) p.γ N := hνP.symm
      _ = μ.withDensity (fun x => ENNReal.ofReal (φ x)) := hνeq
  rw [show HRS.Whole.meanEmpirical (r26t3_Q R N) = HRS.Whole.meanEmpirical P by rfl, hmean]
  exact hνint

private theorem fp81s21_physical_initial_S102Lin
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ) {H : ℝ} :
    S102Lin (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H := by
  intro u t hu hut ht φ ψ c hφ hψ
  have h := fp81s21_U_linear_of_hermite_combo p R hφ hψ c
    (t := t) (r := u) (le_trans hu hut) ⟨hu, hut⟩
  have hfun : φ + c • ψ = (fun x => φ x + c * ψ x) := by
    funext x
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  funext x
  change propagatorW (r26t3_coeff R) u t (φ + c • ψ) x = _
  rw [hfun]
  exact congrFun h x

private theorem fp81s21_physical_predicted_zero_eq_initProp
    {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}
    {Pw : ℝ} (hP : (d : ℝ) < 2 * Pw) (hD : S101Data C m T r c)
    (hlin : S102Lin C m T) (hT : 0 ≤ T)
    (w : OscPath d m T) (z : ℝ → (Euc d → ℝ) → ℝ)
    (hz : S102Z r Pw (z 0))
    (hmatch : r2Vprop C m 0 0 (z 0) = r2PathAt w 0) :
    r2Predicted C w z 0 = r2InitProp C m T (z 0) := by
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  apply ContinuousMap.ext
  intro t
  have hp := s102_predicted_at hP hD hlin w z hzero hz hmatch t.property
  have hi := s102_initProp_at hP hD hlin hz hT t.property
  have hp' : OscPath.at' (r2Predicted C w z 0) t =
      if (t : ℝ) ≤ 0 then r2PathAt w (t : ℝ) else r2Vprop C m (t : ℝ) 0 (z 0) := by
    rw [← s102_r2PathAt_of_mem _ t.property]
    exact hp
  have hi' : OscPath.at' (r2InitProp C m T (z 0)) t =
      r2Vprop C m (t : ℝ) 0 (z 0) := by
    rw [← s102_r2PathAt_of_mem _ t.property]
    exact hi
  change OscPath.at' (r2Predicted C w z 0) t =
    OscPath.at' (r2InitProp C m T (z 0)) t
  rw [hp', hi']
  by_cases ht0 : (t : ℝ) ≤ 0
  · have htval : t = ⟨0, hzero⟩ := Subtype.ext (le_antisymm ht0 t.property.1)
    rw [htval]
    simpa using hmatch.symm
  · simp [ht0]

/-- The full-horizon prediction at time zero, restricted to the physical
window, is the actual initial fluctuation window almost surely. -/
theorem fp81s21_physical_initial_prediction_path (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      0 < p.γ → ∀ a : ℝ, (ha : 0 ≤ a) → ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N,
        ∀ᵐ ω ∂A.P,
          HRS.MS.ProClosureS111.physicalWindowRestriction
              (d := p.d) (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T)
              (H := a + p.T) ha le_rfl
              (s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) (a + p.T)
                A.P A.X ω 0) = initialWindow R N a (A.X₀ ω) := by
  obtain ⟨δr, hδr, hδrhalf, hrestrict⟩ :=
    fp81s21_initialWindow_restriction_Q_ae p
  obtain ⟨δg, hδg, hδghalf, hgenuine⟩ :=
    fp81s21_initialWindow_genuine p
  obtain ⟨δu, hδu, hδuhalf, horbit⟩ := fp81s21_uniform_orbit_amplitudes p
  let δ0 := min δr (min δg δu)
  have hδ0 : 0 < δ0 := by
    dsimp [δ0]
    exact lt_min hδr (lt_min hδg hδu)
  have hδ0half : δ0 ≤ 1 / 2 := by
    dsimp [δ0]
    exact (min_le_left _ _).trans hδrhalf
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R hγ a ha N hN A
  have hδr' : δ ≤ δr := hδle.trans (by dsimp [δ0]; exact min_le_left _ _)
  have hδg' : δ ≤ δg := hδle.trans (by
    dsimp [δ0]
    exact (min_le_right _ _).trans (min_le_left _ _))
  have hδu' : δ ≤ δu := hδle.trans (by
    dsimp [δ0]
    exact (min_le_right _ _).trans (min_le_right _ _))
  have hδhalf : δ ≤ 1 / 2 := hδle.trans hδ0half
  let m : ℝ := (wholeSpaceIndex p.d : ℝ)
  let H : ℝ := a + p.T
  have hH : 0 < H := by dsimp [H]; linarith [p.hT, ha]
  obtain ⟨Co, co, hco, hcosum, horbits⟩ := horbit δ hδ hδu' R
  have hD : S101Data (r26t3_coeff R) m H (2 * p.d + 8)
      (fp81s21_uniform_orbit_coefficient p Co) := by
    simpa [m, H] using horbits H hH
  have hlin : S102Lin (r26t3_coeff R) m H := by
    simpa [m, H] using (fp81s21_physical_initial_S102Lin R (H := H))
  obtain ⟨E⟩ := initialSteinEnv_exists hδ hδhalf R hγ
  have hMoment := fp81s21_physical_initial_mean_moment R hN E
  have hP : (p.d : ℝ) < 2 * m := by
    dsimp [m, HRS.Whole.wholeSpaceIndex]
    push_cast
    nlinarith [p.hd]
  have hP0 : 0 ≤ m := by dsimp [m]; positivity
  have hNpos : 0 < N := by omega
  have hd1 : 1 ≤ p.d := le_trans (by norm_num) p.hd
  have hr : (p.d : ℝ) / 2 < (2 * p.d + 8 : ℕ) := by
    push_cast
    nlinarith [show (0 : ℝ) ≤ p.d by exact Nat.cast_nonneg _]
  have hZinit : ∀ X : EucConfig p.d N,
      S102Z (2 * p.d + 8) m (initialFunctional R N X) := by
    intro X
    unfold initialFunctional
    exact s102_Z_fluct hd1 hP0 (2 * p.d + 8) hr hNpos X
      (HRS.Whole.meanEmpirical (r26t3_Q R N)) hMoment (Real.sqrt N)
  have hXm : ∀ t, Measurable (A.X t) := (A.strong H).adapted
  have hcont := (A.strong H).cont
  have hm : (p.d : ℝ) < m := by
    change (p.d : ℝ) < (wholeSpaceIndex p.d : ℝ)
    unfold wholeSpaceIndex
    push_cast
    nlinarith [p.hd]
  have hcz := s102_zeta_cont hm hNpos A.P A.X hXm hcont
  have hfun := fp81s21_physical_initial_functional p R A
  have hX0 : AEMeasurable A.X₀ A.P :=
    ((A.strong 0).adapted 0).aemeasurable.congr (A.strong 0).init
  have hlaw0 : A.P.map (A.X 0) = r26t3_Q R N := by
    calc A.P.map (A.X 0) = A.P.map A.X₀ := Measure.map_congr (A.strong 0).init
      _ = r26t3_Q R N := A.initial
  have hMoment0 : Integrable
      (fun x : Euc p.d => jbracket x ^ m)
      (HRS.Whole.meanEmpirical (A.P.map (A.X 0))) := by
    rw [hlaw0]
    simpa [m] using hMoment
  have hrestrictR := hrestrict δ hδ hδr' R hγ N hN a ha
  have hLawInit : A.P.map A.X₀ = r26t3_Q R N := A.initial
  have hrestMap : ∀ᵐ X ∂(A.P.map A.X₀),
      HRS.MS.ProClosureS111.physicalWindowRestriction
          (d := p.d) (m := m) (T := p.T) (H := H) ha le_rfl
          (r2InitPath (r26t3_coeff R) m H (r26t3_Q R N) X) =
        initialWindow R N a X := by
    rw [hLawInit]
    exact hrestrictR
  filter_upwards [hfun, hcz, ae_of_ae_map hX0 hrestMap] with ω hfl hczω hrest
  have hz : S102Z (2 * p.d + 8) m
      (s102_zf A.P A.X ω 0) := by
    rw [hfl]
    exact hZinit (A.X₀ ω)
  have hw : ContinuousOn
      (fun t : ℝ => zetaB m (A.P.map (A.X t.toNNReal)) (A.X t.toNNReal ω))
      (Icc (0 : ℝ) H) := hczω.continuousOn
  let w : OscPath p.d m H := zetaPathW m H 0 A.P A.X ω
  have hwat : r2PathAt w 0 =
      zetaB m (A.P.map (A.X (0 : ℝ≥0))) (A.X 0 ω) := by
    change r2PathAt
      (windowPathOf m H 0 (fun t =>
        zetaB m (A.P.map (A.X t.toNNReal)) (A.X t.toNNReal ω))) 0 = _
    simpa using s102_windowPathOf_at hw (⟨le_rfl, hH.le⟩ : (0 : ℝ) ∈ Icc 0 H)
  have hterm : ∀ α : MultiIndex p.d,
      propagatorW (r26t3_coeff R) 0 0 (oscTestFun m α) = oscTestFun m α := by
    intro α
    have htest : IsOscTest m (oscTestFun m α) := by
      simpa [m] using HRS.MS.GenPath.s56_isOscTest m α
    have hclass := fp81s21_U_osc_test_classical p R htest le_rfl
    exact (s102_propagator_classical ⟨_, hclass⟩).terminal
  have hmatch : r2Vprop (r26t3_coeff R) m 0 0
      (s102_zf A.P A.X ω 0) = r2PathAt w 0 := by
    apply s102_ext
    intro α
    calc OscDual.coord (r2Vprop (r26t3_coeff R) m 0 0
          (s102_zf A.P A.X ω 0)) α
        = s102_zf A.P A.X ω 0
            (propagatorW (r26t3_coeff R) 0 0 (oscTestFun m α)) :=
              s102_Vprop_coord hP hD hz hlin ⟨le_rfl, hH.le⟩ ⟨le_rfl, hH.le⟩ α
      _ = s102_zf A.P A.X ω 0 (oscTestFun m α) := by rw [hterm α]
      _ = OscDual.coord (zetaB m (A.P.map (A.X (0 : ℝ≥0))) (A.X 0 ω)) α :=
            by simpa using (s102_coord_zetaB hm hNpos A.P A.X hXm 0 ω α).symm
      _ = OscDual.coord (r2PathAt w 0) α := by rw [hwat]
  have hpred := fp81s21_physical_predicted_zero_eq_initProp
    hP hD hlin hH.le w (s102_zf A.P A.X ω) hz hmatch
  have hinitPath : r2InitProp (r26t3_coeff R) m H
        (initialFunctional R N (A.X₀ ω)) =
      r2InitPath (r26t3_coeff R) m H (r26t3_Q R N) (A.X₀ ω) := by
    rcases hgenuine δ hδ hδg' R hγ N hN a ha (A.X₀ ω) with
      ⟨hpath, hWindow, hcoords, hcompat, hrestrictPt⟩
    have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) H := ⟨le_rfl, hH.le⟩
    have hvcont := s102_Vprop_continuousOn hP hD (hZinit (A.X₀ ω)) hlin hzero
    have hfuncont : ContinuousOn
        (fun s => r2InitFun (r26t3_coeff R) m (r26t3_Q R N) (A.X₀ ω) s)
        (Icc (0 : ℝ) H) :=
      hvcont.congr fun s hs => hcompat s hs
    apply ContinuousMap.ext
    intro t
    change OscPath.at' (r2InitProp (r26t3_coeff R) m H
        (initialFunctional R N (A.X₀ ω))) t =
      OscPath.at' (r2InitPath (r26t3_coeff R) m H
        (r26t3_Q R N) (A.X₀ ω)) t
    calc OscPath.at' (r2InitProp (r26t3_coeff R) m H
          (initialFunctional R N (A.X₀ ω))) t
        = r2PathAt (r2InitProp (r26t3_coeff R) m H
            (initialFunctional R N (A.X₀ ω))) t :=
              (s102_r2PathAt_of_mem _ t.property).symm
      _ = r2Vprop (r26t3_coeff R) m (t : ℝ) 0
            (initialFunctional R N (A.X₀ ω)) :=
              s102_initProp_at hP hD hlin (hZinit (A.X₀ ω)) hH.le t.property
      _ = r2InitFun (r26t3_coeff R) m (r26t3_Q R N) (A.X₀ ω) (t : ℝ) :=
              (hcompat t t.property).symm
      _ = r2PathAt (r2InitPath (r26t3_coeff R) m H
            (r26t3_Q R N) (A.X₀ ω)) t :=
              (s102_windowPathOf_at hfuncont t.property).symm
      _ = OscPath.at' (r2InitPath (r26t3_coeff R) m H
            (r26t3_Q R N) (A.X₀ ω)) t :=
              s102_r2PathAt_of_mem _ t.property
  have hYpath : s102_Y (r26t3_coeff R) m H A.P A.X ω 0 =
      r2InitPath (r26t3_coeff R) m H (r26t3_Q R N) (A.X₀ ω) := by
    change r2Predicted (r26t3_coeff R) w (s102_zf A.P A.X ω) 0 = _
    rw [hpred, hfl, hinitPath]
  rw [← hYpath] at hrest
  exact hrest

/-- The initial endpoint expectation equals the exact static preparation-law
heat integral, for positive preparation strength. -/
theorem fp81s21_physical_initial_prediction_endpoint (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      0 < p.γ →
      ∀ future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H),
      (∀ H v, IsProbabilityMeasure (future H v)) →
      ∀ a : ℝ, ∀ ha : 0 ≤ a, ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N,
      ∀ Φ : Window p → ℝ, MemCb 5 Φ →
        (∫ ω, initialHeat future a ha Φ 0
          (HRS.MS.ProClosureS111.physicalWindowRestriction
            (d := p.d) (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T)
            (H := a + p.T) ha le_rfl
            (s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) (a + p.T)
              A.P A.X ω 0)) ∂A.P) =
          ∫ X, initialHeat future a ha Φ 0 (initialWindow R N a X)
            ∂(r26t3_Q R N) := by
  obtain ⟨δpath, hδpath, hδpathhalf, hpath⟩ :=
    fp81s21_physical_initial_prediction_path p
  obtain ⟨δheat, hδheat, hδheathalf, hheat⟩ :=
    fp81s21_physical_initial_heat_integral p
  let δ0 := min δpath δheat
  have hδ0 : 0 < δ0 := by
    dsimp [δ0]
    exact lt_min hδpath hδheat
  have hδ0half : δ0 ≤ 1 / 2 := by
    dsimp [δ0]
    exact (min_le_left _ _).trans hδpathhalf
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R hγ future hfuture a ha N hN A Φ hΦ
  have hδpath' : δ ≤ δpath := hδle.trans (by dsimp [δ0]; exact min_le_left _ _)
  have hδheat' : δ ≤ δheat := hδle.trans (by dsimp [δ0]; exact min_le_right _ _)
  have hpathAE := hpath δ hδ hδpath' R hγ a ha N hN A
  calc (∫ ω, initialHeat future a ha Φ 0
        (HRS.MS.ProClosureS111.physicalWindowRestriction
          (d := p.d) (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T)
          (H := a + p.T) ha le_rfl
          (s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) (a + p.T)
            A.P A.X ω 0)) ∂A.P)
      = ∫ ω, initialHeat future a ha Φ 0
          (initialWindow R N a (A.X₀ ω)) ∂A.P := by
            apply integral_congr_ae
            filter_upwards [hpathAE] with ω hω
            rw [hω]
    _ = ∫ X, initialHeat future a ha Φ 0 (initialWindow R N a X)
          ∂(r26t3_Q R N) :=
            hheat δ hδ hδheat' R future hfuture a ha N hN A Φ hΦ

#print axioms HRS.Fp81.S21.fp81s21_physical_initial_prediction_path
#print axioms HRS.Fp81.S21.fp81s21_physical_initial_prediction_endpoint
end HRS.Fp81.S21
end
