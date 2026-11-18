import HRS.MS.Fp81S21PhysEndpoints6

/-! The zero-coupling initial prediction endpoint and its two-branch export. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.CovMeas

private theorem fp81s21_physical_zero_prediction_mean_moment
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (R : Trajectory p δ) (hγ : p.γ = 0) {N : ℕ} (hN : 2 ≤ N) :
    Integrable (fun x : Euc p.d => jbracket x ^ (wholeSpaceIndex p.d : ℝ))
      (HRS.Whole.meanEmpirical (r26t3_Q R N)) := by
  let μ : Measure (Euc p.d) := r26t3_mu R 0
  let f : Euc p.d → ℝ := fun x => jbracket x ^ (wholeSpaceIndex p.d : ℝ)
  obtain ⟨M, c, S, hc, hTc⟩ :=
    (r26t3_reference_data p δ hδ hδhalf R).2.2.2 (wholeSpaceIndex p.d)
  have hgauss : HRS.Whole.HasR2GaussianUpper M c (R.ρ 0) :=
    ⟨hc, hTc.gauss⟩
  obtain ⟨CM, hCM⟩ := HRS.MS.R2Chaos.s94_moment_rpow hTc.prob hgauss
    (a := (wholeSpaceIndex p.d : ℝ)) (by positivity)
  haveI hμ : IsProbabilityMeasure μ :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hTc.prob
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
  have hmean : HRS.Whole.meanEmpirical (r26t3_Q R N) = μ := by
    rw [fp81s21_initial_iid_Q hδ hδhalf R hγ N]
    exact HRS.Whole.s11iid_meanEmpirical_pi N (by omega) μ
  rw [hmean]
  exact hfμ

private theorem fp81s21_physical_zero_prediction_S102Lin
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ) {H : ℝ} :
    S102Lin (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H := by
  intro u t hu hut ht φ ψ c hφ hψ
  have h := fp81s21_U_linear_of_hermite_combo p R hφ hψ c
    (t := t) (r := u) (le_trans hu hut) ⟨hu, hut⟩
  have hfun : φ + c • ψ = (fun x => φ x + c * ψ x) := by
    funext x
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  funext x
  rw [hfun]
  exact congrFun h x

private theorem fp81s21_physical_zero_prediction_initFun_eq_Vprop
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ) {N : ℕ}
    (_hN : 2 ≤ N) (H : ℝ) {r : ℕ} {c : MultiIndex p.d → ℝ}
    (hD : S101Data (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H r c)
    (hlin : S102Lin (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H)
    (hZ : ∀ X : EucConfig p.d N,
      S102Z r (wholeSpaceIndex p.d : ℝ) (initialFunctional R N X))
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) H) (X : EucConfig p.d N) :
    r2InitFun (r26t3_coeff R) (wholeSpaceIndex p.d)
        (r26t3_Q R N) X s =
      r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d) s 0
        (initialFunctional R N X) := by
  have hP : (p.d : ℝ) < 2 * (wholeSpaceIndex p.d : ℝ) := by
    dsimp [HRS.Whole.wholeSpaceIndex]
    push_cast
    nlinarith [p.hd]
  have hH : 0 ≤ H := hs.1.trans hs.2
  have hu : (0 : ℝ) ∈ Icc (0 : ℝ) H := ⟨le_rfl, hH⟩
  apply HRS.MS.CovMeas.s101_ellVec_ext
  intro α
  have hmem := s102_z_orbit_memℓp hP hD (hZ X) (u := 0) hu hs
  change OscDual.coord
      (ellVec (wholeSpaceIndex p.d)
        (fun β => Real.sqrt N *
          (HRS.Whole.pair (HRS.Whole.empirical X)
              (propagatorW (r26t3_coeff R) 0 s
                (oscTestFun (wholeSpaceIndex p.d) β)) -
            HRS.Whole.pair (HRS.Whole.meanEmpirical (r26t3_Q R N))
              (propagatorW (r26t3_coeff R) 0 s
                (oscTestFun (wholeSpaceIndex p.d) β))))) α =
    OscDual.coord
      (r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d) s 0
        (initialFunctional R N X)) α
  rw [HRS.MS.CovMeas.s101_ellVec_coord (by
    simpa [initialFunctional] using hmem)]
  rw [s102_Vprop_coord hP hD (hZ X) hlin (u := 0) hu hs α]
  rfl

private theorem fp81s21_physical_zero_prediction_windowPathOf_eq
    {d : ℕ} {m T : ℝ} (f : ℝ → OscDual d m)
    (g : C(Icc (0 : ℝ) T, OscDual d m))
    (hg : ∀ t : Icc (0 : ℝ) T, f (0 + (t : ℝ)) = g t) :
    windowPathOf m T 0 f = (show OscPath d m T from g) := by
  have h : Continuous (fun t : Icc (0 : ℝ) T => f (0 + (t : ℝ))) :=
    g.continuous.congr fun t => (hg t).symm
  unfold windowPathOf
  simp only [h, ↓reduceDIte]
  apply ContinuousMap.ext
  intro t
  exact hg t

private theorem fp81s21_physical_zero_prediction_predicted_eq_initProp
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

/-- The full-horizon prediction at time zero restricts to the zero-strength
initial fluctuation window almost surely. The zero-strength restriction law
is proved separately from the positive-strength law. -/
theorem fp81s21_physical_initial_prediction_path_zero (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      p.γ = 0 → ∀ a : ℝ, (ha : 0 ≤ a) → ∀ N : ℕ, 2 ≤ N →
        ∀ A : Particle R N,
          ∀ᵐ ω ∂A.P,
            HRS.MS.ProClosureS111.physicalWindowRestriction
                (d := p.d) (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T)
                (H := a + p.T) ha le_rfl
                (s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
                  (a + p.T) A.P A.X ω 0) = initialWindow R N a (A.X₀ ω) := by
  obtain ⟨δr, hδr, hδrhalf, hrestrict⟩ :=
    fp81s21_physical_initialWindow_restriction_Q_zero p
  obtain ⟨δu, hδu, hδuhalf, horbit⟩ := fp81s21_uniform_orbit_amplitudes p
  let δ0 := min δr δu
  have hδ0 : 0 < δ0 := by
    dsimp [δ0]
    exact lt_min hδr hδu
  have hδ0half : δ0 ≤ 1 / 2 := by
    dsimp [δ0]
    exact (min_le_left _ _).trans hδrhalf
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R hγ a ha N hN A
  have hδr' : δ ≤ δr := hδle.trans (by dsimp [δ0]; exact min_le_left _ _)
  have hδu' : δ ≤ δu := hδle.trans (by dsimp [δ0]; exact min_le_right _ _)
  have hδhalf : δ ≤ 1 / 2 := hδle.trans hδ0half
  let m : ℝ := (wholeSpaceIndex p.d : ℝ)
  let H : ℝ := a + p.T
  have hH : 0 < H := by dsimp [H]; linarith [p.hT, ha]
  obtain ⟨Co, co, hco, hcosum, horbits⟩ := horbit δ hδ hδu' R
  have hD : S101Data (r26t3_coeff R) m H (2 * p.d + 8)
      (fp81s21_uniform_orbit_coefficient p Co) := by
    simpa [m, H] using horbits H hH
  have hlin : S102Lin (r26t3_coeff R) m H := by
    simpa [m, H] using (fp81s21_physical_zero_prediction_S102Lin R (H := H))
  have hMoment := fp81s21_physical_zero_prediction_mean_moment
    hδ hδhalf R hγ hN
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
  have hz : S102Z (2 * p.d + 8) m (s102_zf A.P A.X ω 0) := by
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
  have hpred := fp81s21_physical_zero_prediction_predicted_eq_initProp
    hP hD hlin hH.le w (s102_zf A.P A.X ω) hz hmatch
  have hcompat : ∀ s : ℝ, s ∈ Icc (0 : ℝ) H →
      r2InitFun (r26t3_coeff R) m (r26t3_Q R N) (A.X₀ ω) s =
        r2Vprop (r26t3_coeff R) m s 0
          (initialFunctional R N (A.X₀ ω)) := by
    intro s hs
    exact fp81s21_physical_zero_prediction_initFun_eq_Vprop R hN H
      (c := fp81s21_uniform_orbit_coefficient p Co) hD hlin hZinit hs (A.X₀ ω)
  have hEq :
      (fun s : Icc (0 : ℝ) H =>
        r2InitFun (r26t3_coeff R) m (r26t3_Q R N) (A.X₀ ω) (s : ℝ)) =
      (fun s : Icc (0 : ℝ) H =>
        r2Vprop (r26t3_coeff R) m (s : ℝ) 0
          (initialFunctional R N (A.X₀ ω))) := by
    funext s
    exact hcompat s s.property
  have hVcont := s102_Vprop_continuousOn hP hD (hZinit (A.X₀ ω)) hlin
    (u := 0) ⟨le_rfl, hH.le⟩
  have hlongcont : Continuous (fun s : Icc (0 : ℝ) H =>
      r2InitFun (r26t3_coeff R) m (r26t3_Q R N) (A.X₀ ω) (s : ℝ)) := by
    rw [hEq]
    exact continuousOn_iff_continuous_restrict.mp hVcont
  have hlongShift : Continuous (fun s : Icc (0 : ℝ) H =>
      r2InitFun (r26t3_coeff R) m (r26t3_Q R N) (A.X₀ ω) (0 + (s : ℝ))) := by
    simpa only [zero_add] using hlongcont
  have hLongPath :
      r2InitPath (r26t3_coeff R) m H (r26t3_Q R N) (A.X₀ ω) =
        (⟨fun s : Icc (0 : ℝ) H =>
          r2InitFun (r26t3_coeff R) m (r26t3_Q R N) (A.X₀ ω) (0 + (s : ℝ)),
          hlongShift⟩ : OscPath p.d m H) := by
    exact fp81s21_physical_zero_prediction_windowPathOf_eq (m := m) (T := H)
      (r2InitFun (r26t3_coeff R) m (r26t3_Q R N) (A.X₀ ω))
      (⟨fun s : Icc (0 : ℝ) H =>
        r2InitFun (r26t3_coeff R) m (r26t3_Q R N) (A.X₀ ω) (0 + (s : ℝ)),
        hlongShift⟩)
      (fun _ => rfl)
  have hinitPath : r2InitProp (r26t3_coeff R) m H
        (initialFunctional R N (A.X₀ ω)) =
      r2InitPath (r26t3_coeff R) m H (r26t3_Q R N) (A.X₀ ω) := by
    apply ContinuousMap.ext
    intro t
    calc OscPath.at' (r2InitProp (r26t3_coeff R) m H
          (initialFunctional R N (A.X₀ ω))) t
        = r2PathAt (r2InitProp (r26t3_coeff R) m H
            (initialFunctional R N (A.X₀ ω))) t :=
              (s102_r2PathAt_of_mem _ t.property).symm
      _ = r2Vprop (r26t3_coeff R) m (t : ℝ) 0
            (initialFunctional R N (A.X₀ ω)) :=
              s102_initProp_at hP hD hlin (hZinit (A.X₀ ω)) hH.le t.property
      _ = r2InitFun (r26t3_coeff R) m (r26t3_Q R N) (A.X₀ ω) (t : ℝ) :=
              (hcompat (t : ℝ) t.property).symm
      _ = r2PathAt (r2InitPath (r26t3_coeff R) m H
            (r26t3_Q R N) (A.X₀ ω)) t :=
              (s102_windowPathOf_at (continuousOn_iff_continuous_restrict.mpr hlongcont)
                t.property).symm
      _ = OscPath.at' (r2InitPath (r26t3_coeff R) m H
            (r26t3_Q R N) (A.X₀ ω)) t :=
              s102_r2PathAt_of_mem _ t.property
  have hYpath : s102_Y (r26t3_coeff R) m H A.P A.X ω 0 =
      r2InitPath (r26t3_coeff R) m H (r26t3_Q R N) (A.X₀ ω) := by
    change r2Predicted (r26t3_coeff R) w (s102_zf A.P A.X ω) 0 = _
    rw [hpred, hfl, hinitPath]
  rw [← hYpath] at hrest
  exact hrest

/-- The zero-strength initial prediction endpoint expectation is the exact
static preparation-law heat integral. -/
theorem fp81s21_physical_initial_prediction_endpoint_zero (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      p.γ = 0 →
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
    fp81s21_physical_initial_prediction_path_zero p
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

/-- The physical initial prediction endpoint for either admissible coupling
branch. The coupling branch is selected before its common small-radius bound. -/
theorem fp81s21_physical_initial_prediction_endpoint_both (p : Parameters)
    (hγ : 0 < p.γ ∨ p.γ = 0) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
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
  rcases hγ with hpos | hzero
  · obtain ⟨δ0, hδ0, hδhalf, hendpoint⟩ :=
      fp81s21_physical_initial_prediction_endpoint p
    refine ⟨δ0, hδ0, hδhalf, ?_⟩
    intro δ hδ hδle R future hfuture a ha N hN A Φ hΦ
    exact hendpoint δ hδ hδle R hpos future hfuture a ha N hN A Φ hΦ
  · obtain ⟨δ0, hδ0, hδhalf, hendpoint⟩ :=
      fp81s21_physical_initial_prediction_endpoint_zero p
    refine ⟨δ0, hδ0, hδhalf, ?_⟩
    intro δ hδ hδle R future hfuture a ha N hN A Φ hΦ
    exact hendpoint δ hδ hδle R hzero future hfuture a ha N hN A Φ hΦ

#print axioms HRS.Fp81.S21.fp81s21_physical_initial_prediction_path_zero
#print axioms HRS.Fp81.S21.fp81s21_physical_initial_prediction_endpoint_zero
#print axioms HRS.Fp81.S21.fp81s21_physical_initial_prediction_endpoint_both
end HRS.Fp81.S21
end
