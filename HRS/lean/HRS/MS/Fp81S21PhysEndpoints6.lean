import HRS.MS.Fp81S21PhysEndpoints5
import HRS.MS.Fp81S21InitialIid

/-! The zero-coupling initial restriction law, proved from the iid preparation. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.CovMeas

private theorem fp81s21_physical_zero_initial_mean_moment
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

private theorem fp81s21_physical_initial_S102Lin_zero
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

private theorem fp81s21_physical_zero_initial_r2InitFun_eq_Vprop
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

private theorem fp81s21_physical_zero_initial_windowPath_eq
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

/-- The initial path restriction identity at zero preparation strength. It is
proved from the iid law and its Gaussian initial marginal, separately from the
positive-strength export. -/
theorem fp81s21_physical_initialWindow_restriction_Q_zero (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      p.γ = 0 → ∀ N : ℕ, 2 ≤ N → ∀ a : ℝ, (ha : 0 ≤ a) →
        ∀ᵐ X ∂(r26t3_Q R N),
          HRS.MS.ProClosureS111.physicalWindowRestriction
              (d := p.d) (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T)
              (H := a + p.T) ha le_rfl
              (r2InitPath (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
                (a + p.T) (r26t3_Q R N) X) = initialWindow R N a X := by
  classical
  obtain ⟨δu, hδu, hδuhalf, horbit⟩ := fp81s21_uniform_orbit_amplitudes p
  refine ⟨δu, hδu, hδuhalf, ?_⟩
  intro δ hδ hδle R hγ N hN a ha
  let H : ℝ := a + p.T
  let m : ℝ := (wholeSpaceIndex p.d : ℝ)
  have hH : 0 < H := by dsimp [H]; linarith [p.hT, ha]
  obtain ⟨Co, co, hco, hcosum, horbits⟩ := horbit δ hδ hδle R
  have hD : S101Data (r26t3_coeff R) m H (2 * p.d + 8)
      (fp81s21_uniform_orbit_coefficient p Co) := by
    simpa [m, H] using horbits H hH
  have hlin : S102Lin (r26t3_coeff R) m H := by
    simpa [m, H] using (fp81s21_physical_initial_S102Lin_zero R (H := H))
  have hδhalf : δ ≤ 1 / 2 := hδle.trans hδuhalf
  have hMoment := fp81s21_physical_zero_initial_mean_moment hδ hδhalf R hγ hN
  have hd1 : 1 ≤ p.d := le_trans (by norm_num) p.hd
  have hP0 : 0 ≤ m := by dsimp [m]; positivity
  have hP : (p.d : ℝ) < 2 * m := by
    dsimp [m, HRS.Whole.wholeSpaceIndex]
    push_cast
    nlinarith [p.hd]
  have hNpos : 0 < N := by omega
  have hr : (p.d : ℝ) / 2 < (2 * p.d + 8 : ℕ) := by
    push_cast
    nlinarith [show (0 : ℝ) ≤ p.d by exact Nat.cast_nonneg _]
  have hZ : ∀ X : EucConfig p.d N,
      S102Z (2 * p.d + 8) m (initialFunctional R N X) := by
    intro X
    unfold initialFunctional
    exact s102_Z_fluct hd1 hP0 (2 * p.d + 8) hr hNpos X
      (HRS.Whole.meanEmpirical (r26t3_Q R N)) hMoment (Real.sqrt N)
  have hpoint : ∀ X₀ : EucConfig p.d N,
      HRS.MS.ProClosureS111.physicalWindowRestriction
          (d := p.d) (m := m) (T := p.T) (H := H) ha le_rfl
          (r2InitPath (r26t3_coeff R) m H (r26t3_Q R N) X₀) =
        initialWindow R N a X₀ := by
    intro X₀
    have hVcont : ContinuousOn
        (fun s => r2Vprop (r26t3_coeff R) m s 0 (initialFunctional R N X₀))
        (Icc (0 : ℝ) H) :=
      s102_Vprop_continuousOn hP hD (hZ X₀) hlin
        (u := 0) ⟨le_rfl, hH.le⟩
    let θ : Icc (0 : ℝ) p.T → Icc (0 : ℝ) H := fun t =>
      ⟨a + (t : ℝ), ⟨add_nonneg ha t.2.1, by
        dsimp [H]
        linarith [t.2.2]⟩⟩
    have hθ : Continuous θ := by
      change Continuous (fun t : Icc (0 : ℝ) p.T =>
        (⟨a + (t : ℝ), _⟩ : Icc (0 : ℝ) H))
      fun_prop
    have hpath : Continuous (fun t : Icc (0 : ℝ) p.T =>
        r2Vprop (r26t3_coeff R) m (a + (t : ℝ)) 0
          (initialFunctional R N X₀)) := by
      change Continuous (fun t =>
        r2Vprop (r26t3_coeff R) m (θ t) 0 (initialFunctional R N X₀))
      exact (continuousOn_iff_continuous_restrict.mp hVcont).comp hθ
    have hWindow : initialWindow R N a X₀ =
        (⟨fun t : Icc (0 : ℝ) p.T =>
            r2Vprop (r26t3_coeff R) m (a + (t : ℝ)) 0
              (initialFunctional R N X₀), hpath⟩ : Window p) := by
      unfold initialWindow windowPathOf
      change (if h : Continuous (fun t : Icc (0 : ℝ) p.T =>
          r2Vprop (r26t3_coeff R) m (a + (t : ℝ)) 0
            (initialFunctional R N X₀)) then
          (⟨fun t : Icc (0 : ℝ) p.T =>
            r2Vprop (r26t3_coeff R) m (a + (t : ℝ)) 0
              (initialFunctional R N X₀), h⟩ : Window p)
        else 0) = _
      exact dif_pos hpath
    have hcompat : ∀ s : ℝ, s ∈ Icc (0 : ℝ) H →
        r2InitFun (r26t3_coeff R) m (r26t3_Q R N) X₀ s =
          r2Vprop (r26t3_coeff R) m s 0 (initialFunctional R N X₀) := by
      intro s hs
      exact fp81s21_physical_zero_initial_r2InitFun_eq_Vprop R hN H
        (c := fp81s21_uniform_orbit_coefficient p Co) hD hlin hZ hs X₀
    have hEq :
        (fun s : Icc (0 : ℝ) H =>
          r2InitFun (r26t3_coeff R) m (r26t3_Q R N) X₀ (s : ℝ)) =
        (fun s : Icc (0 : ℝ) H =>
          r2Vprop (r26t3_coeff R) m (s : ℝ) 0 (initialFunctional R N X₀)) := by
      funext s
      exact hcompat s s.property
    have hlongcont : Continuous (fun s : Icc (0 : ℝ) H =>
        r2InitFun (r26t3_coeff R) m (r26t3_Q R N) X₀ (s : ℝ)) := by
      rw [hEq]
      exact continuousOn_iff_continuous_restrict.mp hVcont
    have hlongShift : Continuous (fun s : Icc (0 : ℝ) H =>
        r2InitFun (r26t3_coeff R) m (r26t3_Q R N) X₀ (0 + (s : ℝ))) := by
      simpa only [zero_add] using hlongcont
    have hLongPath :
        r2InitPath (r26t3_coeff R) m H (r26t3_Q R N) X₀ =
          (⟨fun s : Icc (0 : ℝ) H =>
            r2InitFun (r26t3_coeff R) m (r26t3_Q R N) X₀ (0 + (s : ℝ)),
            hlongShift⟩ : OscPath p.d m H) := by
      exact fp81s21_physical_zero_initial_windowPath_eq
        (m := m) (T := H)
        (r2InitFun (r26t3_coeff R) m (r26t3_Q R N) X₀)
        (⟨fun s : Icc (0 : ℝ) H =>
          r2InitFun (r26t3_coeff R) m (r26t3_Q R N) X₀ (0 + (s : ℝ)),
          hlongShift⟩)
        (fun _ => rfl)
    change HRS.MS.ProClosureS111.physicalWindowRestriction
        (d := p.d) (m := m) (T := p.T) (H := H) ha
        (by dsimp [H]; exact le_rfl)
        (r2InitPath (r26t3_coeff R) m H (r26t3_Q R N) X₀) =
      initialWindow R N a X₀
    rw [hWindow]
    apply ContinuousMap.ext
    intro t
    change OscPath.at'
        (HRS.MS.ProClosureS111.physicalWindowRestriction
          (d := p.d) (m := m) (T := p.T) (H := H) ha
          (by dsimp [H]; exact le_rfl)
          (r2InitPath (r26t3_coeff R) m H (r26t3_Q R N) X₀)) t =
      OscPath.at'
        (⟨fun t : Icc (0 : ℝ) p.T =>
          r2Vprop (r26t3_coeff R) m (a + (t : ℝ)) 0
            (initialFunctional R N X₀), hpath⟩ : Window p) t
    rw [HRS.MS.ProClosureS111.physicalWindowRestriction_apply
      (d := p.d) (m := m) (T := p.T) (H := H) ha
      (by dsimp [H]; exact le_rfl)]
    rw [hLongPath]
    have hs : a + (t : ℝ) ∈ Icc (0 : ℝ) H := by
      constructor
      · linarith [ha, t.2.1]
      · dsimp [H]
        linarith [t.2.2]
    have hct := hcompat (a + (t : ℝ)) hs
    change r2InitFun (r26t3_coeff R) m (r26t3_Q R N) X₀
        (0 + (a + (t : ℝ))) =
      r2Vprop (r26t3_coeff R) m (a + (t : ℝ)) 0
        (initialFunctional R N X₀)
    simpa only [zero_add] using hct
  exact Filter.Eventually.of_forall hpoint

#print axioms HRS.Fp81.S21.fp81s21_physical_initialWindow_restriction_Q_zero
end HRS.Fp81.S21
end
